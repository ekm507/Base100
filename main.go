package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"hash/crc32"
	"io"
	"math/big"
	"os"
	"regexp"
	"strings"
	"unicode/utf8"
)

const (
	base      = 100
	checkMod  = 1_000_000 // 6 digits => 3 groups of 2 digits
	minLength = 4 + 2 + 6 // LLLL + at least one group + checksum(6)
	groupSize = 2         // two digits
	blockSize = 5         // 5 groups per block
)

// ---------------- Errors ----------------

type DecodeError struct {
	Stage string
	Msg   string
}

func (e *DecodeError) Error() string { return fmt.Sprintf("%s: %s", e.Stage, e.Msg) }
func decodeErr(stage, msg string) error {
	return &DecodeError{Stage: stage, Msg: msg}
}

// ---------------- Checksum (CRC32) ----------------

func crc6(payloadDigits string) (string, error) {
	for _, r := range payloadDigits {
		if r < '0' || r > '9' {
			return "", fmt.Errorf("payload contains non-digit: %q", r)
		}
	}
	sum := crc32.ChecksumIEEE([]byte(payloadDigits))
	return fmt.Sprintf("%06d", int(sum%checkMod)), nil
}

// ---------------- Core encode/decode ----------------

func encodeText(text string) (string, error) {
	b := []byte(text)
	L := len(b)
	if L > 9999 {
		return "", fmt.Errorf("input too long in bytes (%d), max 9999", L)
	}

	// bytes -> big.Int
	x := new(big.Int).SetBytes(b)

	// big.Int -> base100 digits
	digits := toBase100Digits(x)

	// DATA as 2-digit groups
	var data strings.Builder
	for _, d := range digits {
		data.WriteString(fmt.Sprintf("%02d", d))
	}

	header := fmt.Sprintf("%04d", L)
	payload := header + data.String()

	cs, err := crc6(payload)
	if err != nil {
		return "", err
	}
	return payload + cs, nil
}

func decodeCode(code string, verifyChecksum bool) (string, error) {
	d := stripNonDigits(code)

	if len(d) < minLength {
		return "", decodeErr("format", "code too short")
	}
	if !isAllDigits(d) {
		return "", decodeErr("format", "code contains non-digits after normalization (unexpected)")
	}

	header := d[:4]
	checksum := d[len(d)-6:]
	data := d[4 : len(d)-6]

	L, err := parseUintFixed(header)
	if err != nil {
		return "", decodeErr("length", "invalid 4-digit length header")
	}
	if L > 9999 {
		return "", decodeErr("length", "declared length exceeds 9999")
	}
	if len(data)%2 != 0 {
		return "", decodeErr("data", "DATA length must be even (two digits per group)")
	}

	payload := header + data
	if verifyChecksum {
		exp, err := crc6(payload)
		if err != nil {
			return "", decodeErr("checksum", "failed to compute checksum")
		}
		if checksum != exp {
			return "", decodeErr("checksum", fmt.Sprintf("checksum mismatch: expected %s got %s", exp, checksum))
		}
	}

	// parse DATA to base100 digits
	base100 := make([]int, 0, len(data)/2)
	for i := 0; i < len(data); i += 2 {
		pair := data[i : i+2]
		v, err := parseUintFixed(pair)
		if err != nil || v > 99 {
			return "", decodeErr("data", fmt.Sprintf("invalid base-100 group %q at position %d", pair, i/2))
		}
		base100 = append(base100, int(v))
	}

	// base100 -> big.Int -> bytes(length L)
	x := fromBase100Digits(base100)

	outBytes, err := toFixedLengthBytes(x, int(L))
	if err != nil {
		return "", decodeErr("bytes", err.Error())
	}
	if !utf8.Valid(outBytes) {
		return "", decodeErr("utf8", "decoded bytes are not valid UTF-8")
	}
	return string(outBytes), nil
}

func toBase100Digits(x *big.Int) []int {
	if x.Sign() == 0 {
		return []int{0}
	}
	n := new(big.Int).Set(x)
	div := big.NewInt(base)
	zero := big.NewInt(0)

	var rev []int
	for n.Cmp(zero) > 0 {
		q := new(big.Int)
		r := new(big.Int)
		q.QuoRem(n, div, r)
		rev = append(rev, int(r.Int64()))
		n = q
	}
	for i, j := 0, len(rev)-1; i < j; i, j = i+1, j-1 {
		rev[i], rev[j] = rev[j], rev[i]
	}
	return rev
}

func fromBase100Digits(digits []int) *big.Int {
	x := big.NewInt(0)
	b := big.NewInt(base)
	for _, d := range digits {
		x.Mul(x, b)
		x.Add(x, big.NewInt(int64(d)))
	}
	return x
}

func toFixedLengthBytes(x *big.Int, length int) ([]byte, error) {
	if length < 0 {
		return nil, errors.New("negative length")
	}
	b := x.Bytes()
	if len(b) > length {
		return nil, fmt.Errorf("decoded integer needs %d bytes, exceeds declared length %d", len(b), length)
	}
	if len(b) == length {
		return b, nil
	}
	out := make([]byte, length)
	copy(out[length-len(b):], b)
	return out, nil
}

// ---------------- REPAIR ----------------

type RepairResult struct {
	FixedCode string
	Text      string

	Edits int

	// positions are group indexes within PAYLOAD groups (2-digit groups).
	Positions []int
	From      []int
	To        []int
}

func tryRepair(digitsOnly string, maxEdits int, maxCandidates int) ([]RepairResult, error) {
	if maxEdits <= 0 {
		return nil, nil
	}
	if maxCandidates <= 0 {
		maxCandidates = 1
	}
	if len(digitsOnly) < minLength {
		return nil, decodeErr("repair", "code too short")
	}
	if !isAllDigits(digitsOnly) {
		return nil, decodeErr("repair", "normalized code must be digits-only")
	}

	payload := digitsOnly[:len(digitsOnly)-6]
	checksum := digitsOnly[len(digitsOnly)-6:]

	if len(payload)%2 != 0 {
		return nil, decodeErr("repair", "payload length is not even (cannot group into 2-digit chunks)")
	}

	// payload -> groups
	groups := make([]int, 0, len(payload)/2)
	for i := 0; i < len(payload); i += 2 {
		v, err := parseUintFixed(payload[i : i+2])
		if err != nil || v > 99 {
			return nil, decodeErr("repair", fmt.Sprintf("invalid payload group %q at index %d", payload[i:i+2], i/2))
		}
		groups = append(groups, int(v))
	}

	// already ok?
	exp, err := crc6(payload)
	if err != nil {
		return nil, decodeErr("repair", "failed to compute checksum")
	}
	if exp == checksum {
		return nil, nil
	}

	results := make([]RepairResult, 0, maxCandidates)

	var dfs func(startPos int, editsLeft int, positions, fromVals, toVals []int)

	dfs = func(startPos int, editsLeft int, positions, fromVals, toVals []int) {
		if len(results) >= maxCandidates {
			return
		}

		// test at any depth >=1 edit
		if len(positions) > 0 {
			payload2 := groupsToPayload(groups)
			cs2, _ := crc6(payload2)
			if cs2 == checksum {
				fixedCode := payload2 + checksum

				// verify decode + re-encode exact match
				text, derr := decodeCode(fixedCode, true)
				if derr == nil {
					reenc, eerr := encodeText(text)
					if eerr == nil && stripNonDigits(reenc) == fixedCode {
						results = append(results, RepairResult{
							FixedCode: fixedCode,
							Text:      text,
							Edits:     len(positions),
							Positions: append([]int(nil), positions...),
							From:      append([]int(nil), fromVals...),
							To:        append([]int(nil), toVals...),
						})
						if len(results) >= maxCandidates {
							return
						}
					}
				}
			}
		}

		if editsLeft == 0 {
			return
		}

		for pos := startPos; pos < len(groups); pos++ {
			orig := groups[pos]
			for newVal := 0; newVal < 100; newVal++ {
				if newVal == orig {
					continue
				}
				groups[pos] = newVal
				dfs(pos+1, editsLeft-1,
					append(positions, pos),
					append(fromVals, orig),
					append(toVals, newVal),
				)
				groups[pos] = orig
				if len(results) >= maxCandidates {
					return
				}
			}
		}
	}

	for e := 1; e <= maxEdits && len(results) < maxCandidates; e++ {
		dfs(0, e, nil, nil, nil)
	}

	return results, nil
}

func groupsToPayload(groups []int) string {
	var b strings.Builder
	b.Grow(len(groups) * 2)
	for _, g := range groups {
		b.WriteString(fmt.Sprintf("%02d", g))
	}
	return b.String()
}

// ---------------- Pretty printing (block-numbered) ----------------

func prettyPrintBlocks(out io.Writer, fullCode string, highlightPayloadPositions map[int]bool) {
	d := stripNonDigits(fullCode)
	if len(d) < 10 {
		fmt.Fprintln(out, d)
		return
	}

	groups := splitIntoGroups(d, 2)

	payloadGroupCount := len(groups) - 3 // last 3 groups are checksum
	if payloadGroupCount < 2 {
		fmt.Fprintln(out, d)
		return
	}

	// ANSI styles
	reset := "\x1b[0m"
	bold := "\x1b[1m"
	cyan := "\x1b[36m"   // LEN
	yellow := "\x1b[33m" // DATA
	green := "\x1b[32m"  // CRC
	red := "\x1b[31m"    // repaired groups

	fmt.Fprintf(out, "%sBLOCKS%s: each line = %d groups (each group = 2 digits)\n\n", bold, reset, blockSize)

	for bi := 0; bi < len(groups); bi += blockSize {
		blockNum := bi/blockSize + 1
		end := bi + blockSize
		if end > len(groups) {
			end = len(groups)
		}

		var parts []string
		for gi := bi; gi < end; gi++ {
			g := groups[gi]

			var color string
			switch {
			case gi == 0 || gi == 1:
				color = cyan // LEN
			case gi >= payloadGroupCount:
				color = green // CRC
			default:
				color = yellow // DATA
			}

			// highlight repaired payload group indices
			if gi < payloadGroupCount && highlightPayloadPositions != nil && highlightPayloadPositions[gi] {
				color = red
			}

			parts = append(parts, fmt.Sprintf("%s%s%s", color, g, reset))
		}

		fmt.Fprintf(out, "%s%02d%s: %s\n", bold, blockNum, reset, strings.Join(parts, " "))
	}

	fmt.Fprintf(out, "\n%sFULL%s %s\n", bold, reset, d)
}

func splitIntoGroups(digits string, size int) []string {
	var out []string
	for i := 0; i < len(digits); i += size {
		end := i + size
		if end > len(digits) {
			end = len(digits)
		}
		out = append(out, digits[i:end])
	}
	return out
}

func formatForPhone(digitsOnly string) string {
	d := stripNonDigits(digitsOnly)
	groups := splitIntoGroups(d, 2)

	var blocks []string
	for i := 0; i < len(groups); i += blockSize {
		end := i + blockSize
		if end > len(groups) {
			end = len(groups)
		}
		blocks = append(blocks, strings.Join(groups[i:end], " "))
	}
	return strings.Join(blocks, " - ")
}

// ---------------- CLI helpers ----------------

var nonDigitsRe = regexp.MustCompile(`\D+`)

func stripNonDigits(s string) string { return nonDigitsRe.ReplaceAllString(s, "") }

func isAllDigits(s string) bool {
	for _, r := range s {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}

func parseUintFixed(s string) (uint64, error) {
	var n uint64
	for _, r := range s {
		if r < '0' || r > '9' {
			return 0, fmt.Errorf("non-digit")
		}
		n = n*10 + uint64(r-'0')
	}
	return n, nil
}

func readAllStdin() (string, error) {
	info, err := os.Stdin.Stat()
	if err != nil {
		return "", err
	}
	if (info.Mode() & os.ModeCharDevice) != 0 {
		return "", nil
	}
	var buf bytes.Buffer
	_, err = io.Copy(&buf, os.Stdin)
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(buf.String()), nil
}

func checksumMismatch(err error) bool {
	var de *DecodeError
	if errors.As(err, &de) {
		return de.Stage == "checksum" && strings.Contains(de.Msg, "checksum mismatch")
	}
	return false
}

// ---------------- Main ----------------

func usage() {
	fmt.Fprintf(os.Stderr, `Usage:
  urlcode encode [--text "..."] [--pretty]
  urlcode decode [--code "..."] [--pretty] [--no-check] [--repair N] [--max-candidates K]

Stdin:
  echo "https://example.com/..." | urlcode encode --pretty
  echo "0105..." | urlcode decode --pretty

Options:
  --pretty            Print numbered blocks (5 groups per line) with colors.
  --no-check          (decode) Skip checksum verification (not recommended).
  --repair N          (decode) If checksum mismatch, brute-force fix by changing 1..N payload groups.
  --max-candidates K  (decode) Max repair candidates (default 3).
`)
}

func main() {
	if len(os.Args) < 2 {
		usage()
		os.Exit(2)
	}
	switch os.Args[1] {
	case "encode":
		runEncode(os.Args[2:])
	case "decode":
		runDecode(os.Args[2:])
	default:
		usage()
		os.Exit(2)
	}
}

func runEncode(args []string) {
	fs := flag.NewFlagSet("encode", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)

	text := fs.String("text", "", "Text/URL to encode (or read from stdin)")
	pretty := fs.Bool("pretty", false, "Pretty colored output with numbered blocks")

	if err := fs.Parse(args); err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(2)
	}

	in := strings.TrimSpace(*text)
	if in == "" {
		stdin, err := readAllStdin()
		if err != nil {
			fmt.Fprintln(os.Stderr, "error reading stdin:", err)
			os.Exit(1)
		}
		in = stdin
	}
	if in == "" {
		fmt.Fprintln(os.Stderr, "error: no input provided (use --text or stdin)")
		os.Exit(2)
	}

	code, err := encodeText(in)
	if err != nil {
		fmt.Fprintln(os.Stderr, "encode error:", err)
		os.Exit(1)
	}

	if *pretty {
		prettyPrintBlocks(os.Stdout, code, nil)
	} else {
		fmt.Println(formatForPhone(code))
	}
}

func runDecode(args []string) {
	fs := flag.NewFlagSet("decode", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)

	code := fs.String("code", "", "Code to decode (or read from stdin)")
	pretty := fs.Bool("pretty", false, "Pretty output")
	noCheck := fs.Bool("no-check", false, "Skip checksum verification")
	repair := fs.Int("repair", 0, "If checksum mismatch, try brute-force repair by changing 1..N payload groups")
	maxCand := fs.Int("max-candidates", 3, "Max number of repaired candidates to output")

	if err := fs.Parse(args); err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(2)
	}

	in := strings.TrimSpace(*code)
	if in == "" {
		stdin, err := readAllStdin()
		if err != nil {
			fmt.Fprintln(os.Stderr, "error reading stdin:", err)
			os.Exit(1)
		}
		in = stdin
	}
	if in == "" {
		fmt.Fprintln(os.Stderr, "error: no input provided (use --code or stdin)")
		os.Exit(2)
	}

	normalized := stripNonDigits(in)

	text, derr := decodeCode(normalized, !*noCheck)
	if derr == nil {
		if *pretty {
			fmt.Println("\x1b[1mDECODED\x1b[0m", text)
			fmt.Println()
			prettyPrintBlocks(os.Stdout, normalized, nil)
		} else {
			fmt.Println(text)
		}
		return
	}

	// Repair path (only if checksum mismatch)
	if *repair > 0 && checksumMismatch(derr) {
		results, rerr := tryRepair(normalized, *repair, *maxCand)
		if rerr != nil {
			fmt.Fprintln(os.Stderr, "decode error:", derr)
			fmt.Fprintln(os.Stderr, "repair error:", rerr)
			os.Exit(1)
		}
		if len(results) == 0 {
			fmt.Fprintln(os.Stderr, "decode error:", derr)
			fmt.Fprintf(os.Stderr, "repair: no valid fix found with up to %d edits\n", *repair)
			os.Exit(1)
		}

		if len(results) > 1 {
			fmt.Fprintln(os.Stderr, "decode error:", derr)
			fmt.Fprintf(os.Stderr, "repair: found %d possible fixes (ambiguous). Candidates:\n\n", len(results))
			for i, r := range results {
				fmt.Fprintf(os.Stderr, "[%d] edits=%d\n", i+1, r.Edits)
				printEditLocations(os.Stderr, r.Positions, r.From, r.To)
				if *pretty {
					hl := make(map[int]bool)
					for _, p := range r.Positions {
						hl[p] = true
					}
					prettyPrintBlocks(os.Stderr, r.FixedCode, hl)
				} else {
					fmt.Fprintln(os.Stderr, formatForPhone(r.FixedCode))
				}
				fmt.Fprintln(os.Stderr)
			}
			os.Exit(1)
		}

		// single fix
		r := results[0]
		if *pretty {
			fmt.Println("\x1b[1mREPAIRED\x1b[0m")
			printEditLocations(os.Stdout, r.Positions, r.From, r.To)
			fmt.Println()
			hl := make(map[int]bool)
			for _, p := range r.Positions {
				hl[p] = true
			}
			prettyPrintBlocks(os.Stdout, r.FixedCode, hl)
			fmt.Println("\n\x1b[1mDECODED\x1b[0m", r.Text)
		} else {
			fmt.Println(r.Text)
		}
		return
	}

	fmt.Fprintln(os.Stderr, "decode error:", derr)
	os.Exit(1)
}

func printEditLocations(out io.Writer, positions, fromVals, toVals []int) {
	fmt.Fprintln(out, "\x1b[1mEDITS\x1b[0m")
	for i := range positions {
		p := positions[i]
		blockNum := p/blockSize + 1
		inBlock := p%blockSize + 1
		fmt.Fprintf(out, " - payload-group=%d  block=%d  in-block=%d  %02d -> %02d\n",
			p, blockNum, inBlock, fromVals[i], toVals[i])
	}
}

