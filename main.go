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
	"sort"
	"strings"
	"unicode/utf8"
)

const (
	base = 100

	versionCurrent = 1

	// Header layout: 8 groups (16 digits)
	headerGroups = 8
	headerDigits = headerGroups * 2

	// Fixed final checksum length: 3 groups = 6 digits
	finalCheckGroups = 3

	// For safety limits (header encodes these as 00..99, but we accept some bounds)
	maxLenBytes = 9999
	maxGroups   = 9999
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

// ---------------- Digits helpers ----------------

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

func parseUintFixedDigits(s string) (uint64, error) {
	var n uint64
	for _, r := range s {
		if r < '0' || r > '9' {
			return 0, fmt.Errorf("non-digit")
		}
		n = n*10 + uint64(r-'0')
	}
	return n, nil
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

func groupsToDigits(groups []int) string {
	var b strings.Builder
	b.Grow(len(groups) * 2)
	for _, g := range groups {
		b.WriteString(fmt.Sprintf("%02d", g))
	}
	return b.String()
}

// ---------------- Header ----------------

type Header struct {
	Version int
	BD      int // block data groups
	BC      int // block checksum groups
	Flags   int // bit0: final checksum enabled
	L       int // byte length
	G       int // number of DATA base100 groups
}

func (h Header) finalEnabled() bool { return (h.Flags & 1) == 1 }

func (h Header) validate() error {
	if h.Version != versionCurrent {
		return fmt.Errorf("unsupported version: %d", h.Version)
	}
	if h.BD <= 0 || h.BD > 99 {
		return fmt.Errorf("invalid BD (block-data-groups): %d", h.BD)
	}
	if h.BC <= 0 || h.BC > 99 {
		return fmt.Errorf("invalid BC (block-check-groups): %d", h.BC)
	}
	if h.L < 0 || h.L > maxLenBytes {
		return fmt.Errorf("invalid L (byte length): %d", h.L)
	}
	if h.G < 0 || h.G > maxGroups {
		return fmt.Errorf("invalid G (data group count): %d", h.G)
	}
	return nil
}

func encodeHeaderDigits(h Header) (string, error) {
	if err := h.validate(); err != nil {
		return "", err
	}
	// L and G as base100 hi/lo
	llHi, llLo := h.L/100, h.L%100
	ggHi, ggLo := h.G/100, h.G%100

	// groups:
	// VV BD BC FF LL ll GG gg
	g := []int{
		h.Version,
		h.BD,
		h.BC,
		h.Flags,
		llHi,
		llLo,
		ggHi,
		ggLo,
	}
	return groupsToDigits(g), nil
}

func parseHeaderDigits(digitsOnly string) (Header, error) {
	if len(digitsOnly) < headerDigits {
		return Header{}, decodeErr("header", "code too short for header")
	}
	if !isAllDigits(digitsOnly[:headerDigits]) {
		return Header{}, decodeErr("header", "header contains non-digits")
	}

	raw := digitsOnly[:headerDigits]
	gr := splitIntoGroups(raw, 2)
	if len(gr) != headerGroups {
		return Header{}, decodeErr("header", "failed to split header groups")
	}

	val := make([]int, headerGroups)
	for i := 0; i < headerGroups; i++ {
		u, err := parseUintFixedDigits(gr[i])
		if err != nil || u > 99 {
			return Header{}, decodeErr("header", fmt.Sprintf("invalid header group %q at index %d", gr[i], i))
		}
		val[i] = int(u)
	}

	h := Header{
		Version: val[0],
		BD:      val[1],
		BC:      val[2],
		Flags:   val[3],
		L:       val[4]*100 + val[5],
		G:       val[6]*100 + val[7],
	}
	if err := h.validate(); err != nil {
		return Header{}, decodeErr("header", err.Error())
	}
	return h, nil
}

// ---------------- Checksums ----------------

func modForGroups(groups int) int {
	m := 1
	for i := 0; i < groups; i++ {
		m *= 100
	}
	return m
}

// CRC32(payloadDigits) mod 100^k, formatted as 2*k digits (zero padded)
func checksumK(payloadDigits string, kGroups int) (string, error) {
	for _, r := range payloadDigits {
		if r < '0' || r > '9' {
			return "", fmt.Errorf("payload contains non-digit: %q", r)
		}
	}
	mod := modForGroups(kGroups)
	sum := crc32.ChecksumIEEE([]byte(payloadDigits))
	val := int(sum % uint32(mod))
	return fmt.Sprintf("%0*d", 2*kGroups, val), nil
}

func blockIndexDigits(blockIndex int) string {
	// blockIndex up to 9999 -> 2 base100 groups (4 digits)
	hi := blockIndex / 100
	lo := blockIndex % 100
	return fmt.Sprintf("%02d%02d", hi, lo)
}

// Block checksum covers: header + blockIndex(2 groups) + blockDataDigits
func blockChecksumDigits(headerDigits string, blockIndex int, blockDataDigits string, bcGroups int) (string, error) {
	payload := headerDigits + blockIndexDigits(blockIndex) + blockDataDigits
	return checksumK(payload, bcGroups)
}

// Final checksum covers: header + all blocks (data+blockchk), excluding itself
func finalChecksumDigits(allExceptFinal string) (string, error) {
	return checksumK(allExceptFinal, finalCheckGroups)
}

// ---------------- Base100 conversion ----------------

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

// ---------------- Encoding ----------------

type EncodeSettings struct {
	BD    int
	BC    int
	Final bool
}

func encodeText(text string, es EncodeSettings) (string, error) {
	if es.BD <= 0 || es.BD > 99 {
		return "", fmt.Errorf("block-data-groups must be 1..99")
	}
	if es.BC <= 0 || es.BC > 99 {
		return "", fmt.Errorf("block-check-groups must be 1..99")
	}

	b := []byte(text)
	L := len(b)
	if L > maxLenBytes {
		return "", fmt.Errorf("input too long in bytes (%d), max %d", L, maxLenBytes)
	}

	x := new(big.Int).SetBytes(b)
	dataGroups := toBase100Digits(x)
	G := len(dataGroups)
	if G > maxGroups {
		return "", fmt.Errorf("too many DATA groups (%d), max %d", G, maxGroups)
	}

	flags := 0
	if es.Final {
		flags |= 1
	}

	h := Header{
		Version: versionCurrent,
		BD:      es.BD,
		BC:      es.BC,
		Flags:   flags,
		L:       L,
		G:       G,
	}

	headerDigits, err := encodeHeaderDigits(h)
	if err != nil {
		return "", err
	}

	var out strings.Builder
	out.WriteString(headerDigits)

	// blocks
	blockCount := 0
	for i := 0; i < G; i += es.BD {
		blockCount++
		end := i + es.BD
		if end > G {
			end = G
		}
		blockDataDigits := groupsToDigits(dataGroups[i:end])

		bchk, err := blockChecksumDigits(headerDigits, blockCount, blockDataDigits, es.BC)
		if err != nil {
			return "", err
		}

		out.WriteString(blockDataDigits)
		out.WriteString(bchk)
	}

	// final checksum
	if es.Final {
		fc, err := finalChecksumDigits(out.String())
		if err != nil {
			return "", err
		}
		out.WriteString(fc)
	}

	return out.String(), nil
}

// ---------------- Decoding & Report ----------------

type BlockStatus struct {
	BlockIndex int
	Expected   string
	Got        string
}

type DecodeReport struct {
	Header       Header
	BadBlocks    []BlockStatus
	FinalOK      bool
	FinalExpected string
	FinalGot      string
}

func decodeCodeWithReport(code string, verify bool) (string, DecodeReport, error) {
	var rep DecodeReport

	d := stripNonDigits(code)
	if len(d) < headerDigits {
		return "", rep, decodeErr("format", "code too short")
	}
	if !isAllDigits(d) {
		return "", rep, decodeErr("format", "code has non-digits after normalization (unexpected)")
	}

	h, err := parseHeaderDigits(d)
	if err != nil {
		return "", rep, err
	}
	rep.Header = h

	headerDigitsStr := d[:headerDigits]
	body := d[headerDigits:]

	finalDigits := 0
	if h.finalEnabled() {
		finalDigits = finalCheckGroups * 2
		if len(body) < finalDigits {
			return "", rep, decodeErr("format", "code too short for final checksum")
		}
		rep.FinalGot = body[len(body)-finalDigits:]
		body = body[:len(body)-finalDigits]
	} else {
		rep.FinalOK = true
	}

	// Parse blocks
	totalBlocks := (h.G + h.BD - 1) / h.BD
	perBlockCheckDigits := h.BC * 2

	cursor := 0
	dataGroups := make([]int, 0, h.G)

	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := h.G - (blk-1)*h.BD
		thisDataGroups := h.BD
		if remaining < thisDataGroups {
			thisDataGroups = remaining
		}
		thisDataDigits := thisDataGroups * 2

		need := thisDataDigits + perBlockCheckDigits
		if cursor+need > len(body) {
			return "", rep, decodeErr("format", fmt.Sprintf("truncated at block %d", blk))
		}

		blockDataDigits := body[cursor : cursor+thisDataDigits]
		blockChkGot := body[cursor+thisDataDigits : cursor+need]
		cursor += need

		exp, err := blockChecksumDigits(headerDigitsStr, blk, blockDataDigits, h.BC)
		if err != nil {
			return "", rep, decodeErr("checksum", "failed to compute block checksum")
		}
		if verify && blockChkGot != exp {
			rep.BadBlocks = append(rep.BadBlocks, BlockStatus{
				BlockIndex: blk,
				Expected:   exp,
				Got:        blockChkGot,
			})
		}

		// parse block data groups
		for i := 0; i < len(blockDataDigits); i += 2 {
			pair := blockDataDigits[i : i+2]
			u, err := parseUintFixedDigits(pair)
			if err != nil || u > 99 {
				return "", rep, decodeErr("data", fmt.Sprintf("invalid group %q in block %d", pair, blk))
			}
			dataGroups = append(dataGroups, int(u))
		}
	}

	if cursor != len(body) {
		return "", rep, decodeErr("format", "extra trailing digits in body (header/settings mismatch?)")
	}

	// final checksum verify
	if verify && h.finalEnabled() {
		fullExceptFinal := headerDigitsStr + body
		exp, err := finalChecksumDigits(fullExceptFinal)
		if err != nil {
			return "", rep, decodeErr("checksum", "failed to compute final checksum")
		}
		rep.FinalExpected = exp
		rep.FinalOK = (rep.FinalGot == exp)
		if !rep.FinalOK {
			// keep going; caller decides (repair)
		}
	}

	if verify && len(rep.BadBlocks) > 0 {
		return "", rep, decodeErr("checksum", fmt.Sprintf("%d block checksum mismatches", len(rep.BadBlocks)))
	}
	if verify && h.finalEnabled() && !rep.FinalOK {
		return "", rep, decodeErr("checksum", "final checksum mismatch")
	}

	// decode base100 -> bytes(L)
	x := fromBase100Digits(dataGroups)
	outBytes, err := toFixedLengthBytes(x, h.L)
	if err != nil {
		return "", rep, decodeErr("bytes", err.Error())
	}
	if !utf8.Valid(outBytes) {
		return "", rep, decodeErr("utf8", "decoded bytes are not valid UTF-8")
	}
	return string(outBytes), rep, nil
}

// ---------------- Pretty printing ----------------

func prettyPrint(out io.Writer, digitsOnly string, highlight map[int]map[int]bool) {
	// highlight[block][pos] => true
	// block: 1..N ; block 0 used for FINAL (pos 1..finalCheckGroups)

	d := stripNonDigits(digitsOnly)
	if len(d) < headerDigits {
		fmt.Fprintln(out, d)
		return
	}

	h, err := parseHeaderDigits(d)
	if err != nil {
		fmt.Fprintln(out, d)
		return
	}

	// ANSI
	reset := "\x1b[0m"
	bold := "\x1b[1m"
	cyan := "\x1b[36m"
	yellow := "\x1b[33m"
	green := "\x1b[32m"
	red := "\x1b[31m"

	headerDigitsStr := d[:headerDigits]
	headerGroupsStr := splitIntoGroups(headerDigitsStr, 2)

	fmt.Fprintf(out, "%sHEADER%s  %s\n", bold, reset, strings.Join(headerGroupsStr, " "))
	fmt.Fprintf(out, "%sparams%s  ver=%d  BD=%d  BC=%d  final=%v  L=%d  G=%d\n\n",
		bold, reset, h.Version, h.BD, h.BC, h.finalEnabled(), h.L, h.G)

	body := d[headerDigits:]

	// strip final (print it separately)
	finalPart := ""
	if h.finalEnabled() {
		fd := finalCheckGroups * 2
		if len(body) >= fd {
			finalPart = body[len(body)-fd:]
			body = body[:len(body)-fd]
		}
	}

	totalBlocks := (h.G + h.BD - 1) / h.BD
	perBlockCheckDigits := h.BC * 2

	cursor := 0
	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := h.G - (blk-1)*h.BD
		thisDataGroups := h.BD
		if remaining < thisDataGroups {
			thisDataGroups = remaining
		}
		thisDataDigits := thisDataGroups * 2

		blockData := body[cursor : cursor+thisDataDigits]
		blockChk := body[cursor+thisDataDigits : cursor+thisDataDigits+perBlockCheckDigits]
		cursor += thisDataDigits + perBlockCheckDigits

		dataGroups := splitIntoGroups(blockData, 2)
		chkGroups := splitIntoGroups(blockChk, 2)

		var parts []string
		for i, g := range dataGroups {
			color := yellow
			if highlight != nil && highlight[blk] != nil && highlight[blk][i+1] {
				color = red
			}
			parts = append(parts, fmt.Sprintf("%s%s%s", color, g, reset))
		}
		parts = append(parts, fmt.Sprintf("%s|%s", bold, reset))
		for i, g := range chkGroups {
			pos := thisDataGroups + (i + 1)
			color := green
			if highlight != nil && highlight[blk] != nil && highlight[blk][pos] {
				color = red
			}
			parts = append(parts, fmt.Sprintf("%s%s%s", color, g, reset))
		}

		fmt.Fprintf(out, "%s%02d%s: %s\n", bold, blk, reset, strings.Join(parts, " "))
	}

	if h.finalEnabled() && finalPart != "" {
		fg := splitIntoGroups(finalPart, 2)
		for i := range fg {
			if highlight != nil && highlight[0] != nil && highlight[0][i+1] {
				fg[i] = red + fg[i] + reset
			} else {
				fg[i] = cyan + fg[i] + reset
			}
		}
		fmt.Fprintf(out, "\n%sFINAL%s: %s\n", bold, reset, strings.Join(fg, " "))
	}

	fmt.Fprintf(out, "\n%sFULL%s %s\n", bold, reset, d)
}

// ---------------- Repair ----------------

type Edit struct {
	Block int // 1..N, 0 = FINAL
	Pos   int // position inside that segment (data then chk for blocks; 1..finalCheckGroups for FINAL)
	From  int
	To    int
}

type RepairResult struct {
	FixedDigits string
	Text        string
	Edits       []Edit
}

func tryRepair(code string, maxEdits int, maxCandidates int) ([]RepairResult, error) {
	if maxEdits <= 0 {
		return nil, nil
	}
	if maxCandidates <= 0 {
		maxCandidates = 1
	}

	d := stripNonDigits(code)
	if len(d) < headerDigits {
		return nil, decodeErr("repair", "code too short")
	}

	// First get report (verify=true) to know bad blocks / final mismatch
	_, rep, derr := decodeCodeWithReport(d, true)
	if derr == nil {
		return nil, nil
	}
	h := rep.Header
	headerDigitsStr := d[:headerDigits]

	// Build groups array for whole code (2-digit groups)
	if len(d)%2 != 0 {
		return nil, decodeErr("repair", "digits length not even")
	}
	allGroupsStr := splitIntoGroups(d, 2)
	allGroups := make([]int, len(allGroupsStr))
	for i, g := range allGroupsStr {
		u, err := parseUintFixedDigits(g)
		if err != nil || u > 99 {
			return nil, decodeErr("repair", fmt.Sprintf("invalid group %q at index %d", g, i))
		}
		allGroups[i] = int(u)
	}

	// Compute absolute group ranges
	// layout in groups:
	// headerGroups +
	// blocks (each: dataCount + BC) +
	// optional final (finalCheckGroups)
	totalBlocks := (h.G + h.BD - 1) / h.BD

	type blockRange struct {
		blk        int
		startAbs   int // inclusive
		dataCount  int
		checkCount int
		endAbs     int // exclusive
	}
	var ranges []blockRange
	cursor := headerGroups
	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := h.G - (blk-1)*h.BD
		dataCount := h.BD
		if remaining < dataCount {
			dataCount = remaining
		}
		start := cursor
		end := cursor + dataCount + h.BC
		ranges = append(ranges, blockRange{
			blk:        blk,
			startAbs:   start,
			dataCount:  dataCount,
			checkCount: h.BC,
			endAbs:     end,
		})
		cursor = end
	}
	finalStart := cursor
	finalEnd := cursor
	if h.finalEnabled() {
		finalEnd = finalStart + finalCheckGroups
		if finalEnd > len(allGroups) {
			return nil, decodeErr("repair", "missing final checksum groups")
		}
	}

	// Determine targets:
	badBlocks := make([]int, 0, len(rep.BadBlocks))
	for _, b := range rep.BadBlocks {
		badBlocks = append(badBlocks, b.BlockIndex)
	}
	sort.Ints(badBlocks)

	inSet := func(x int, set []int) bool {
		for _, v := range set {
			if v == x {
				return true
			}
		}
		return false
	}

	targetAbs := []int{}
	targetMeta := map[int]Edit{} // abs->(block,pos)
	absToLoc := func(abs int) (blk int, pos int, ok bool) {
		if h.finalEnabled() && abs >= finalStart && abs < finalEnd {
			return 0, abs - finalStart + 1, true
		}
		for _, br := range ranges {
			if abs >= br.startAbs && abs < br.endAbs {
				return br.blk, abs - br.startAbs + 1, true
			}
		}
		return 0, 0, false
	}

	if len(badBlocks) > 0 {
		for _, br := range ranges {
			if !inSet(br.blk, badBlocks) {
				continue
			}
			for abs := br.startAbs; abs < br.endAbs; abs++ {
				targetAbs = append(targetAbs, abs)
				blk, pos, _ := absToLoc(abs)
				targetMeta[abs] = Edit{Block: blk, Pos: pos}
			}
		}
	} else if h.finalEnabled() && !rep.FinalOK {
		for abs := finalStart; abs < finalEnd; abs++ {
			targetAbs = append(targetAbs, abs)
			blk, pos, _ := absToLoc(abs)
			targetMeta[abs] = Edit{Block: blk, Pos: pos}
		}
	} else {
		return nil, decodeErr("repair", "no identifiable bad blocks or final mismatch")
	}

	results := make([]RepairResult, 0, maxCandidates)

	// DFS edits
	var dfs func(startIdx int, editsLeft int, chosenAbs []int, fromVals []int, toVals []int)

	testCandidate := func(chosenAbs []int, fromVals []int, toVals []int) {
		// Build candidate digits
		var b strings.Builder
		b.Grow(len(allGroups) * 2)
		for _, g := range allGroups {
			b.WriteString(fmt.Sprintf("%02d", g))
		}
		candDigits := b.String()

		// Verify full decode using embedded settings
		text, _, err := decodeCodeWithReport(candDigits, true)
		if err != nil {
			return
		}

		// Re-encode with the SAME embedded settings (from header)
		es := EncodeSettings{BD: h.BD, BC: h.BC, Final: h.finalEnabled()}
		reenc, eerr := encodeText(text, es)
		if eerr != nil {
			return
		}
		if stripNonDigits(reenc) != candDigits {
			return
		}

		edits := make([]Edit, 0, len(chosenAbs))
		for i, abs := range chosenAbs {
			meta := targetMeta[abs]
			edits = append(edits, Edit{
				Block: meta.Block,
				Pos:   meta.Pos,
				From:  fromVals[i],
				To:    toVals[i],
			})
		}

		results = append(results, RepairResult{
			FixedDigits: candDigits,
			Text:        text,
			Edits:       edits,
		})
	}

	dfs = func(startIdx int, editsLeft int, chosenAbs []int, fromVals []int, toVals []int) {
		if len(results) >= maxCandidates {
			return
		}

		if len(chosenAbs) > 0 {
			testCandidate(chosenAbs, fromVals, toVals)
			if len(results) >= maxCandidates {
				return
			}
		}

		if editsLeft == 0 {
			return
		}

		for i := startIdx; i < len(targetAbs); i++ {
			abs := targetAbs[i]
			orig := allGroups[abs]
			for nv := 0; nv < 100; nv++ {
				if nv == orig {
					continue
				}
				allGroups[abs] = nv
				dfs(i+1, editsLeft-1,
					append(chosenAbs, abs),
					append(fromVals, orig),
					append(toVals, nv),
				)
				allGroups[abs] = orig
				if len(results) >= maxCandidates {
					return
				}
			}
		}
	}

	for e := 1; e <= maxEdits && len(results) < maxCandidates; e++ {
		dfs(0, e, nil, nil, nil)
	}

	// If nothing found and the only mismatch was FINAL, print a hintable error:
	_ = headerDigitsStr // keep for future extensions
	return results, nil
}

func editsToHighlight(edits []Edit) map[int]map[int]bool {
	hl := map[int]map[int]bool{}
	for _, e := range edits {
		if hl[e.Block] == nil {
			hl[e.Block] = map[int]bool{}
		}
		hl[e.Block][e.Pos] = true
	}
	return hl
}

func printEdits(out io.Writer, edits []Edit) {
	fmt.Fprintln(out, "\x1b[1mEDITS\x1b[0m")
	for _, e := range edits {
		if e.Block == 0 {
			fmt.Fprintf(out, " - FINAL pos=%d  %02d -> %02d\n", e.Pos, e.From, e.To)
		} else {
			fmt.Fprintf(out, " - block=%d pos=%d  %02d -> %02d\n", e.Block, e.Pos, e.From, e.To)
		}
	}
}

// ---------------- CLI IO ----------------

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

// ---------------- CLI ----------------

func usage() {
	fmt.Fprintf(os.Stderr, `Usage:
  urlcode encode [--text "..."] [--pretty]
               --block-data-groups N --block-check-groups K
               [--final-check | --no-final-check]

  urlcode decode [--code "..."] [--pretty] [--no-check]
               [--repair E] [--max-candidates C]

Notes:
- Decode reads BD/BC/final from the HEADER; you do NOT pass them on decode.
- Header is 8 groups (16 digits): VV BD BC FF LL ll GG gg
- FINAL checksum (if enabled) is always 3 groups (6 digits).
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
	prettyFlag := fs.Bool("pretty", false, "Pretty block-numbered output")

	bd := fs.Int("block-data-groups", 5, "How many 2-digit DATA groups per block (1..99)")
	bc := fs.Int("block-check-groups", 2, "How many 2-digit checksum groups per block (1..99)")

	finalOn := fs.Bool("final-check", true, "Enable final checksum")
	finalOff := fs.Bool("no-final-check", false, "Disable final checksum (overrides --final-check)")

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

	final := *finalOn
	if *finalOff {
		final = false
	}

	code, err := encodeText(in, EncodeSettings{BD: *bd, BC: *bc, Final: final})
	if err != nil {
		fmt.Fprintln(os.Stderr, "encode error:", err)
		os.Exit(1)
	}

	if *prettyFlag {
		prettyPrint(os.Stdout, code, nil)
	} else {
		// compact: just print digits-only (user can add separators if desired)
		fmt.Println(code)
	}
}

func runDecode(args []string) {
	fs := flag.NewFlagSet("decode", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)

	code := fs.String("code", "", "Code to decode (or read from stdin)")
	prettyFlag := fs.Bool("pretty", false, "Pretty output")
	noCheck := fs.Bool("no-check", false, "Skip checksum verification (not recommended)")

	repair := fs.Int("repair", 0, "If checksum fails, brute-force repair with 1..E edits (within bad blocks)")
	maxCand := fs.Int("max-candidates", 3, "Max repair candidates to output")

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

	text, rep, err := decodeCodeWithReport(normalized, !*noCheck)
	if err == nil {
		if *prettyFlag {
			fmt.Println("\x1b[1mDECODED\x1b[0m", text)
			fmt.Println()
			prettyPrint(os.Stdout, normalized, nil)
		} else {
			fmt.Println(text)
		}
		return
	}

	// If verify disabled, just report
	if *noCheck {
		fmt.Fprintln(os.Stderr, "decode error:", err)
		os.Exit(1)
	}

	// Report details
	fmt.Fprintln(os.Stderr, "decode error:", err)
	if len(rep.BadBlocks) > 0 {
		fmt.Fprintf(os.Stderr, "bad blocks (%d):\n", len(rep.BadBlocks))
		for _, b := range rep.BadBlocks {
			fmt.Fprintf(os.Stderr, " - block %d: expected %s got %s\n", b.BlockIndex, b.Expected, b.Got)
		}
	}
	if rep.Header.finalEnabled() && !rep.FinalOK {
		fmt.Fprintf(os.Stderr, "final checksum mismatch: expected %s got %s\n", rep.FinalExpected, rep.FinalGot)
	}

	// Repair
	if *repair > 0 {
		results, rerr := tryRepair(normalized, *repair, *maxCand)
		if rerr != nil {
			fmt.Fprintln(os.Stderr, "repair error:", rerr)
			os.Exit(1)
		}
		if len(results) == 0 {
			fmt.Fprintf(os.Stderr, "repair: no valid fix found with up to %d edits\n", *repair)
			os.Exit(1)
		}
		if len(results) > 1 {
			fmt.Fprintf(os.Stderr, "repair: found %d possible fixes (ambiguous)\n\n", len(results))
			for i, r := range results {
				fmt.Fprintf(os.Stderr, "[%d] edits=%d\n", i+1, len(r.Edits))
				printEdits(os.Stderr, r.Edits)
				if *prettyFlag {
					prettyPrint(os.Stderr, r.FixedDigits, editsToHighlight(r.Edits))
				} else {
					fmt.Fprintln(os.Stderr, r.FixedDigits)
				}
				fmt.Fprintln(os.Stderr)
			}
			os.Exit(1)
		}

		r := results[0]
		if *prettyFlag {
			fmt.Println("\x1b[1mREPAIRED\x1b[0m")
			printEdits(os.Stdout, r.Edits)
			fmt.Println()
			prettyPrint(os.Stdout, r.FixedDigits, editsToHighlight(r.Edits))
			fmt.Println("\n\x1b[1mDECODED\x1b[0m", r.Text)
		} else {
			fmt.Println(r.Text)
		}
		return
	}

	os.Exit(1)
}

