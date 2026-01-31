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
	base            = 100
	headerDigits    = 8  // LLLLGGGG
	headerGroups    = 4  // 8 digits / 2
	defaultFinalMod = 1_000_000 // 6 digits (3 groups)
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

// ---------------- Settings ----------------

type Settings struct {
	BlockDataGroups  int  // e.g. 5 or 10 (counts 2-digit groups)
	BlockCheckGroups int  // e.g. 2 (=> 4 digits) or 1 (=> 2 digits)
	FinalCheck       bool // add/verify final checksum
	FinalCheckGroups int  // fixed at 3 groups (6 digits) for now
}

func (s Settings) validate() error {
	if s.BlockDataGroups <= 0 {
		return fmt.Errorf("block-data-groups must be > 0")
	}
	if s.BlockCheckGroups <= 0 {
		return fmt.Errorf("block-check-groups must be > 0")
	}
	if s.BlockCheckGroups > 4 {
		// practical limit; can increase if you want
		return fmt.Errorf("block-check-groups too large (max 4 suggested)")
	}
	if s.FinalCheckGroups <= 0 {
		return fmt.Errorf("final-check-groups must be > 0")
	}
	return nil
}

func modForGroups(groups int) int {
	// groups of 2 digits => base 100 per group => 100^groups
	m := 1
	for i := 0; i < groups; i++ {
		m *= 100
	}
	return m
}

// ---------------- Helpers: digits ----------------

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

func splitIntoGroups(digits string, groupSize int) []string {
	var out []string
	for i := 0; i < len(digits); i += groupSize {
		end := i + groupSize
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

// ---------------- Checksums ----------------

// CRC over ASCII digits, then mod 100^k, formatted as k groups (2-digit each)
func checksumK(payloadDigits string, kGroups int) (string, error) {
	for _, r := range payloadDigits {
		if r < '0' || r > '9' {
			return "", fmt.Errorf("payload contains non-digit: %q", r)
		}
	}
	mod := modForGroups(kGroups)
	sum := crc32.ChecksumIEEE([]byte(payloadDigits))
	val := int(sum % uint32(mod))
	// format as 2*k digits (zero-padded)
	return fmt.Sprintf("%0*d", 2*kGroups, val), nil
}

// For block checksum, we include block index in digits to reduce “block swap” errors detection when final-check is off.
func blockChecksumDigits(header string, blockIndex int, blockDataDigits string, kGroups int) (string, error) {
	// blockIndex: 1..N as 4 digits
	blk := fmt.Sprintf("%04d", blockIndex)
	payload := header + blk + blockDataDigits
	return checksumK(payload, kGroups)
}

// final checksum covers everything except itself (header + all blocks including their checksums)
func finalChecksumDigits(allExceptFinal string, kGroups int) (string, error) {
	return checksumK(allExceptFinal, kGroups)
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

// ---------------- Encoding format ----------------
//
// DIGITS-ONLY FORMAT:
//
//   HEADER: 8 digits => LLLLGGGG
//     LLLL = byte length (0000..9999)
//     GGGG = count of DATA groups (0000..9999)
//
//   Then blocks:
//     [DATA(block)] [BCHK(block)]
//     where DATA(block) = up to BlockDataGroups groups (2 digits each)
//           BCHK(block) = BlockCheckGroups groups (2 digits each)
//
//   Optional final checksum at end:
//     FINAL = FinalCheckGroups groups (default 3 groups => 6 digits)
//     computed over: HEADER + all block segments (DATA+blockCHK) concatenated
//

func encodeText(text string, s Settings) (string, error) {
	if err := s.validate(); err != nil {
		return "", err
	}

	b := []byte(text)
	L := len(b)
	if L > 9999 {
		return "", fmt.Errorf("input too long in bytes (%d), max 9999", L)
	}

	x := new(big.Int).SetBytes(b)
	dataGroups := toBase100Digits(x)
	G := len(dataGroups)
	if G > 9999 {
		return "", fmt.Errorf("too many DATA groups (%d), max 9999", G)
	}

	header := fmt.Sprintf("%04d%04d", L, G)

	// build blocks
	var out strings.Builder
	out.WriteString(header)

	blockCount := 0
	for i := 0; i < G; i += s.BlockDataGroups {
		blockCount++
		end := i + s.BlockDataGroups
		if end > G {
			end = G
		}
		blockData := dataGroups[i:end]
		blockDataDigits := groupsToDigits(blockData)

		bchk, err := blockChecksumDigits(header, blockCount, blockDataDigits, s.BlockCheckGroups)
		if err != nil {
			return "", err
		}
		out.WriteString(blockDataDigits)
		out.WriteString(bchk)
	}

	if s.FinalCheck {
		fc, err := finalChecksumDigits(out.String(), s.FinalCheckGroups)
		if err != nil {
			return "", err
		}
		out.WriteString(fc)
	}

	return out.String(), nil
}

// ---------------- Decoding & validation ----------------

type BlockStatus struct {
	BlockIndex int
	Ok         bool
	Expected   string
	Got        string
}

type DecodeReport struct {
	HeaderOK          bool
	FinalOK           bool
	BadBlocks         []BlockStatus
	TotalBlocks       int
	TotalDataGroups   int
	FinalExpected     string
	FinalGot          string
	NormalizedDigits  string
}

func decodeCodeWithReport(code string, s Settings, verify bool) (string, DecodeReport, error) {
	var rep DecodeReport
	if err := s.validate(); err != nil {
		return "", rep, err
	}

	d := stripNonDigits(code)
	rep.NormalizedDigits = d

	if len(d) < headerDigits {
		return "", rep, decodeErr("format", "code too short for header")
	}
	if !isAllDigits(d) {
		return "", rep, decodeErr("format", "code contains non-digits after normalization (unexpected)")
	}

	header := d[:headerDigits]
	Lraw := header[:4]
	Graw := header[4:8]

	Lu, err := parseUintFixedDigits(Lraw)
	if err != nil {
		return "", rep, decodeErr("header", "invalid LLLL in header")
	}
	Gu, err := parseUintFixedDigits(Graw)
	if err != nil {
		return "", rep, decodeErr("header", "invalid GGGG in header")
	}
	L := int(Lu)
	G := int(Gu)
	rep.HeaderOK = true
	rep.TotalDataGroups = G

	// Determine if final checksum exists
	finalDigits := 0
	if s.FinalCheck {
		finalDigits = 2 * s.FinalCheckGroups
		if len(d) < headerDigits+finalDigits {
			return "", rep, decodeErr("format", "code too short for final checksum")
		}
	}

	body := d[headerDigits:]
	finalGot := ""
	bodyWithoutFinal := body
	if s.FinalCheck {
		finalGot = body[len(body)-finalDigits:]
		bodyWithoutFinal = body[:len(body)-finalDigits]
		rep.FinalGot = finalGot
	}

	// Parse blocks using G and per-block sizes
	perBlockCheckDigits := 2 * s.BlockCheckGroups

	// We know how many blocks:
	totalBlocks := (G + s.BlockDataGroups - 1) / s.BlockDataGroups
	rep.TotalBlocks = totalBlocks

	// Walk blocks, reconstruct data groups, and validate block checksums
	dataGroups := make([]int, 0, G)

	cursor := 0
	for blk := 1; blk <= totalBlocks; blk++ {
		remainingData := G - len(dataGroups)
		thisDataGroups := s.BlockDataGroups
		if remainingData < thisDataGroups {
			thisDataGroups = remainingData
		}
		thisDataDigits := thisDataGroups * 2

		need := thisDataDigits + perBlockCheckDigits
		if cursor+need > len(bodyWithoutFinal) {
			return "", rep, decodeErr("format", fmt.Sprintf("truncated at block %d (need %d digits, have %d)", blk, need, len(bodyWithoutFinal)-cursor))
		}

		blockDataDigits := bodyWithoutFinal[cursor : cursor+thisDataDigits]
		blockChkGot := bodyWithoutFinal[cursor+thisDataDigits : cursor+need]
		cursor += need

		// validate block checksum
		exp, err := blockChecksumDigits(header, blk, blockDataDigits, s.BlockCheckGroups)
		if err != nil {
			return "", rep, decodeErr("checksum", "failed to compute block checksum")
		}
		ok := (blockChkGot == exp)
		if verify && !ok {
			rep.BadBlocks = append(rep.BadBlocks, BlockStatus{
				BlockIndex: blk,
				Ok:         false,
				Expected:   exp,
				Got:        blockChkGot,
			})
		}

		// parse block data digits into groups
		for i := 0; i < len(blockDataDigits); i += 2 {
			pair := blockDataDigits[i : i+2]
			v, err := parseUintFixedDigits(pair)
			if err != nil || v > 99 {
				return "", rep, decodeErr("data", fmt.Sprintf("invalid base-100 group %q in block %d", pair, blk))
			}
			dataGroups = append(dataGroups, int(v))
		}
	}

	// extra garbage?
	if cursor != len(bodyWithoutFinal) {
		return "", rep, decodeErr("format", "extra trailing digits in body (settings mismatch?)")
	}

	// verify final checksum
	if verify && s.FinalCheck {
		fullExceptFinal := header + bodyWithoutFinal
		exp, err := finalChecksumDigits(fullExceptFinal, s.FinalCheckGroups)
		if err != nil {
			return "", rep, decodeErr("checksum", "failed to compute final checksum")
		}
		rep.FinalExpected = exp
		rep.FinalOK = (finalGot == exp)
		if !rep.FinalOK {
			// keep going; we’ll still try to decode (maybe only final part mistyped)
		}
	} else {
		rep.FinalOK = true
	}

	// If verify and there are bad blocks, stop with checksum error (caller may repair)
	if verify && len(rep.BadBlocks) > 0 {
		return "", rep, decodeErr("checksum", fmt.Sprintf("%d block checksum mismatches", len(rep.BadBlocks)))
	}
	if verify && s.FinalCheck && !rep.FinalOK {
		return "", rep, decodeErr("checksum", "final checksum mismatch")
	}

	// decode data groups to bytes
	x := fromBase100Digits(dataGroups)
	outBytes, err := toFixedLengthBytes(x, L)
	if err != nil {
		return "", rep, decodeErr("bytes", err.Error())
	}
	if !utf8.Valid(outBytes) {
		return "", rep, decodeErr("utf8", "decoded bytes are not valid UTF-8")
	}
	return string(outBytes), rep, nil
}

// ---------------- Pretty printing ----------------

func prettyPrint(out io.Writer, digitsOnly string, s Settings, highlight map[int]map[int]bool) {
	// highlight[blockIndex][posInBlockSegment] == true
	// posInBlockSegment counts groups in the *printed segment* of that block:
	//   1..BlockDataGroups for data, then (BlockDataGroups+1..BlockDataGroups+BlockCheckGroups) for block checksum
	// (last block may have fewer data groups; we still number within its real size)

	d := stripNonDigits(digitsOnly)
	if len(d) < headerDigits {
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

	header := d[:headerDigits]
	L := header[:4]
	G := header[4:8]

	fmt.Fprintf(out, "%sHEADER%s  LEN=%s%s%s  GROUPS=%s%s%s\n\n",
		bold, reset, cyan, L, reset, cyan, G, reset)

	// parse header to know blocks
	Gu, _ := parseUintFixedDigits(G)
	totalGroups := int(Gu)
	totalBlocks := (totalGroups + s.BlockDataGroups - 1) / s.BlockDataGroups

	// remove final checksum for printing separately
	body := d[headerDigits:]
	finalDigits := 0
	finalPart := ""
	bodyWithoutFinal := body
	if s.FinalCheck {
		finalDigits = 2 * s.FinalCheckGroups
		if len(body) >= finalDigits {
			finalPart = body[len(body)-finalDigits:]
			bodyWithoutFinal = body[:len(body)-finalDigits]
		}
	}

	cursor := 0
	perBlockCheckDigits := 2 * s.BlockCheckGroups

	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := totalGroups - (blk-1)*s.BlockDataGroups
		thisDataGroups := s.BlockDataGroups
		if remaining < thisDataGroups {
			thisDataGroups = remaining
		}
		thisDataDigits := thisDataGroups * 2

		blockData := bodyWithoutFinal[cursor : cursor+thisDataDigits]
		blockChk := bodyWithoutFinal[cursor+thisDataDigits : cursor+thisDataDigits+perBlockCheckDigits]
		cursor += thisDataDigits + perBlockCheckDigits

		// groups for printing
		dataGroups := splitIntoGroups(blockData, 2)
		chkGroups := splitIntoGroups(blockChk, 2)

		// build line: [NN] data... | chk...
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

	if s.FinalCheck && finalPart != "" {
		finalGroups := splitIntoGroups(finalPart, 2)
		fmt.Fprintf(out, "\n%sFINAL%s: %s\n", bold, reset, strings.Join(finalGroups, " "))
	}

	fmt.Fprintf(out, "\n%sFULL%s %s\n", bold, reset, d)
}

// ---------------- Repair ----------------

type Edit struct {
	Block     int // 1-based
	Pos       int // group position within printed block segment (data then chk)
	From, To  int
}

type RepairResult struct {
	FixedDigits string
	Text        string
	Edits       []Edit
}

func tryRepair(digitsOnly string, s Settings, maxEdits int, maxCandidates int) ([]RepairResult, error) {
	if maxEdits <= 0 {
		return nil, nil
	}
	if maxCandidates <= 0 {
		maxCandidates = 1
	}
	if err := s.validate(); err != nil {
		return nil, err
	}

	// First, decode with report to find bad blocks / whether final mismatch
	_, rep, err := decodeCodeWithReport(digitsOnly, s, true)
	if err == nil {
		return nil, nil // nothing to repair
	}

	// If no bad blocks but final mismatch only: we can attempt to repair FINAL digits by brute-forcing FINAL groups.
	// We’ll do that after block repair attempt.
	badBlocks := make([]int, 0, len(rep.BadBlocks))
	for _, b := range rep.BadBlocks {
		badBlocks = append(badBlocks, b.BlockIndex)
	}
	sort.Ints(badBlocks)

	normalized := stripNonDigits(digitsOnly)
	if len(normalized) < headerDigits {
		return nil, decodeErr("repair", "code too short")
	}

	// Build a mutable slice of 2-digit groups for the whole message
	if len(normalized)%2 != 0 {
		return nil, decodeErr("repair", "digits length not even")
	}
	allGroupsStr := splitIntoGroups(normalized, 2)
	allGroups := make([]int, len(allGroupsStr))
	for i, g := range allGroupsStr {
		v, e := parseUintFixedDigits(g)
		if e != nil || v > 99 {
			return nil, decodeErr("repair", fmt.Sprintf("invalid group %q at index %d", g, i))
		}
		allGroups[i] = int(v)
	}

	// Locate group ranges for each block segment (data+blockchk) in terms of absolute group indices.
	// Layout in groups:
	//   headerGroups (4) +
	//   blocks: for each block: dataGroups + checkGroups
	//   optional final: FinalCheckGroups
	// We know total data groups from header (GGGG)
	Graw := normalized[4:8]
	Gu, _ := parseUintFixedDigits(Graw)
	totalDataGroups := int(Gu)
	totalBlocks := (totalDataGroups + s.BlockDataGroups - 1) / s.BlockDataGroups

	type blockRange struct {
		blk          int
		startAbs     int // inclusive, in group indices
		dataCount    int
		checkCount   int
		endAbs       int // exclusive
	}
	ranges := []blockRange{}
	cursor := headerGroups
	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := totalDataGroups - (blk-1)*s.BlockDataGroups
		dataCount := s.BlockDataGroups
		if remaining < dataCount {
			dataCount = remaining
		}
		start := cursor
		end := cursor + dataCount + s.BlockCheckGroups
		ranges = append(ranges, blockRange{
			blk:        blk,
			startAbs:   start,
			dataCount:  dataCount,
			checkCount: s.BlockCheckGroups,
			endAbs:     end,
		})
		cursor = end
	}

	// final range (absolute groups)
	finalStart := cursor
	finalEnd := cursor
	if s.FinalCheck {
		finalEnd = finalStart + s.FinalCheckGroups
		if finalEnd > len(allGroups) {
			return nil, decodeErr("repair", "missing final checksum groups")
		}
	}

	// Target positions for edits:
	// - If we have bad blocks: search inside those blocks (both data and block checksum groups).
	// - Else (final mismatch only): search only inside FINAL groups.
	targetAbsPositions := []int{}
	targetMeta := map[int]Edit{} // template filled later

	inSet := func(x int, set []int) bool {
		for _, v := range set {
			if v == x {
				return true
			}
		}
		return false
	}

	if len(badBlocks) > 0 {
		for _, br := range ranges {
			if !inSet(br.blk, badBlocks) {
				continue
			}
			for abs := br.startAbs; abs < br.endAbs; abs++ {
				targetAbsPositions = append(targetAbsPositions, abs)
			}
		}
	} else if s.FinalCheck && !rep.FinalOK {
		for abs := finalStart; abs < finalEnd; abs++ {
			targetAbsPositions = append(targetAbsPositions, abs)
		}
	} else {
		// unknown mismatch type; nothing sensible
		return nil, decodeErr("repair", "no identifiable bad blocks or final mismatch in report")
	}

	// Map abs group index -> (block, posInBlockSegment) for reporting/highlighting
	absToLoc := func(abs int) (blk int, pos int, ok bool) {
		// final checksum "block" reported as 0
		if s.FinalCheck && abs >= finalStart && abs < finalEnd {
			return 0, abs - finalStart + 1, true
		}
		for _, br := range ranges {
			if abs >= br.startAbs && abs < br.endAbs {
				return br.blk, abs - br.startAbs + 1, true
			}
		}
		return 0, 0, false
	}

	for _, abs := range targetAbsPositions {
		blk, pos, ok := absToLoc(abs)
		if !ok {
			continue
		}
		targetMeta[abs] = Edit{Block: blk, Pos: pos}
	}

	results := make([]RepairResult, 0, maxCandidates)

	// DFS edits (1..maxEdits) over targetAbsPositions
	// DFS edits (1..maxEdits) over targetAbsPositions
	var dfs func(startIdx int, editsLeft int, chosenAbs []int, fromVals []int, toVals []int)

	testCandidate := func(chosenAbs []int, fromVals []int, toVals []int) {
		// Build candidate digits
		var b strings.Builder
		b.Grow(len(allGroups) * 2)
		for _, g := range allGroups {
			b.WriteString(fmt.Sprintf("%02d", g))
		}
		candDigits := b.String()

		// Verify fully
		text, _, derr := decodeCodeWithReport(candDigits, s, true)
		if derr != nil {
			return
		}
		reenc, eerr := encodeText(text, s)
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

		// test at any depth >=1 edit
		if len(chosenAbs) > 0 {
			testCandidate(chosenAbs, fromVals, toVals)
			if len(results) >= maxCandidates {
				return
			}
		}

		if editsLeft == 0 {
			return
		}

		for i := startIdx; i < len(targetAbsPositions); i++ {
			abs := targetAbsPositions[i]
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

	return results, nil
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
               [--block-data-groups N] [--block-check-groups K]
               [--final-check | --no-final-check]

  urlcode decode [--code "..."] [--pretty] [--no-check]
               [--block-data-groups N] [--block-check-groups K]
               [--final-check | --no-final-check]
               [--repair E] [--max-candidates C]

Notes:
- Groups are 2-digit numbers (00..99).
- Each printed block shows: DATA groups then '|' then block checksum groups.
- Header is always: LLLLGGGG (byte length + number of DATA groups).

Examples:
  urlcode encode --text "https://example.com/..." --pretty --block-data-groups 5 --block-check-groups 2 --final-check
  urlcode decode --code "...." --pretty --block-data-groups 10 --block-check-groups 1 --no-final-check
  urlcode decode --code "...." --repair 1 --max-candidates 3 --pretty

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

func commonFlags(fs *flag.FlagSet) (*int, *int, *bool, *bool) {
	blockData := fs.Int("block-data-groups", 5, "How many 2-digit groups of DATA per block (e.g. 5 or 10)")
	blockChk := fs.Int("block-check-groups", 2, "How many 2-digit groups of checksum per block (e.g. 2 or 1)")

	finalOn := fs.Bool("final-check", true, "Enable final checksum")
	finalOff := fs.Bool("no-final-check", false, "Disable final checksum (overrides --final-check)")

	return blockData, blockChk, finalOn, finalOff
}

func buildSettings(blockData, blockChk int, finalOn, finalOff bool) Settings {
	final := finalOn
	if finalOff {
		final = false
	}
	return Settings{
		BlockDataGroups:  blockData,
		BlockCheckGroups: blockChk,
		FinalCheck:       final,
		FinalCheckGroups: 3, // 6 digits
	}
}

func runEncode(args []string) {
	fs := flag.NewFlagSet("encode", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)

	text := fs.String("text", "", "Text/URL to encode (or read from stdin)")
	prettyFlag := fs.Bool("pretty", false, "Pretty block-numbered output")

	blockData, blockChk, finalOn, finalOff := commonFlags(fs)

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

	s := buildSettings(*blockData, *blockChk, *finalOn, *finalOff)
	if err := s.validate(); err != nil {
		fmt.Fprintln(os.Stderr, "settings error:", err)
		os.Exit(2)
	}

	code, err := encodeText(in, s)
	if err != nil {
		fmt.Fprintln(os.Stderr, "encode error:", err)
		os.Exit(1)
	}

	if *prettyFlag {
		prettyPrint(os.Stdout, code, s, nil)
	} else {
		// simple: space each 2-digit group, dash between printed blocks
		fmt.Println(formatCompactPhone(code, s))
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

	blockData, blockChk, finalOn, finalOff := commonFlags(fs)

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

	s := buildSettings(*blockData, *blockChk, *finalOn, *finalOff)
	if err := s.validate(); err != nil {
		fmt.Fprintln(os.Stderr, "settings error:", err)
		os.Exit(2)
	}

	normalized := stripNonDigits(in)
	text, rep, err := decodeCodeWithReport(normalized, s, !*noCheck)
	if err == nil {
		if *prettyFlag {
			fmt.Println("\x1b[1mDECODED\x1b[0m", text)
			fmt.Println()
			prettyPrint(os.Stdout, normalized, s, nil)
		} else {
			fmt.Println(text)
		}
		return
	}

	// If verify disabled, err might be utf8/bytes/etc; just print it
	if *noCheck {
		fmt.Fprintln(os.Stderr, "decode error:", err)
		os.Exit(1)
	}

	// Show a helpful report
	fmt.Fprintln(os.Stderr, "decode error:", err)
	if len(rep.BadBlocks) > 0 {
		fmt.Fprintf(os.Stderr, "bad blocks (%d):\n", len(rep.BadBlocks))
		for _, b := range rep.BadBlocks {
			fmt.Fprintf(os.Stderr, " - block %d: expected %s got %s\n", b.BlockIndex, b.Expected, b.Got)
		}
	}
	if s.FinalCheck && !rep.FinalOK {
		fmt.Fprintf(os.Stderr, "final checksum mismatch: expected %s got %s\n", rep.FinalExpected, rep.FinalGot)
	}

	// repair
	if *repair > 0 {
		results, rerr := tryRepair(normalized, s, *repair, *maxCand)
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
				hl := editsToHighlight(r.Edits)
				if *prettyFlag {
					prettyPrint(os.Stderr, r.FixedDigits, s, hl)
				} else {
					fmt.Fprintln(os.Stderr, formatCompactPhone(r.FixedDigits, s))
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
			hl := editsToHighlight(r.Edits)
			prettyPrint(os.Stdout, r.FixedDigits, s, hl)
			fmt.Println("\n\x1b[1mDECODED\x1b[0m", r.Text)
		} else {
			fmt.Println(r.Text)
		}
		return
	}

	os.Exit(1)
}

// Simple phone format: show each block as "dd dd ... | cc cc" separated by " - "
// (header printed first as 4 groups)
func formatCompactPhone(digitsOnly string, s Settings) string {
	d := stripNonDigits(digitsOnly)
	if len(d) < headerDigits {
		return d
	}
	header := d[:headerDigits]
	body := d[headerDigits:]

	// strip final
	if s.FinalCheck {
		fd := 2 * s.FinalCheckGroups
		if len(body) >= fd {
			body = body[:len(body)-fd]
		}
	}

	hg := splitIntoGroups(header, 2)
	parts := []string{strings.Join(hg, " ")}

	// parse blocks using header G
	Gu, _ := parseUintFixedDigits(header[4:8])
	totalGroups := int(Gu)
	totalBlocks := (totalGroups + s.BlockDataGroups - 1) / s.BlockDataGroups

	cursor := 0
	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := totalGroups - (blk-1)*s.BlockDataGroups
		thisData := s.BlockDataGroups
		if remaining < thisData {
			thisData = remaining
		}
		dataDigits := thisData * 2
		chkDigits := s.BlockCheckGroups * 2

		seg := body[cursor : cursor+dataDigits+chkDigits]
		cursor += dataDigits + chkDigits

		data := splitIntoGroups(seg[:dataDigits], 2)
		chk := splitIntoGroups(seg[dataDigits:], 2)

		parts = append(parts, strings.Join(data, " ")+" | "+strings.Join(chk, " "))
	}

	return strings.Join(parts, " - ")
}

func printEdits(out io.Writer, edits []Edit) {
	fmt.Fprintln(out, "\x1b[1mEDITS\x1b[0m")
	for _, e := range edits {
		if e.Block == 0 {
			fmt.Fprintf(out, " - FINAL pos=%d  %02d -> %02d\n", e.Pos, e.From, e.To)
			continue
		}
		fmt.Fprintf(out, " - block=%d pos=%d  %02d -> %02d\n", e.Block, e.Pos, e.From, e.To)
	}
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
