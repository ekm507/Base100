package main

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"flag"
	"fmt"
	"hash/crc32"
	"io"
	"math/big"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode/utf8"
)

const (
	base = 100

	versionCurrent = 1

	// Header groups (2-digit groups):
	// VV BD BC FL LL ll GG gg FB
	// VV: version
	// BD: block data groups
	// BC: block checksum groups
	// FL: flags (reserved)
	// LL ll: byte length L = 100*LL + ll
	// GG gg: data group count G = 100*GG + gg
	// FB: final checksum bytes (0 disables final)
	headerGroups = 9
	headerDigits = headerGroups * 2

	maxLenBytes = 9999
	maxGroups   = 9999

	maxFinalBytes = 32 // SHA-256 has 32 bytes
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

func digitsToGroups2(digits string) ([]int, error) {
	if len(digits)%2 != 0 {
		return nil, fmt.Errorf("digits length not even")
	}
	gs := splitIntoGroups(digits, 2)
	out := make([]int, len(gs))
	for i, g := range gs {
		u, err := parseUintFixedDigits(g)
		if err != nil || u > 99 {
			return nil, fmt.Errorf("invalid group %q", g)
		}
		out[i] = int(u)
	}
	return out, nil
}

// ---------------- Header ----------------

type Header struct {
	Version    int
	BD         int // block data groups
	BC         int // block checksum groups
	Flags      int // reserved
	L          int // byte length
	G          int // data group count (base100 digits count)
	FinalBytes int // 0 disables final
}

func (h Header) finalEnabled() bool { return h.FinalBytes > 0 }

func (h Header) validate() error {
	if h.Version != versionCurrent {
		return fmt.Errorf("unsupported version: %d", h.Version)
	}
	if h.BD <= 0 || h.BD > 99 {
		return fmt.Errorf("invalid BD: %d", h.BD)
	}
	if h.BC <= 0 || h.BC > 99 {
		return fmt.Errorf("invalid BC: %d", h.BC)
	}
	if h.L < 0 || h.L > maxLenBytes {
		return fmt.Errorf("invalid L: %d", h.L)
	}
	if h.G < 0 || h.G > maxGroups {
		return fmt.Errorf("invalid G: %d", h.G)
	}
	if h.FinalBytes < 0 || h.FinalBytes > maxFinalBytes {
		return fmt.Errorf("invalid FinalBytes: %d", h.FinalBytes)
	}
	return nil
}

func encodeHeaderDigits(h Header) (string, error) {
	if err := h.validate(); err != nil {
		return "", err
	}
	llHi, llLo := h.L/100, h.L%100
	ggHi, ggLo := h.G/100, h.G%100

	// VV BD BC FL LL ll GG gg FB
	g := []int{
		h.Version,
		h.BD,
		h.BC,
		h.Flags,
		llHi,
		llLo,
		ggHi,
		ggLo,
		h.FinalBytes,
	}
	return groupsToDigits(g), nil
}

func parseHeaderDigits(digitsOnly string) (Header, error) {
	if len(digitsOnly) < headerDigits {
		return Header{}, decodeErr("header", "code too short for header")
	}
	raw := digitsOnly[:headerDigits]
	if !isAllDigits(raw) {
		return Header{}, decodeErr("header", "header contains non-digits")
	}
	gr := splitIntoGroups(raw, 2)
	if len(gr) != headerGroups {
		return Header{}, decodeErr("header", "header split failed")
	}

	val := make([]int, headerGroups)
	for i := 0; i < headerGroups; i++ {
		u, err := parseUintFixedDigits(gr[i])
		if err != nil || u > 99 {
			return Header{}, decodeErr("header", fmt.Sprintf("invalid group %q at index %d", gr[i], i))
		}
		val[i] = int(u)
	}

	h := Header{
		Version:    val[0],
		BD:         val[1],
		BC:         val[2],
		Flags:      val[3],
		L:          val[4]*100 + val[5],
		G:          val[6]*100 + val[7],
		FinalBytes: val[8],
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

// CRC32(payloadDigits) mod 100^k, formatted as 2*k digits
func checksumCRCMod(payloadDigits string, kGroups int) (string, error) {
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
	// 2 groups (4 digits) base100
	hi := blockIndex / 100
	lo := blockIndex % 100
	return fmt.Sprintf("%02d%02d", hi, lo)
}

func blockChecksumDigits(headerDigits string, blockIndex int, blockDataDigits string, bcGroups int) (string, error) {
	payload := headerDigits + blockIndexDigits(blockIndex) + blockDataDigits
	return checksumCRCMod(payload, bcGroups)
}

// final checksum: SHA-256 over ASCII digits of (header + blocks), take first N bytes,
// convert to base100 groups of fixed length that depends on N.
func finalGroupsCountForBytes(n int) int {
	// Need g such that 100^g >= 256^n
	// We compute exactly using big.Int powers.
	if n <= 0 {
		return 0
	}
	pow256 := new(big.Int).Exp(big.NewInt(256), big.NewInt(int64(n)), nil)
	g := 1
	pow100 := big.NewInt(100)
	cur := new(big.Int).Set(pow100)
	for cur.Cmp(pow256) < 0 {
		g++
		cur.Mul(cur, pow100)
	}
	return g
}

func sha256FinalDigits(payloadDigits string, finalBytes int) (string, error) {
	if finalBytes <= 0 {
		return "", nil
	}
	if finalBytes > maxFinalBytes {
		return "", fmt.Errorf("finalBytes too large: %d", finalBytes)
	}
	for _, r := range payloadDigits {
		if r < '0' || r > '9' {
			return "", fmt.Errorf("payload contains non-digit: %q", r)
		}
	}

	sum := sha256.Sum256([]byte(payloadDigits))
	b := sum[:finalBytes]

	// bytes -> big.Int -> base100 groups
	x := new(big.Int).SetBytes(b)
	groups := toBase100Digits(x)

	need := finalGroupsCountForBytes(finalBytes)
	if len(groups) > need {
		// should not happen if need computed correctly, but be safe
		return "", fmt.Errorf("internal: final groups length %d exceeds expected %d", len(groups), need)
	}
	if len(groups) < need {
		pad := make([]int, need-len(groups))
		groups = append(pad, groups...)
	}
	return groupsToDigits(groups), nil
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
	BD         int
	BC         int
	FinalBytes int // 0 disables final
}

func encodeText(text string, es EncodeSettings) (string, error) {
	if es.BD <= 0 || es.BD > 99 {
		return "", fmt.Errorf("block-data-groups must be 1..99")
	}
	if es.BC <= 0 || es.BC > 99 {
		return "", fmt.Errorf("block-check-groups must be 1..99")
	}
	if es.FinalBytes < 0 || es.FinalBytes > maxFinalBytes {
		return "", fmt.Errorf("final-bytes must be 0..%d", maxFinalBytes)
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

	h := Header{
		Version:    versionCurrent,
		BD:         es.BD,
		BC:         es.BC,
		Flags:      0,
		L:          L,
		G:          G,
		FinalBytes: es.FinalBytes,
	}
	headerDigitsStr, err := encodeHeaderDigits(h)
	if err != nil {
		return "", err
	}

	var out strings.Builder
	out.WriteString(headerDigitsStr)

	// blocks
	blockCount := 0
	for i := 0; i < G; i += es.BD {
		blockCount++
		end := i + es.BD
		if end > G {
			end = G
		}
		blockDataDigits := groupsToDigits(dataGroups[i:end])

		bchk, err := blockChecksumDigits(headerDigitsStr, blockCount, blockDataDigits, es.BC)
		if err != nil {
			return "", err
		}

		out.WriteString(blockDataDigits)
		out.WriteString(bchk)
	}

	// final checksum
	if es.FinalBytes > 0 {
		finalDigits, err := sha256FinalDigits(out.String(), es.FinalBytes)
		if err != nil {
			return "", err
		}
		out.WriteString(finalDigits)
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
	Header        Header
	BadBlocks     []BlockStatus
	FinalOK       bool
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

	// strip final
	finalDigitsLen := 0
	if h.finalEnabled() {
		g := finalGroupsCountForBytes(h.FinalBytes)
		finalDigitsLen = g * 2
		if len(body) < finalDigitsLen {
			return "", rep, decodeErr("format", "code too short for final checksum")
		}
		rep.FinalGot = body[len(body)-finalDigitsLen:]
		body = body[:len(body)-finalDigitsLen]
	} else {
		rep.FinalOK = true
	}

	// parse blocks
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

		// parse data groups
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
		return "", rep, decodeErr("format", "extra trailing digits (settings mismatch?)")
	}

	// final verify
	if verify && h.finalEnabled() {
		exp, err := sha256FinalDigits(headerDigitsStr+body, h.FinalBytes)
		if err != nil {
			return "", rep, decodeErr("checksum", "failed to compute final checksum")
		}
		rep.FinalExpected = exp
		rep.FinalOK = (rep.FinalGot == exp)
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
	// highlight[block][pos] true
	// block 0 means FINAL, pos 1..finalGroupsCount
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
	hg := splitIntoGroups(headerDigitsStr, 2)
	fmt.Fprintf(out, "%sHEADER%s  %s\n", bold, reset, strings.Join(hg, " "))

	finalGroups := 0
	if h.finalEnabled() {
		finalGroups = finalGroupsCountForBytes(h.FinalBytes)
	}
	fmt.Fprintf(out, "%sparams%s  ver=%d BD=%d BC=%d L=%d G=%d finalBytes=%d finalGroups=%d\n\n",
		bold, reset, h.Version, h.BD, h.BC, h.L, h.G, h.FinalBytes, finalGroups)

	body := d[headerDigits:]

	// strip final for block printing
	finalPart := ""
	if h.finalEnabled() {
		fd := finalGroups * 2
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
			pos := i + 1
			if highlight != nil && highlight[0] != nil && highlight[0][pos] {
				fg[i] = red + fg[i] + reset
			} else {
				fg[i] = cyan + fg[i] + reset
			}
		}
		fmt.Fprintf(out, "\n%sFINAL%s: %s\n", bold, reset, strings.Join(fg, " "))
	}

	fmt.Fprintf(out, "\n%sFULL%s %s\n", bold, reset, d)
}

// ---------------- Repair (guided + scope) ----------------

type BlockRange struct {
	Blk      int
	StartAbs int // inclusive (group index)
	EndAbs   int // exclusive
	DataCnt  int
	ChkCnt   int
}

type RepairScopeKind int

const (
	ScopeAuto RepairScopeKind = iota
	ScopeBad
	ScopeAll
	ScopeFinal
	ScopeBlocks
)

type RepairScope struct {
	Kind RepairScopeKind
}

func uniqueInts(a []int) []int {
	if len(a) == 0 {
		return a
	}
	out := []int{a[0]}
	for i := 1; i < len(a); i++ {
		if a[i] != a[i-1] {
			out = append(out, a[i])
		}
	}
	return out
}

func containsInt(a []int, x int) bool {
	for _, v := range a {
		if v == x {
			return true
		}
	}
	return false
}

func parseRepairScope(s string) (RepairScope, []int, error) {
	s = strings.TrimSpace(strings.ToLower(s))
	if s == "" || s == "auto" {
		return RepairScope{Kind: ScopeAuto}, nil, nil
	}
	if s == "bad" {
		return RepairScope{Kind: ScopeBad}, nil, nil
	}
	if s == "all" {
		return RepairScope{Kind: ScopeAll}, nil, nil
	}
	if s == "final" {
		return RepairScope{Kind: ScopeFinal}, nil, nil
	}
	if strings.HasPrefix(s, "blocks:") {
		rest := strings.TrimSpace(strings.TrimPrefix(s, "blocks:"))
		if rest == "" {
			return RepairScope{}, nil, fmt.Errorf("blocks: requires comma-separated list, e.g. blocks:3,7")
		}
		parts := strings.Split(rest, ",")
		var out []int
		for _, p := range parts {
			p = strings.TrimSpace(p)
			if p == "" {
				continue
			}
			u, err := strconv.Atoi(p)
			if err != nil || u <= 0 || u > 9999 {
				return RepairScope{}, nil, fmt.Errorf("invalid block number %q", p)
			}
			out = append(out, u)
		}
		sort.Ints(out)
		out = uniqueInts(out)
		if len(out) == 0 {
			return RepairScope{}, nil, fmt.Errorf("no valid blocks given")
		}
		return RepairScope{Kind: ScopeBlocks}, out, nil
	}
	return RepairScope{}, nil, fmt.Errorf("unknown repair scope %q (auto|bad|all|final|blocks:..)", s)
}

type Edit struct {
	Block int // 1..N ; 0=FINAL
	Pos   int // within block segment (data then chk), or within FINAL
	From  int
	To    int
}

type RepairResult struct {
	FixedDigits string
	Text        string
	Edits       []Edit
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

func buildRanges(h Header) (ranges []BlockRange, finalStart, finalEnd int, err error) {
	totalBlocks := (h.G + h.BD - 1) / h.BD
	cursor := headerGroups

	for blk := 1; blk <= totalBlocks; blk++ {
		remaining := h.G - (blk-1)*h.BD
		dataCnt := h.BD
		if remaining < dataCnt {
			dataCnt = remaining
		}
		start := cursor
		end := cursor + dataCnt + h.BC
		ranges = append(ranges, BlockRange{
			Blk:      blk,
			StartAbs: start,
			EndAbs:   end,
			DataCnt:  dataCnt,
			ChkCnt:   h.BC,
		})
		cursor = end
	}

	finalStart = cursor
	finalEnd = cursor
	if h.finalEnabled() {
		fg := finalGroupsCountForBytes(h.FinalBytes)
		finalEnd = finalStart + fg
	}
	return ranges, finalStart, finalEnd, nil
}

func tryRepair(code string, maxEdits int, maxCandidates int, scope RepairScope, scopeBlocks []int, guided bool) ([]RepairResult, error) {
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

	// initial report
	_, rep0, err0 := decodeCodeWithReport(d, true)
	if err0 == nil {
		return nil, nil
	}
	h := rep0.Header

	// full groups array
	allGroups, err := digitsToGroups2(d)
	if err != nil {
		return nil, decodeErr("repair", "failed to parse groups")
	}

	ranges, finalStart, finalEnd, _ := buildRanges(h)

	totalBlocks := (h.G + h.BD - 1) / h.BD

	badBlocks0 := []int{}
	for _, b := range rep0.BadBlocks {
		badBlocks0 = append(badBlocks0, b.BlockIndex)
	}
	sort.Ints(badBlocks0)
	badBlocks0 = uniqueInts(badBlocks0)

	// Decide eligible targets
	targetBlocks := []int(nil)
	targetFinal := false

	switch scope.Kind {
	case ScopeAuto:
		if len(badBlocks0) > 0 {
			targetBlocks = badBlocks0
		} else if h.finalEnabled() && !rep0.FinalOK {
			targetFinal = true
		} else {
			return nil, decodeErr("repair", "auto: no bad blocks or final mismatch detected")
		}
	case ScopeBad:
		if len(badBlocks0) == 0 {
			return nil, decodeErr("repair", "bad: no bad blocks detected")
		}
		targetBlocks = badBlocks0
	case ScopeAll:
		for i := 1; i <= totalBlocks; i++ {
			targetBlocks = append(targetBlocks, i)
		}
		if h.finalEnabled() {
			targetFinal = true
		}
	case ScopeFinal:
		if !h.finalEnabled() {
			return nil, decodeErr("repair", "final: final not enabled in header")
		}
		targetFinal = true
	case ScopeBlocks:
		for _, b := range scopeBlocks {
			if b < 1 || b > totalBlocks {
				return nil, decodeErr("repair", fmt.Sprintf("block %d out of range (1..%d)", b, totalBlocks))
			}
			targetBlocks = append(targetBlocks, b)
		}
	default:
		return nil, decodeErr("repair", "unknown scope")
	}

	// helper build digits
	buildDigits := func() string {
		var sb strings.Builder
		sb.Grow(len(allGroups) * 2)
		for _, g := range allGroups {
			sb.WriteString(fmt.Sprintf("%02d", g))
		}
		return sb.String()
	}

	// helper validate
	validateCandidate := func(candDigits string) (string, bool) {
		text, _, e := decodeCodeWithReport(candDigits, true)
		if e != nil {
			return "", false
		}
		es := EncodeSettings{BD: h.BD, BC: h.BC, FinalBytes: h.FinalBytes}
		reenc, e2 := encodeText(text, es)
		if e2 != nil {
			return "", false
		}
		if stripNonDigits(reenc) != candDigits {
			return "", false
		}
		return text, true
	}

	// map abs -> (block,pos)
	absToLoc := func(abs int) (blk int, pos int, ok bool) {
		// FINAL
		if h.finalEnabled() && abs >= finalStart && abs < finalEnd {
			return 0, abs - finalStart + 1, true
		}
		for _, br := range ranges {
			if abs >= br.StartAbs && abs < br.EndAbs {
				return br.Blk, abs - br.StartAbs + 1, true
			}
		}
		return 0, 0, false
	}

	results := make([]RepairResult, 0, maxCandidates)

	// ---------------- Guided: fix bad blocks first (allows multiple errors per block) ----------------
	if guided && len(targetBlocks) > 0 {
		editsLeft := maxEdits
		var allEdits []Edit

		for editsLeft > 0 {
			cand := buildDigits()
			_, rep, derr := decodeCodeWithReport(cand, true)
			if derr == nil {
				text, ok := validateCandidate(cand)
				if ok {
					results = append(results, RepairResult{FixedDigits: cand, Text: text, Edits: append([]Edit(nil), allEdits...)})
					return results, nil
				}
			}

			// current bad blocks within scope
			curBad := []int{}
			for _, b := range rep.BadBlocks {
				if containsInt(targetBlocks, b.BlockIndex) {
					curBad = append(curBad, b.BlockIndex)
				}
			}
			sort.Ints(curBad)
			curBad = uniqueInts(curBad)

			if len(curBad) == 0 {
				break
			}

			blk := curBad[0]
			var br BlockRange
			found := false
			for _, r := range ranges {
				if r.Blk == blk {
					br = r
					found = true
					break
				}
			}
			if !found {
				break
			}

			// local DFS in this block range
			fixed, chosenAbs, fromVals, toVals := localDFSFix(allGroups, br.StartAbs, br.EndAbs, editsLeft, func() bool {
				// Accept if this block no longer bad
				c := buildDigits()
				_, r, _ := decodeCodeWithReport(c, true)
				for _, bb := range r.BadBlocks {
					if bb.BlockIndex == blk {
						return false
					}
				}
				return true
			})
			if !fixed {
				break
			}

			// commit edits already applied by localDFSFix; record them
			for i, abs := range chosenAbs {
				bk, pos, ok := absToLoc(abs)
				if !ok {
					continue
				}
				allEdits = append(allEdits, Edit{Block: bk, Pos: pos, From: fromVals[i], To: toVals[i]})
			}
			editsLeft -= len(chosenAbs)
		}

		// optionally repair final if allowed and still mismatching
		if h.finalEnabled() && (targetFinal || scope.Kind == ScopeAuto || scope.Kind == ScopeAll) && editsLeft > 0 {
			cand := buildDigits()
			_, rep, _ := decodeCodeWithReport(cand, true)
			if !rep.FinalOK {
				fixed, chosenAbs, fromVals, toVals := localDFSFix(allGroups, finalStart, finalEnd, editsLeft, func() bool {
					c := buildDigits()
					_, r, e := decodeCodeWithReport(c, true)
					return e == nil && r.FinalOK
				})
				if fixed {
					for i, abs := range chosenAbs {
						bk, pos, ok := absToLoc(abs)
						if !ok {
							continue
						}
						allEdits = append(allEdits, Edit{Block: bk, Pos: pos, From: fromVals[i], To: toVals[i]})
					}
					editsLeft -= len(chosenAbs)
				}
			}
		}

		cand := buildDigits()
		text, ok := validateCandidate(cand)
		if ok {
			results = append(results, RepairResult{FixedDigits: cand, Text: text, Edits: allEdits})
			return results, nil
		}
		// fall through to global DFS (scope constrained)
	}

	// ---------------- Global DFS (scope-constrained) ----------------

	// Build target abs list
	targetAbs := []int{}
	targetMeta := map[int]Edit{}

	// blocks
	if len(targetBlocks) > 0 {
		for _, br := range ranges {
			if !containsInt(targetBlocks, br.Blk) {
				continue
			}
			for abs := br.StartAbs; abs < br.EndAbs; abs++ {
				targetAbs = append(targetAbs, abs)
				bk, pos, _ := absToLoc(abs)
				targetMeta[abs] = Edit{Block: bk, Pos: pos}
			}
		}
	}
	// final
	if targetFinal && h.finalEnabled() {
		for abs := finalStart; abs < finalEnd; abs++ {
			targetAbs = append(targetAbs, abs)
			bk, pos, _ := absToLoc(abs)
			targetMeta[abs] = Edit{Block: bk, Pos: pos}
		}
	}

	if len(targetAbs) == 0 {
		return nil, decodeErr("repair", "no target positions selected by scope")
	}

	var dfs func(startIdx int, editsLeft int, chosenAbs []int, fromVals []int, toVals []int)

	testCandidate := func(chosenAbs []int, fromVals []int, toVals []int) {
		candDigits := buildDigits()
		text, ok := validateCandidate(candDigits)
		if !ok {
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

	return results, nil
}

// local DFS within [startAbs,endAbs) to satisfy accept().
// Allows multiple errors in same block because it tries 1..maxEdits changes.
func localDFSFix(allGroups []int, startAbs, endAbs int, maxEdits int, accept func() bool) (fixed bool, chosenAbs []int, fromVals []int, toVals []int) {
	target := make([]int, 0, endAbs-startAbs)
	for abs := startAbs; abs < endAbs; abs++ {
		target = append(target, abs)
	}

	var bestChosen, bestFrom, bestTo []int

	var dfs func(startIdx int, editsLeft int, chosen []int, from []int, to []int) bool
	dfs = func(startIdx int, editsLeft int, chosen []int, from []int, to []int) bool {
		if len(chosen) > 0 && accept() {
			bestChosen = append([]int(nil), chosen...)
			bestFrom = append([]int(nil), from...)
			bestTo = append([]int(nil), to...)
			return true
		}
		if editsLeft == 0 {
			return false
		}
		for i := startIdx; i < len(target); i++ {
			abs := target[i]
			orig := allGroups[abs]
			for nv := 0; nv < 100; nv++ {
				if nv == orig {
					continue
				}
				allGroups[abs] = nv
				if dfs(i+1, editsLeft-1,
					append(chosen, abs),
					append(from, orig),
					append(to, nv),
				) {
					return true
				}
				allGroups[abs] = orig
			}
		}
		return false
	}

	for e := 1; e <= maxEdits; e++ {
		if dfs(0, e, nil, nil, nil) {
			return true, bestChosen, bestFrom, bestTo
		}
	}
	return false, nil, nil, nil
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
               --final-bytes B

  urlcode decode [--code "..."] [--pretty] [--no-check]
               [--repair E] [--max-candidates C]
               [--repair-scope auto|bad|all|final|blocks:1,2]
               [--repair-guided=true|false]

Notes:
- Decode reads BD/BC/final-bytes from HEADER; you do NOT pass them on decode.
- Header groups (2-digit): VV BD BC FL LL ll GG gg FB
- final-bytes: 0 disables final; otherwise uses SHA-256 first B bytes, encoded to base100 groups.
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
	finalBytes := fs.Int("final-bytes", 8, "Final checksum strength in bytes: 0..32 (0 disables)")

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

	code, err := encodeText(in, EncodeSettings{BD: *bd, BC: *bc, FinalBytes: *finalBytes})
	if err != nil {
		fmt.Fprintln(os.Stderr, "encode error:", err)
		os.Exit(1)
	}

	if *prettyFlag {
		prettyPrint(os.Stdout, code, nil)
	} else {
		fmt.Println(code)
	}
}

func runDecode(args []string) {
	fs := flag.NewFlagSet("decode", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)

	code := fs.String("code", "", "Code to decode (or read from stdin)")
	prettyFlag := fs.Bool("pretty", false, "Pretty output")
	noCheck := fs.Bool("no-check", false, "Skip checksum verification (not recommended)")

	repair := fs.Int("repair", 0, "If checksum fails, brute-force repair with 1..E edits")
	maxCand := fs.Int("max-candidates", 3, "Max repair candidates to output")

	repairScopeStr := fs.String("repair-scope", "auto", "Repair scope: auto|bad|all|final|blocks:1,2")
	repairGuided := fs.Bool("repair-guided", true, "Guided repair using bad-block detection (recommended)")

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

	if *noCheck {
		fmt.Fprintln(os.Stderr, "decode error:", err)
		os.Exit(1)
	}

	// report
	fmt.Fprintln(os.Stderr, "decode error:", err)
	if len(rep.BadBlocks) > 0 {
		fmt.Fprintf(os.Stderr, "bad blocks (%d):\n", len(rep.BadBlocks))
		for _, b := range rep.BadBlocks {
			fmt.Fprintf(os.Stderr, " - block %d: expected %s got %s\n", b.BlockIndex, b.Expected, b.Got)
		}
	}
	if rep.Header.finalEnabled() && !rep.FinalOK {
		fmt.Fprintf(os.Stderr, "final mismatch: expected %s got %s\n", rep.FinalExpected, rep.FinalGot)
	}

	if *repair > 0 {
		scope, blockList, scErr := parseRepairScope(*repairScopeStr)
		if scErr != nil {
			fmt.Fprintln(os.Stderr, "repair-scope error:", scErr)
			os.Exit(2)
		}

		results, rerr := tryRepair(normalized, *repair, *maxCand, scope, blockList, *repairGuided)
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

