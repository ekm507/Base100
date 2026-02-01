# Developer Notes — urlcode internals

این سند برای توسعه‌دهنده‌هاست: فرمت دقیق، چک‌سام‌ها، و منطق repair.

---

## 1) Data model (base100)

- متن ورودی به `[]byte` تبدیل می‌شود.
- `big.Int` از روی bytes ساخته می‌شود (`SetBytes`).
- سپس به base100 تبدیل می‌شود:
  - هر "digit" در بازه‌ی 0..99 است.
  - هر digit به صورت دو رقم ده‌دهی `00..99` در خروجی نمایش داده می‌شود.
- برای decode:
  - digits base100 → `big.Int` → bytes با طول ثابت `L` (از هدر)

این روش تضمین می‌کند بازسازی دقیق bytes ممکن باشد (با `toFixedLengthBytes` و طول `L`).

---

## 2) Wire format

تمام پیام digits-only است (فقط 0..9). هر "گروه" 2 رقم دارد و معادل یک مقدار 0..99 است.

### 2.1 Header (9 groups = 18 digits)

Header groups:
1. `VV` : version (فعلاً 01)
2. `BD` : block data groups (1..99)
3. `BC` : block checksum groups (1..99)
4. `FL` : flags (reserved; فعلاً 00)
5. `LL` : byte length high (base100)
6. `ll` : byte length low  (base100) => `L = 100*LL + ll` (0..9999)
7. `GG` : data group count high (base100)
8. `gg` : data group count low  (base100) => `G = 100*GG + gg` (0..9999)
9. `FB` : final checksum bytes (0..32). اگر 0 باشد final نداریم.

Header به صورت `groupsToDigits([]int{...})` سریالایز می‌شود.

### 2.2 Body

Body شامل بلوک‌هاست:

برای block index = 1..N:
- `DATA` : تا `BD` گروه (آخرین بلوک ممکن است کمتر)
- `BCHK` : دقیقاً `BC` گروه

که:
`N = ceil(G / BD)` و تعداد گروه‌های DATA کل پیام `G` از header می‌آید.

### 2.3 Final checksum (optional)

اگر `FB > 0`:
- `SHA-256` روی ASCII digits of `(HEADER + BODY_without_final)` گرفته می‌شود.
- `FB` بایت اول انتخاب می‌شود.
- این بایت‌ها به یک `big.Int` تبدیل و سپس به base100 digits تبدیل می‌شوند.
- طول digits نهایی ثابت می‌شود تا ambiguity نداشته باشیم:
  - تعداد گروه‌های لازم `finalGroupsCountForBytes(FB)` است (کمترین g که 100^g >= 256^FB)
  - سپس با صفر از چپ pad می‌شود تا دقیقاً g گروه شود.

در نتیجه طول بخش final فقط تابع `FB` است و در decode از header خوانده می‌شود.

---

## 3) Checksums

### 3.1 Block checksum (BCHK)
- هدف: یافتن سریع بلوک خراب برای انتقال دستی/تلفنی
- الگوریتم: `CRC32(payloadDigits) mod 100^BC`
- payloadDigits:
  - `headerDigits` +
  - `blockIndex` به صورت 2 گروه base100 (4 digit) +
  - `blockDataDigits`
- سپس نتیجه به `BC` گروه 2 رقمی تبدیل می‌شود (2*BC digits).

مزیت blockIndex: در صورت جابجایی/تکرار/حذف بلوک احتمال catch شدن بالاتر می‌رود.

### 3.2 Final checksum
- هدف: اطمینان قوی end-to-end
- الگوریتم: SHA-256 و truncate به `FB` بایت
- encoding: base100 با طول ثابت گروه‌ها

---

## 4) Decode pipeline

1) strip non-digits
2) parse header → `Header{BD,BC,L,G,FB}`
3) جدا کردن بخش final اگر `FB > 0` (طول ثابت)
4) parse blocks با دانستن `G, BD, BC`
5) verify block checksums (اگر verify=true)
6) verify final checksum (اگر verify=true و FB>0)
7) reconstruct bytes:
   - dataGroups → big.Int → bytes of length L
   - UTF-8 validation

DecodeReport شامل:
- Header
- لیست bad blocks (expected/got)
- final expected/got (اگر فعال)

---

## 5) Repair

Repair دو حالت دارد:

### 5.1 Guided repair (recommended)
- ابتدا decode report می‌گیرد.
- اگر بلوک‌های خراب وجود دارند:
  - یکی‌یکی بلوک‌های خراب را انتخاب می‌کند.
  - داخل همان range (data+blockchk) با DFS محدود تا N تغییر، به دنبال وضعیتی می‌گردد که آن بلوک دیگر bad نباشد.
  - این کار اجازه می‌دهد **چند خطا در یک بلوک** با `--repair N` پوشش داده شود.
- در پایان، اگر final فعال باشد و هنوز mismatch باشد، می‌تواند final range را هم تا N تغییر اصلاح کند (بسته به scope).

### 5.2 Global DFS (fallback)
- روی مجموعه‌ی موقعیت‌هایی که scope اجازه داده DFS می‌کند:
  - `auto/bad` ⇒ بلوک‌های bad
  - `all` ⇒ کل بلوک‌ها (+ final)
  - `blocks:` ⇒ بلوک‌های انتخاب‌شده
  - `final` ⇒ فقط final
- در هر depth، candidate با:
  - decode verify=true
  - و re-encode exact-match
  تایید می‌شود تا false positive کم شود.

> نکته: Repair در بدترین حالت می‌تواند انفجاری شود؛ scope و guided برای کنترل هزینه هستند.

---

## 6) Pretty printing

- Header به صورت گروه‌های 2 رقمی چاپ می‌شود.
- سپس بلوک‌ها:
  - `BD` گروه داده (زرد)
  - `|` separator
  - `BC` گروه چک‌سام (سبز)
- `FINAL` اگر فعال باشد (فیروزه‌ای)
- اگر repair انجام شده باشد، گروه‌های تغییر کرده قرمز می‌شوند (highlight map).

---

## 7) Extension points

- جایگزینی CRC32 بلوکی با تابع سریع‌تر/بهتر (مثلاً xxhash) اگر نیاز شد.
- افزایش ظرفیت header (افزودن نوع checksum، یا الگوریتم نهایی غیر SHA-256).
- افزودن "human-friendly separators" در خروجی non-pretty.
- اضافه کردن حالت "streaming" برای encode/decode خیلی بزرگ (فعلاً محدود به 9999 بایت).

---

## 8) Security / Reliability notes

- این سیستم رمزنگاری/امنیت برای secrecy نیست؛ برای *integrity + usability* طراحی شده است.
- `final-bytes` تعیین‌کننده‌ی احتمال تصادفی درست شدن checksum است.
- block checksum برای localization خطاست؛ final checksum برای اطمینان سراسری.
