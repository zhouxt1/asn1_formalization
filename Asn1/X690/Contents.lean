import Asn1.Bits
import Asn1.X680.Syntax
import Asn1.X680.Time
import Asn1.X690.Iso2022

/-!
# The octets of an encoding that do not depend on the type's structure (X.690 8.1.2–8.1.5, 8.2–8.8,
8.19–8.23, 8.26, 11.1–11.4, 11.7–11.9)

Identifier and length octets, and the contents octets of every primitive encoding. X.691 reuses
several of these: REAL (X.691 15.2 takes the CER/DER contents octets), the object identifier types
(X.691 24–27 take the BER contents octets) and the character strings that are not known-multiplier
(X.691 30.6 takes the octets of X.690 8.23.5).

Where X.690 gives the sender a choice, the definition is a relation that allows every choice
(`…Contents`). Where CER and DER restrict it (clause 11), the restricted relation sits next to it
(`…Canon`). Where there is no choice, the definition is a function.

`Profile` says which of the three rules is in force. CER and DER share clause 11's restrictions, and
differ only in 9.1/10.1 (length forms), 9.2/10.2 (string forms) and 9.3/10.3 (SET order).
-/

namespace Asn1.X690

open Asn1.X680

/-- X.690 8, 9, 10: the basic, canonical and distinguished encoding rules. -/
inductive Profile where
  | ber | cer | der
  deriving DecidableEq, Repr

/-- X.690 11: the restrictions CER and DER share apply. -/
def Profile.restricted : Profile → Bool
  | .ber => false
  | _ => true

/-! ## Identifier octets (8.1.2) -/

/-- X.690 8.1.2.2 a), Table 1: bits 8 and 7 of the leading identifier octet. -/
def _root_.Asn1.X680.TagClass.bits87 : TagClass → Nat
  | .universal => 0
  | .application => 1
  | .context => 2
  | .private_ => 3

/-- X.690 8.1.2.4.2, 8.19.2, 8.20.2: a whole number in base 128, bits 7 to 1 of each octet, bit 8
set in every octet but the last, in the fewest octets (the leading octet is not 80₁₆). The digits
of `n`, least significant first, are found by `go`. -/
def base128 (n : Nat) : Octets :=
  let ds := go n (n + 1)
  (ds.reverse.zipIdx).map fun (d, i) => octet (if i + 1 < ds.length then 128 + d else d)
where
  /-- The base-128 digits of `n`, least significant first; at least one. -/
  go (n : Nat) : Nat → List Nat
    | 0 => [n % 128]
    | k + 1 => if n < 128 then [n] else (n % 128) :: go (n / 128) k

/-- X.690 8.1.2: the identifier octets of a tag, primitive or `constructed` (8.1.2.5).
- 8.1.2.2: one octet for a number up to 30;
- 8.1.2.4: otherwise a leading octet with bits 5 to 1 all ones, then the number in base 128, in the
  fewest octets (8.1.2.4.2 c)). -/
def identOctets (tg : Tag) (constructed : Bool) : Octets :=
  let lead := 64 * tg.cls.bits87 + (if constructed then 32 else 0)
  if tg.num ≤ 30 then [octet (lead + tg.num)]
  else octet (lead + 31) :: base128 tg.num

/-! ## Length octets (8.1.3) -/

/-- X.690 8.1.3: the form of the length octets. -/
inductive LenForm where
  /-- 8.1.3.4 -/
  | short
  /-- 8.1.3.5: an initial octet and `k` subsequent octets -/
  | long (k : Nat)
  /-- 8.1.3.6 -/
  | indefinite
  deriving DecidableEq, Repr

/-- X.690 8.1.3.3–8.1.3.6: the length octets for `n` contents octets in the definite forms (the
indefinite form ignores `n`). -/
def lengthOctets : LenForm → Nat → Octets
  | .short, n => [octet n]
  | .long k, n => octet (128 + k) :: beOctets k n
  | .indefinite, _ => [octet 128]

/-- X.690 8.1.3: a length form can carry `n` contents octets.
- 8.1.3.4: the short form up to 127;
- 8.1.3.5: the long form with one or more subsequent octets that hold `n`; 11111111₂ is not used,
  so at most 126 of them. NOTE 2: more subsequent octets than necessary are the sender's option.
- 8.1.3.6: the indefinite form, for any length. Only a constructed encoding uses it
  (8.1.3.2 a)): `LenForm.Allowed`. -/
def LenForm.Fits : LenForm → Nat → Prop
  | .short, n => n ≤ 127
  | .long k, n => 1 ≤ k ∧ k ≤ 126 ∧ n < 256 ^ k
  | .indefinite, _ => True

/-- The definite form in the fewest length octets (9.1, 10.1): the short form up to 127, else the
long form with the fewest subsequent octets. -/
def minLenForm (n : Nat) : LenForm := if n ≤ 127 then .short else .long (octetsFor n)

/-- X.690 8.1.3.2, 9.1, 10.1: the length forms a profile allows for an encoding of `n` contents
octets that is primitive or `constructed`.
- BER (8.1.3.2): definite if primitive; definite or indefinite, the sender's option, if constructed.

  OPEN (ledger X690-1): 8.1.3.2 c) requires the indefinite form when a constructed encoding "is
  not all immediately available". That is a property of the sender, not of the octets, so it is not
  a rule here: both forms are allowed for a constructed encoding.
- CER (9.1): indefinite if constructed; the fewest length octets if primitive.
- DER (10.1): definite, in the fewest octets.
In every profile the form must be able to carry the length (8.1.3.5 c): at most 126 subsequent
octets). -/
def LenForm.Allowed (p : Profile) (constructed : Bool) (f : LenForm) (n : Nat) : Prop :=
  match p with
  | .ber => f.Fits n ∧ (constructed = false → f ≠ .indefinite)
  | .cer => (if constructed then f = .indefinite else f = minLenForm n) ∧ f.Fits n
  | .der => f = minLenForm n ∧ f.Fits n

instance (f : LenForm) (n : Nat) : Decidable (f.Fits n) := by
  cases f <;> unfold LenForm.Fits <;> infer_instance

instance (p : Profile) (c : Bool) (f : LenForm) (n : Nat) : Decidable (f.Allowed p c n) := by
  cases p <;> unfold LenForm.Allowed <;> infer_instance

/-- X.690 8.1.5: the end-of-contents octets. -/
def eoc : Octets := [octet 0, octet 0]

/-! ## BOOLEAN (8.2, 11.1) -/

/-- X.690 8.2.1, 8.2.2: one contents octet, zero for FALSE and any non-zero value for TRUE, the
sender's option. 11.1: all ones under CER and DER. -/
def BoolContents (p : Profile) (b : Bool) (os : Octets) : Prop :=
  ∃ o : Fin 256, os = [o] ∧
    if b then o ≠ 0 ∧ (p.restricted = true → o = 255) else o = 0

/-! ## INTEGER and ENUMERATED (8.3, 8.4) -/

/-- X.690 8.3: one or more contents octets, a two's complement binary number equal to `i`, and in
the fewest octets (8.3.2: the first nine bits are not all equal). This is `TcMinOctets` of X.691
11.4.6 (ledger X691-2), so the encoding is unique (`intContents`). -/
def IntContents (i : Int) (os : Octets) : Prop := TcMinOctets i (bitsOf os) ∧ os ≠ []

/-- The contents octets of 8.3. -/
def intContents (i : Int) : Octets := bitsToOctets (tcMinFn i)

theorem intContents_spec (i : Int) : IntContents i (intContents i) := by
  have h := tcMinFn_spec i
  refine ⟨?_, ?_⟩
  · rw [intContents, bitsOf_bitsToOctets _ h.1]; exact h
  · intro he
    have := congrArg bitsOf he
    rw [intContents, bitsOf_bitsToOctets _ h.1] at this
    exact absurd this (List.ne_nil_of_length_pos h.2.1)

/-! ## REAL (8.5, 11.3) -/

/-- X.690 8.5.7.4: the exponent field and the format (bits 2 to 1) that announces it.
- a)–c): one, two or three octets, a two's complement number;
- d): an octet with the number of exponent octets X ≥ 1, then X octets, whose first nine bits are
  not all zeros or all ones.

  OPEN (ledger X690-2): as in X.691 11.4.6, "the first nine bits" do not exist when X = 1, and the
  rule then binds nothing. -/
def ExpField (e : Int) (fmt : Nat) (os : Octets) : Prop :=
  match fmt with
  | 0 | 1 | 2 => os.length = fmt + 1 ∧ tcValue (bitsOf os) = e
  | 3 => ∃ x ex, os = octet x :: ex ∧ 1 ≤ x ∧ x ≤ 255 ∧ ex.length = x ∧ tcValue (bitsOf ex) = e ∧
      (x = 1 ∨ ((bitsOf ex).take 9 ≠ List.replicate 9 false ∧ (bitsOf ex).take 9 ≠ List.replicate 9 true))
  | _ => False

/-- X.690 11.3.1: the exponent "in the fewest octets": the fewest two's complement octets, in
format a)–c) when that is three or fewer, and in format d) otherwise. Format d) counts the exponent
octets in one octet, so an exponent of more than 255 octets has no encoding (8.5.7.4 d)). -/
def ExpFieldMin (e : Int) (fmt : Nat) (os : Octets) : Prop :=
  let k := tcOctetsFor e
  if k ≤ 3 then fmt = k - 1 ∧ os = bitsToOctets (tcMinFn e)
  else fmt = 3 ∧ k ≤ 255 ∧ os = octet k :: bitsToOctets (tcMinFn e)

/-- X.690 11.3.1 refines 8.5.7.4: the fewest-octets exponent is an exponent field. -/
theorem expFieldMin_expField {e : Int} {fmt : Nat} {os : Octets} (h : ExpFieldMin e fmt os) :
    ExpField e fmt os := by
  have hs := tcMinFn_spec e
  have h8 : (tcMinFn e).length % 8 = 0 := hs.1
  have hl : (bitsToOctets (tcMinFn e)).length = tcOctetsFor e := by
    rw [bitsToOctets_length h8, tcMinFn_length]; omega
  have hv : tcValue (bitsOf (bitsToOctets (tcMinFn e))) = e := by
    rw [bitsOf_bitsToOctets _ h8]; exact hs.2.2.1
  have hpos := tcOctetsFor_pos e
  simp only [ExpFieldMin] at h
  split at h
  · obtain ⟨rfl, rfl⟩ := h
    have : tcOctetsFor e - 1 = 0 ∨ tcOctetsFor e - 1 = 1 ∨ tcOctetsFor e - 1 = 2 := by omega
    rcases this with h0 | h0 | h0 <;> rw [h0] <;> exact ⟨by omega, hv⟩
  · obtain ⟨rfl, hk, rfl⟩ := h
    refine ⟨tcOctetsFor e, bitsToOctets (tcMinFn e), rfl, by omega, hk, hl, hv, Or.inr ?_⟩
    rw [bitsOf_bitsToOctets _ h8]
    rcases hs.2.2.2 with h | h
    · rw [tcMinFn_length] at h; omega
    · exact h

instance (e : Int) (fmt : Nat) (os : Octets) : Decidable (ExpFieldMin e fmt os) := by
  unfold ExpFieldMin; infer_instance

/-- X.690 8.5.7.2: the base B' that bits 6 to 5 encode. -/
def realBase : Nat → Nat
  | 0 => 2
  | 1 => 8
  | _ => 16

/-- X.690 8.5.6 a), 8.5.7: the binary encoding of the non-zero number `q`. The sender chooses the
base B' (2, 8 or 16, 8.5.4), the sign S, the integer N > 0, the scaling factor F (0 to 3) and the
exponent E with `q = S × N × 2^F × B'^E`, and the exponent's format. N fills the remaining octets as
an unsigned binary number (8.5.7.5); NOTE 1: BER does not require it to be normalized.

11.3.1, under CER and DER: base 2, F = 0, M (that is, N) odd, and N and E in the fewest octets. -/
def RealBinary (p : Profile) (q : ℚ) (os : Octets) : Prop :=
  ∃ (neg : Bool) (bb : Nat) (f : Nat) (e : Int) (nn : Nat) (fmt : Nat) (ef nf : Octets),
    bb < 3 ∧ f < 4 ∧ 0 < nn ∧
    q = (if neg then -1 else 1) * (nn : ℚ) * 2 ^ f * (realBase bb : ℚ) ^ e ∧
    -- 8.5.6 a), 8.5.7.1–8.5.7.4: the first contents octet
    os = octet (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) :: ef ++ nf ∧
    nf ≠ [] ∧ nnbValue (bitsOf nf) = nn ∧
    (if p.restricted then bb = 0 ∧ f = 0 ∧ nn % 2 = 1 ∧ nf = bitsToOctets (nnbMinFn nn) ∧
        ExpFieldMin e fmt ef
     else ExpField e fmt ef)

/-! ### The decimal encoding (8.5.8, 11.3.2)

ISO 6093 is not available here. The three number representations are read from what X.690 and
ISO 6093's well-known definitions say of them:
- NR1: an optionally signed integer, `[+|-]digits`;
- NR2: an optionally signed number with a decimal mark (`.` or `,`) and at least one digit;
- NR3: an NR2 significand, then `E` or `e`, then an optionally signed integer exponent.
Leading spaces are allowed in each (8.5.8 NOTE 2 and 11.3.2.2 imply that SPACE can occur).

OPEN (ledger X690-3): the grammar is reconstructed, not transcribed from ISO 6093. -/

def isDig (c : Char) : Bool := c.isDigit
def digVal (cs : List Char) : Nat := cs.foldl (fun a c => 10 * a + (c.toNat - '0'.toNat)) 0

/-- An optional sign: `true` for minus. -/
def readSign : List Char → Bool × List Char
  | '+' :: r => (false, r)
  | '-' :: r => (true, r)
  | r => (false, r)

/-- `[digits][mark][digits]` with at least one digit, and a mark if `needMark`: the value. -/
def readSignificand (needMark : Bool) (s : List Char) : Option (ℚ × List Char) :=
  let a := s.takeWhile isDig
  let r := s.drop a.length
  match r with
  | c :: r' =>
    if c = '.' ∨ c = ',' then
      let b := r'.takeWhile isDig
      if a.length + b.length = 0 then none
      else some ((digVal a : ℚ) + (digVal b : ℚ) / 10 ^ b.length, r'.drop b.length)
    else if needMark ∨ a = [] then none else some (digVal a, r)
  | [] => if needMark ∨ a = [] then none else some (digVal a, [])

/-- X.690 8.5.8: the value of an ISO 6093 field in number representation NR`form`. -/
def nrValue (form : Nat) (s : List Char) : Option ℚ :=
  let s := s.dropWhile (· = ' ')
  let (neg, s) := readSign s
  let sgn : ℚ := if neg then -1 else 1
  match form with
  | 1 => let d := s.takeWhile isDig
    if d ≠ [] ∧ d.length = s.length then some (sgn * digVal d) else none
  | 2 => match readSignificand true s with
    | some (q, []) => some (sgn * q)
    | _ => none
  | 3 => match readSignificand true s with
    | some (q, c :: r) =>
      if c = 'E' ∨ c = 'e' then
        let (eneg, r) := readSign r
        if r ≠ [] ∧ r.all isDig then
          let e : Int := if eneg then -(digVal r : Int) else digVal r
          some (sgn * q * (10 : ℚ) ^ e)
        else none
      else none
    | _ => none
  | _ => none

/-- X.690 11.3.2: the NR3 form CER and DER use, for a non-zero number: an optional MINUS SIGN, the
mantissa digits (neither the first nor the last a 0, 11.3.2.4), FULL STOP, "E", and the exponent,
"+0" for zero and otherwise without a leading zero or PLUS SIGN (11.3.2.6). -/
def Nr3Canon (q : ℚ) (s : List Char) : Prop :=
  ∃ (neg : Bool) (m : Nat) (e : Int), 0 < m ∧ m % 10 ≠ 0 ∧
    q = (if neg then -1 else 1) * (m : ℚ) * (10 : ℚ) ^ e ∧
    s = (if neg then ['-'] else []) ++ (Nat.toDigits 10 m) ++ ['.', 'E'] ++
      (if e = 0 then ['+', '0'] else if e < 0 then '-' :: Nat.toDigits 10 e.natAbs
       else Nat.toDigits 10 e.natAbs)

/-- X.690 8.5.6 b), 8.5.8: the decimal encoding of `q`: the first octet gives the number
representation in bits 6 to 1, and the rest is an ISO 6093 field whose length the sender chooses.
11.3.2: CER and DER use NR3 in the form `Nr3Canon`. -/
def RealDecimal (p : Profile) (q : ℚ) (os : Octets) : Prop :=
  ∃ form s, os = octet form :: s.map (fun c => octet c.toNat) ∧ (∀ c ∈ s, c.toNat < 128) ∧
    1 ≤ form ∧ form ≤ 3 ∧ nrValue form s = some q ∧
    (p.restricted = true → form = 3 ∧ Nr3Canon q s)

/-- X.690 8.5: the contents octets of a real value.
- 8.5.2: none for plus zero;
- 8.5.3, 8.5.9: one octet for minus zero and the special values;
- 8.5.4, 8.5.5: a base 2 value in the binary encoding, a base 10 value in the decimal one. -/
def RealContents (p : Profile) : RealVal → Octets → Prop
  | .plusZero, os => os = []
  | .plusInfinity, os => os = [octet 0x40]
  | .minusInfinity, os => os = [octet 0x41]
  | .notANumber, os => os = [octet 0x42]
  | .minusZero, os => os = [octet 0x43]
  | .num .two q, os => RealBinary p q os
  | .num .ten q, os => RealDecimal p q os

/-! ## BIT STRING (8.6.2, 11.2) -/

/-- X.690 8.6.2: the contents octets of a primitive encoding of the bits `bs`: an initial octet with
the number of unused bits in the final octet (0 to 7), then the bits, leading bit first, filling
the octets. 8.6.2.3: an empty bit string is the single octet 0. The unused bits are anything in BER;
11.2.1: zero in CER and DER. -/
def BitsPrim (p : Profile) (bs : Bits) (os : Octets) : Prop :=
  ∃ (u : Nat) (pad : Bits), u ≤ 7 ∧ pad.length = u ∧ (bs.length + u) % 8 = 0 ∧
    (bs = [] → u = 0) ∧
    os = octet u :: bitsToOctets (bs ++ pad) ∧
    (p.restricted = true → pad = List.replicate u false)

/-! ## Object identifiers (8.19–8.22) -/

/-- X.690 8.19.2–8.19.5: the subidentifiers of an object identifier value with at least two arcs:
`40 X + Y`, then the arcs after the second, each in base 128. -/
def oidContents : List Nat → Octets
  | x :: y :: rest => base128 (40 * x + y) ++ rest.flatMap base128
  | _ => []

/-- X.690 8.20.2–8.20.4: one sub-identifier per arc. -/
def relOidContents (arcs : List Nat) : Octets := arcs.flatMap base128

/-- ISO/IEC 10646 Annex D: UTF-8, each character in the fewest octets (X.690 8.21.2, 8.23.10). -/
def utf8 (c : Nat) : Octets :=
  if c < 0x80 then [octet c]
  else if c < 0x800 then [octet (0xC0 + c / 64), octet (0x80 + c % 64)]
  else if c < 0x10000 then
    [octet (0xE0 + c / 4096), octet (0x80 + c / 64 % 64), octet (0x80 + c % 64)]
  else [octet (0xF0 + c / 262144), octet (0x80 + c / 4096 % 64), octet (0x80 + c / 64 % 64),
        octet (0x80 + c % 64)]

def utf8String (cs : List Nat) : Octets := cs.flatMap utf8

/-- X.690 8.21.2: the UTF-8 encoding of the XML value notation of an OID-IRI, `/label/label…`
(X.680 34.3), with no white space. -/
def iriContents (arcs : List String) : Octets :=
  utf8String ((arcs.map fun a => '/' :: a.toList).flatten.map Char.toNat)

/-- X.690 8.22.2: the same for a relative OID-IRI, `label/label…` (X.680 35.3). -/
def relIriContents (arcs : List String) : Octets :=
  utf8String (("/".intercalate arcs).toList.map Char.toNat)

/-! ## Restricted character strings (8.23, 11.4) -/

/-- X.690 8.23.8: two octets per character, the 2-octet BMP form. -/
def bmpOctets (cs : List Nat) : Octets := cs.flatMap fun c => beOctets 2 c

/-- X.690 8.23.7: four octets per character, the 4-octet canonical form. -/
def universalOctets (cs : List Nat) : Octets := cs.flatMap fun c => beOctets 4 c

/-- X.690 8.23.3–8.23.10: the value of the octet string a character string value is encoded as.
- NumericString, PrintableString, VisibleString and IA5String: G0 is registration 6 (and C0 is
  registration 1 for IA5String), assumed and invoked at the start, with no escape sequences allowed
  (Table 3). Each character is then its 7-bit code, which is its ISO/IEC 10646 code point (both
  registrations are the first 128 cells of ISO/IEC 10646).
- UniversalString, BMPString, UTF8String: 8.23.7, 8.23.8, 8.23.10.
- TeletexString, VideotexString, GraphicString, GeneralString: ISO/IEC 2022 with the escape
  sequences the type allows (`Iso2022Enc`); 11.4 restricts them under CER and DER. -/
def StringOctets (p : Profile) (k : StrType) : Val → Octets → Prop
  | .chars cs, os => match k with
    | .numeric | .printable | .visible | .ia5 => os = cs.map octet ∧ ∀ c ∈ cs, c < 128
    | .universal => os = universalOctets cs
    | .bmp => os = bmpOctets cs
    | .utf8 => os = utf8String cs
    | _ => False
  | .regChars cs, os => k.isRegister = true ∧ Iso2022Enc p.restricted k cs os
  | _, _ => False

/-! ## Time types (8.25, 8.26, 11.7–11.9) -/

/-- X.690 11.7: the forms of GeneralizedTime that CER and DER encode: terminated by "Z" (11.7.1),
with seconds (11.7.2), a fraction only if it is not zero and without trailing zeros (11.7.3), with
"." as the decimal point (11.7.4), and midnight as 000000 (11.7.5, which the format of X.680 46.3
already requires: hour 24 is not a GeneralizedTime). The value is the string itself (X.680 46.1),
so a string in another form has no CER or DER encoding.

OPEN (ledger X690-4): X.680 46 makes the values of GeneralizedTime strings, so a value not in this
form is not converted to one that is (which could change the day, for a local time or a time
difference). It has no CER or DER encoding. -/
def GenTimeCanon (s : List Char) : Prop :=
  s.getLast? = some 'Z' ∧
  ∃ (ymdhms : List Char) (fr : List Char),
    s = ymdhms ++ (if fr = [] then [] else '.' :: fr) ++ ['Z'] ∧
    ymdhms.length = 14 ∧ ymdhms.all isDig ∧ fr.all isDig ∧ fr.getLast? ≠ some '0'

/-- X.690 11.8: the forms of UTCTime that CER and DER encode: "YYMMDDhhmmssZ" (11.8.1, 11.8.2).
The same reading as `GenTimeCanon` (ledger X690-4). -/
def UtcTimeCanon (s : List Char) : Prop :=
  s.length = 13 ∧ s.getLast? = some 'Z' ∧ (s.take 12).all isDig

namespace TimePrint

/-- `n` in decimal, with at least `w` digits. -/
def pad (w n : Nat) : List Char :=
  let ds := Nat.toDigits 10 n
  List.replicate (w - ds.length) '0' ++ ds

/-- Table 7, "Year component" (as `Notation.yearOrCentury` reads it). -/
def year (y : Int) : List Char :=
  if 0 ≤ y ∧ y ≤ 9999 then pad 4 y.toNat
  else if y > 9999 then '+' :: Nat.toDigits 10 y.toNat
  else '-' :: pad 4 y.natAbs

def century (c : Int) : List Char :=
  (if 0 ≤ c ∧ c ≤ 99 then pad 2 c.toNat
   else if c > 99 then '+' :: Nat.toDigits 10 c.toNat
   else '-' :: pad 2 c.natAbs) ++ ['C']

def date : DateV → List Char
  | .c c => century c
  | .y y => year y
  | .ym y m => year y ++ '-' :: pad 2 m
  | .ymd y m d => year y ++ '-' :: pad 2 m ++ '-' :: pad 2 d
  | .yd y d => year y ++ '-' :: pad 3 d
  | .yw y w => year y ++ '-' :: 'W' :: pad 2 w
  | .ywd y w d => year y ++ '-' :: 'W' :: pad 2 w ++ '-' :: pad 1 d

/-- 11.9.1 a): a full stop as the decimal sign. -/
def frac (ds : Digits) : List Char :=
  if ds = [] then [] else '.' :: ds.map fun d => Char.ofNat ('0'.toNat + d.val)

/-- 11.9.1 b): the minutes of a time difference that is a whole number of hours are removed. -/
def zone : Zone → List Char
  | .local_ => []
  | .utc => ['Z']
  | .diff m =>
    (if m < 0 then '-' else '+') :: pad 2 (m.natAbs / 60) ++
      (if m.natAbs % 60 = 0 then [] else ':' :: pad 2 (m.natAbs % 60))

def timeOfDay (t : TimeOfDayV) : List Char :=
  pad 2 t.hour ++ (match t.minute with
    | some m => ':' :: pad 2 m ++ (match t.second with
      | some s => ':' :: pad 2 s
      | none => [])
    | none => []) ++ frac t.frac ++ zone t.zone

def point : PointV → List Char
  | .date d => date d
  | .time t => timeOfDay t
  | .dateTime d t => date d ++ 'T' :: timeOfDay t

def duration (d : DurationV) : List Char :=
  let el (o : Option Nat) (c : Char) (last : Bool) : List Char := match o with
    | some v => Nat.toDigits 10 v ++ (if last then frac d.frac else []) ++ [c]
    | none => []
  let lastIdx := d.elems.length - 1 - (d.elems.reverse.findIdx Option.isSome)
  let es := d.elems.zipIdx
  let get (i : Nat) (c : Char) := el (es[i]?.bind (·.1)) c (i = lastIdx)
  let datePart := get 0 'Y' ++ get 1 'M' ++ get 2 'W' ++ get 3 'D'
  let timePart := get 4 'H' ++ get 5 'M' ++ get 6 'S'
  'P' :: datePart ++ (if timePart = [] then [] else 'T' :: timePart)

/-- The zone a point carries, if it has a time of day. -/
def pointZone : PointV → Option Zone
  | .time t | .dateTime _ t => some t.zone
  | .date _ => none

/-- 11.9.1 c): an end point's time difference is removed when it is the start point's. -/
def dropZone : PointV → PointV
  | .time t => .time { t with zone := .local_ }
  | .dateTime d t => .dateTime d { t with zone := .local_ }
  | p => p

def interval : IntervalV → List Char
  | .se a b =>
    let b' := match pointZone a, pointZone b with
      | some (.diff m), some (.diff m') => if m = m' then dropZone b else b
      | _, _ => b
    point a ++ '/' :: point b'
  -- 11.9.1 d): zero time components removed but the least significant (`DurationV.norm`)
  | .d du => duration du.norm
  | .sd a du => point a ++ '/' :: duration du.norm
  | .de du b => duration du.norm ++ '/' :: point b

/-- The value notation of a TIME value (without its QUOTATION MARKs), in the canonical form of
X.690 11.9.1.

OPEN (ledger X690-5): 11.9 transforms "the value notation", so every notation of a value should
give one result. The notation fixes things 11.9 does not mention (the digits of a recurrence count
may have leading zeros: "R05" and "R5" are one value). We print the count without leading zeros. -/
def time : TimeV → List Char
  | .point p => point p
  | .interval i => interval i
  | .recurring n i => 'R' :: (match n with | some k => Nat.toDigits 10 k | none => []) ++
      '/' :: interval i

end TimePrint

/-- The time types of X.690 8.26, which differ only in what is removed from the notation. -/
inductive TimeKind where
  | time | date | timeOfDay | dateTime | duration
  deriving DecidableEq, Repr

/-- X.690 8.26.1.2–8.26.5.2: the characters removed from the value notation. -/
def TimeKind.strip : TimeKind → List Char → List Char
  | .time, s => s
  | .date, s => s.filter (· ≠ '-')
  | .timeOfDay, s => s.filter (· ≠ ':')
  | .dateTime, s => s.filter fun c => c ≠ '-' ∧ c ≠ ':' ∧ c ≠ 'T'
  | .duration, s => s.filter (· ≠ 'P')

/-- X.690 8.26: the contents octets are the UTF-8 encoding of a value notation of `v`, with the
characters of its kind removed. BER takes any notation (X.680 38.3.2: `TimeV.Notates`); CER and DER
the canonical form of 11.9 (11.9.2). -/
def TimeContents (p : Profile) (k : TimeKind) (v : TimeV) (os : Octets) : Prop :=
  if p.restricted then os = utf8String ((k.strip (TimePrint.time v.norm)).map Char.toNat)
  else ∃ s, v.Notates s ∧ os = utf8String ((k.strip s).map Char.toNat)

end Asn1.X690
