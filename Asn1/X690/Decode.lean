import Asn1.X690.Ber
import Asn1.X680.Checker

/-!
# Decoding BER, CER and DER, as the relation `ber` reads

An executable decoder written to follow `ber` case by case, so that the relation can be run on real
encodings (`asn1check decode`).

1. `parseNode` reads octets into a `Node` (X.690 8.1): the identifier, length and end-of-contents
   octets fix the tree, and `parseNode_octets` (`DecodeSound.lean`) proves that the tree lays out
   to exactly the octets read. `dec_sound` (`DecSound.lean`) proves that what `dec` returns, `ber`
   relates to the node, and `decode_sound` puts the two together; `dec_complete` and
   `decode_complete` (`DecComplete.lean`) prove the converse for `Decodable` values.
2. `dec` reads a `Node` against a type, one case per case of `ber`. Where `ber` allows a choice,
   the node says which was taken. Where a clause has a function (OBJECT IDENTIFIER contents, the
   canonical TIME notation, UTF-8), the decoder re-encodes what it read and compares.
3. An open type (X.690 8.15) is a value of *some* type; `ber` allows any. The decoder finds the type
   from the table constraint on the component (X.682 10), as an application would, or else from the
   tags of the encoding (`nodeTy`), as for a table with no row for the key. Which type is picked
   cannot make the result wrong, only fail.
4. Where proving that a check implies the relation would mean reasoning about a parser, the decoder
   instead reads the sender's choices and checks the relation's own equation with them: the NR3
   form (`nr3CanonB`), the TIME notation's UTF-8, an enumeration's number. Under CER and DER an
   encoded DEFAULT component must be shown *not* to be its default (`notDefaultB`), so for a
   default that is not a simple value the decoder rejects rather than guess.
5. Beyond `ber`, the decoder checks part of the value set (`Has`), as `X690.rule` requires: a
   contents constraint's octets decode as the contained type (X.682 11.4), and the value passes
   `valSemB` (ranges, sizes, alphabets, time formats), whose rejections are sound.

Errors say which clause the octets break.
-/

namespace Asn1.X690

open Asn1.X680

/-! ## The octets of an encoding (8.1) -/

/-- The digits of a base-128 field, least significant first. -/
def base128Digits : Nat → List (Fin 256) → Option (List Nat × List (Fin 256))
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, o :: rest =>
    if o.val < 128 then some ([o.val], rest)
    else (base128Digits k rest).map fun (ds, r) => (ds ++ [o.val - 128], r)

/-- X.690 8.1.2.4.2, 8.19.2: a whole number in base 128, in the fewest octets. The number is read,
then written again with `base128` and compared, so the octets are exactly `base128` of it. -/
def readSubId (os : List (Fin 256)) : Option (Nat × List (Fin 256)) :=
  match base128Digits os.length os with
  | some (ds, r) =>
    let v := ds.foldr (fun d acc => acc * 128 + d) 0
    if base128 v ++ r = os then some (v, r) else none
  | none => none

def TagClass.ofBits : Nat → TagClass
  | 0 => .universal
  | 1 => .application
  | 2 => .context
  | _ => .private_

/-- The tag and form the identifier octets at the front of `os` would give, before the check. -/
def identCandidate : List (Fin 256) → Option (Tag × Bool × List (Fin 256))
  | [] => none
  | o :: rest =>
    if o.val % 32 < 31 then some (⟨TagClass.ofBits (o.val / 64), o.val % 32⟩, o.val / 32 % 2 == 1, rest)
    else (readSubId rest).map fun (v, r) => (⟨TagClass.ofBits (o.val / 64), v⟩, o.val / 32 % 2 == 1, r)

/-- X.690 8.1.2: the tag and form of the identifier octets at the front of `os`, and the rest. A
number up to 30 has only the one-octet form (8.1.2.2), and a larger one the fewest octets
(8.1.2.4.2 c)): what is read is re-encoded with `identOctets` and compared. -/
def readIdent (os : List (Fin 256)) : Option (Tag × Bool × List (Fin 256)) :=
  (identCandidate os).bind fun (t, c, r) => if identOctets t c ++ r = os then some (t, c, r) else none

/-- A big-endian unsigned number. -/
def beValue (os : List (Fin 256)) : Nat := os.foldl (fun a o => 256 * a + o.val) 0

/-- The length form and length the length octets at the front of `os` would give. -/
def lenCandidate : List (Fin 256) → Option (LenForm × Option Nat × List (Fin 256))
  | [] => none
  | o :: rest =>
    if o.val < 128 then some (.short, some o.val, rest)
    else if o.val = 128 then some (.indefinite, none, rest)
    else some (.long (o.val - 128), some (beValue (rest.take (o.val - 128))), rest.drop (o.val - 128))

/-- The length octets of a form and a length (`none` for the indefinite form). -/
def lenOcts : LenForm → Option Nat → Octets
  | .indefinite, _ => [octet 128]
  | f, some n => lengthOctets f n
  | _, none => []

/-- X.690 8.1.3: the length form, the length (none for the indefinite form) and the rest. What is
read is re-encoded and compared, so the long form has as many octets as it says, 11111111₂ is not
used (8.1.3.5 c)), and a length is given exactly when the form is definite. -/
def readLen (os : List (Fin 256)) : Option (LenForm × Option Nat × List (Fin 256)) :=
  (lenCandidate os).bind fun (f, l, r) =>
    if lenOcts f l ++ r = os ∧ (f = .indefinite ↔ l = none) ∧ f.Fits (l.getD 0) then some (f, l, r)
    else none

mutual
  /-- X.690 8.1.1–8.1.5: one encoding at the front of `os`, and the rest. A primitive encoding has
  the definite form (8.1.3.2 a)). A constructed one holds encodings up to its length, or, in the
  indefinite form, up to the end-of-contents octets (8.1.5). -/
  def parseNode : Nat → List (Fin 256) → Option (Node × List (Fin 256))
    | 0, _ => none
    | f + 1, os =>
      match readIdent os with
      | none => none
      | some (tg, cons, r1) =>
        match readLen r1 with
        | none => none
        | some (form, len, r2) =>
          match cons, len with
          | false, some l => if l ≤ r2.length then some (.prim tg form (r2.take l), r2.drop l) else none
          | false, none => none
          | true, some l =>
            if l ≤ r2.length then (parseAll f (r2.take l)).map fun ch => (.cons tg form ch, r2.drop l)
            else none
          | true, none => (parseUntilEoc f r2).map fun (ch, r) => (.cons tg form ch, r)

  /-- The encodings that make up all of `os`. -/
  def parseAll : Nat → List (Fin 256) → Option (List Node)
    | _, [] => some []
    | 0, _ :: _ => none
    | f + 1, os@(_ :: _) =>
      match parseNode f os with
      | some (nd, r) => (parseAll f r).map (nd :: ·)
      | none => none

  /-- The encodings up to the end-of-contents octets, and what follows them. -/
  def parseUntilEoc : Nat → List (Fin 256) → Option (List Node × List (Fin 256))
    | 0, _ => none
    | f + 1, os =>
      match os with
      | a :: b :: r => if a.val = 0 ∧ b.val = 0 then some ([], r) else
        match parseNode f os with
        | some (nd, r') => (parseUntilEoc f r').map fun (ch, r'') => (nd :: ch, r'')
        | none => none
      | _ => none
end

mutual
  /-- `Node.LenOk`, decided. -/
  def lenOkB (p : Profile) : Node → Bool
    | .prim _ f cs => decide (f.Allowed p false cs.length)
    | .cons _ f ch => decide (f.Allowed p true (Node.octetsList ch).length) && lenOkListB p ch
  def lenOkListB (p : Profile) : List Node → Bool
    | [] => true
    | nd :: rest => lenOkB p nd && lenOkListB p rest
end

/-! ## Contents octets, decided -/

/-- X.690 8.3.2: the leading nine bits are not all equal, or there are only eight. -/
def intContentsB (cs : Octets) : Bool :=
  !cs.isEmpty && (cs.length == 1 ||
    let b := (bitsOf cs).take 9
    b != List.replicate 9 false && b != List.replicate 9 true)

/-- `ExpField`, decided. -/
def expFieldB (e : Int) (fmt : Nat) (os : Octets) : Bool :=
  match fmt with
  | 0 | 1 | 2 => os.length == fmt + 1 && tcValue (bitsOf os) == e
  | 3 => match os with
    | x :: ex => 1 ≤ x.val && ex.length == x.val && tcValue (bitsOf ex) == e &&
      (x.val == 1 || ((bitsOf ex).take 9 != List.replicate 9 false &&
        (bitsOf ex).take 9 != List.replicate 9 true))
    | [] => false
  | _ => false

/-- The NR3 notation of `Nr3Canon`, for the sign, mantissa and exponent. -/
def nr3Print (neg : Bool) (m : Nat) (e : Int) : List Char :=
  (if neg then ['-'] else []) ++ Nat.toDigits 10 m ++ ['.', 'E'] ++
    (if e = 0 then ['+', '0'] else if e < 0 then '-' :: Nat.toDigits 10 e.natAbs
     else Nat.toDigits 10 e.natAbs)

/-- The exponent of an NR3 notation after "E": an optional sign, then digits. -/
def nr3Exp (ex : List Char) : Int :=
  let eneg := ex.head? == some '-'
  let ed := if eneg || ex.head? == some '+' then ex.drop 1 else ex
  if eneg then -(digVal ed : Int) else digVal ed

/-- X.690 11.3.2: `Nr3Canon q s`, decided: the sign, mantissa and exponent are read from `s`, and
`s` must be their NR3 notation (`nr3Print`) with the value `q`. -/
def nr3CanonB (q : ℚ) (s : List Char) : Bool :=
  let neg := s.head? == some '-'
  let r := if neg then s.drop 1 else s
  let md := r.takeWhile isDig
  let m := digVal md
  let e := nr3Exp ((r.drop md.length).drop 2)
  0 < m && m % 10 != 0 && decide (q = (if neg then -1 else 1) * (m : ℚ) * (10 : ℚ) ^ e) &&
    s == nr3Print neg m e

/-- X.690 8.5.7.4: the exponent octets and the N octets after the first contents octet, by the
format in bits 2 to 1. -/
def realSplit (fmt : Nat) (rest : Octets) : Octets × Octets :=
  match fmt, rest with
  | 3, x :: r => (x :: r.take x.val, r.drop x.val)
  | 3, [] => ([], [])
  | k, _ => (rest.take (k + 1), rest.drop (k + 1))

/-- The octets of the exponent's value: after the count octet in format d). -/
def realExpOctets (fmt : Nat) (ef : Octets) : Octets := if fmt = 3 then ef.drop 1 else ef

/-- X.690 8.5: the real value of the contents octets. -/
def decReal (p : Profile) (cs : Octets) : Except String RealVal :=
  match cs with
  | [] => .ok .plusZero
  | o :: rest =>
    if o.val / 128 = 1 then
      -- 8.5.7: binary
      let neg := o.val / 64 % 2 == 1
      let bb := o.val / 16 % 4
      let f := o.val / 4 % 4
      let fmt := o.val % 4
      if bb = 3 then .error "8.5.7.2: reserved base" else
      let ef := (realSplit fmt rest).1
      let nf := (realSplit fmt rest).2
      let e := tcValue (bitsOf (realExpOctets fmt ef))
      let nn := nnbValue (bitsOf nf)
      let q : ℚ := (if neg then -1 else 1) * (nn : ℚ) * 2 ^ f * (realBase bb : ℚ) ^ e
      if nf.isEmpty || nn = 0 then .error "8.5.7.5: N must be a positive integer"
      else if !expFieldB e fmt ef then .error "8.5.7.4: exponent field"
      else if p.restricted && !(bb == 0 && f == 0 && nn % 2 == 1 && nf == bitsToOctets (nnbMinFn nn) &&
          decide (ExpFieldMin e fmt ef)) then .error "11.3.1: REAL not normalized"
      else .ok (.num .two q)
    else if o.val / 64 = 1 then
      -- 8.5.9
      if !rest.isEmpty then .error "8.5.9: one contents octet" else
      match o.val with
      | 0x40 => .ok .plusInfinity
      | 0x41 => .ok .minusInfinity
      | 0x42 => .ok .notANumber
      | 0x43 => .ok .minusZero
      | _ => .error "8.5.9: reserved special value"
    else
      -- 8.5.8: decimal
      let form := o.val % 64
      let s := rest.map fun c => Char.ofNat c.val
      if !(rest.all (·.val < 128)) || form < 1 || form > 3 then .error "8.5.8: number representation"
      else match nrValue form s with
        | some q =>
          if q = 0 then .error "8.5.2: zero has no contents octets"
          else if p.restricted && !(form == 3 && nr3CanonB q s) then .error "11.3.2: NR3 form"
          else .ok (.num .ten q)
        | none => .error "8.5.8: not an ISO 6093 number"

/-- X.690 8.6.2: the bits of a primitive bit string encoding. -/
def decBitsPrim (p : Profile) (cs : Octets) : Except String Bits :=
  match cs with
  | [] => .error "8.6.2: no initial octet"
  | u :: rest =>
    if u.val > 7 then .error "8.6.2.2: unused bits above 7"
    else if rest.isEmpty && u.val ≠ 0 then .error "8.6.2.3: empty bit string with unused bits"
    else
      let all := bitsOf rest
      let bs := all.take (all.length - u.val)
      let pad := all.drop (all.length - u.val)
      if p.restricted && pad != List.replicate u.val false then .error "11.2.1: unused bits not zero"
      else .ok bs

/-- `octLe`, decided. -/
def octLeB : Octets → Octets → Bool
  | [], _ => true
  | a :: as, [] => a.val == 0 && octLeB as []
  | a :: as, b :: bs => a.val < b.val || (a == b && octLeB as bs)

/-- Each element is related by `r` to the next. -/
def sortedB {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: rest => r a b && sortedB r (b :: rest)
  | _ => true

/-- X.690 8.7, 9.2, 10.2: the octets of an octet string encoding with tag `tg`. -/
def decOctets (p : Profile) : Nat → Tag → Node → Except String Octets
  | 0, _, _ => .error "fuel"
  | n + 1, tg, .prim tg' _ cs =>
    if tg' != tg then .error s!"8.7: tag {repr tg'} where {repr tg} belongs"
    else if p = .cer && cs.length > 1000 then .error "9.2: CER string over 1000 octets not segmented"
    else .ok cs
  | n + 1, tg, .cons tg' _ ch =>
    if tg' != tg then .error s!"8.7: tag {repr tg'} where {repr tg} belongs"
    else if p = .der then .error "10.2: DER string constructed"
    else do
      let segs ← ch.mapM (decOctets p n (univ 4))
      let os := segs.flatten
      if p = .cer && !(1000 < os.length && cerFragmentsB ch) then .error "9.2: CER fragments"
      else .ok os
where
  cerFragmentsB (ch : List Node) : Bool :=
    ch.all (!·.isConstructed) &&
    (ch.dropLast.all fun nd => nd.contentsLength == 1000) &&
    (match ch.getLast? with
     | some nd => 1 ≤ nd.contentsLength && nd.contentsLength ≤ 1000
     | none => false)

/-- X.690 8.6, 9.2, 10.2: the bits of a bit string encoding with tag `tg`; `isLast` as in
`bitsEnc`. -/
def decBits (p : Profile) : Nat → Bool → Tag → Node → Except String Bits
  | 0, _, _, _ => .error "fuel"
  | n + 1, isLast, tg, .prim tg' _ cs =>
    if tg' != tg then .error s!"8.6: tag {repr tg'} where {repr tg} belongs"
    else if p = .cer && cs.length > 1000 then .error "9.2: CER string over 1000 octets not segmented"
    else do
      let bs ← decBitsPrim p cs
      if !isLast && bs.length % 8 != 0 then .error "8.6.4: a segment before the last is not whole octets"
      else .ok bs
  | n + 1, isLast, tg, .cons tg' _ ch =>
    if tg' != tg then .error s!"8.6: tag {repr tg'} where {repr tg} belongs"
    else if p = .der then .error "10.2: DER string constructed"
    else do
      let segs ← (ch.zipIdx).mapM fun (c, i) => decBits p n (isLast && i + 1 == ch.length) (univ 3) c
      let bs := segs.flatten
      if p = .cer && !(1000 < (bs.length + 7) / 8 + 1 && decOctets.cerFragmentsB ch) then
        .error "9.2: CER fragments"
      else .ok bs

/-- UTF-8 (ISO/IEC 10646 Annex D): the characters, if the octets are exactly `utf8String` of them. -/
def decUtf8 (os : Octets) : Option (List Nat) :=
  let rec go : Nat → List Nat → Option (List Nat)
    | 0, _ => none
    | _, [] => some []
    | k + 1, b :: r =>
      if b < 0x80 then (go k r).map (b :: ·)
      else if b < 0xE0 then match r with
        | c :: r' => (go k r').map (fun xs => ((b % 32) * 64 + c % 64) :: xs)
        | [] => none
      else if b < 0xF0 then match r with
        | c :: d :: r' => (go k r').map (fun xs => ((b % 16) * 4096 + (c % 64) * 64 + d % 64) :: xs)
        | _ => none
      else match r with
        | c :: d :: e :: r' => (go k r').map (fun xs => ((b % 8) * 262144 + (c % 64) * 4096 + (d % 64) * 64 + e % 64) :: xs)
        | _ => none
  match go (os.length + 1) (os.map (·.val)) with
  | some cs => if utf8String cs = os then some cs else none
  | none => none

/-- Fixed-width big-endian characters (BMPString, UniversalString). -/
def decWide (w : Nat) (os : Octets) : Option (List Nat) :=
  if os.length % w != 0 then none else
  let cs := (List.range (os.length / w)).map fun i => beValue ((os.drop (w * i)).take w)
  if cs.flatMap (fun c => beOctets w c) = os then some cs else none

/-- X.690 8.23: the value of a character string type from its octets (`StringOctets`). -/
def decString (p : Profile) (k : StrType) (os : Octets) : Except String Val :=
  match k with
  | .numeric | .printable | .visible | .ia5 =>
    if os.all (·.val < 128) then .ok (.chars (os.map (·.val))) else .error "8.23.5: octet above 7F"
  | .universal => match decWide 4 os with
    | some cs => .ok (.chars cs) | none => .error "8.23.7: not 4-octet characters"
  | .bmp => match decWide 2 os with
    | some cs => .ok (.chars cs) | none => .error "8.23.8: not 2-octet characters"
  | .utf8 => match decUtf8 os with
    | some cs => .ok (.chars cs) | none => .error "8.23.10: not shortest-form UTF-8"
  | _ => match iso2022Decode k p.restricted (os.length + 1) (assumed k) none (os.map (·.val)) with
    | some cs => .ok (.regChars cs)
    | none => .error "8.23.5: not ISO/IEC 2022 the type allows"

/-- X.690 8.19: the arcs of an object identifier's contents octets. -/
def decOidArcs (rel : Bool) (cs : Octets) : Option (List Nat) :=
  let rec go : Nat → List (Fin 256) → Option (List Nat)
    | _, [] => some []
    | 0, _ => none
    | k + 1, os => match readSubId os with
      | some (v, r) => (go k r).map (v :: ·)
      | none => none
  match go (cs.length + 1) cs with
  | some ids =>
    if rel then (if relOidContents ids = cs then some ids else none)
    else match ids with
      | s :: rest =>
        let arcs := (if s < 40 then [0, s] else if s < 80 then [1, s - 40] else [2, s - 80]) ++ rest
        if oidContents arcs = cs then some arcs else none
      | [] => none
  | none => none

/-- X.690 8.21, 8.22: the labels of an OID-IRI's contents octets. -/
def decIri (rel : Bool) (cs : Octets) : Option (List String) :=
  match decUtf8 cs with
  | some chars =>
    let s := String.ofList (chars.map Char.ofNat)
    let ls := if rel then s.splitOn "/" else (s.splitOn "/").drop 1
    if (if rel then relIriContents ls else iriContents ls) = cs then some ls else none
  | none => none

/-- X.690 8.26: the time value whose notation, with the kind's characters removed, is `s0`. The
removed characters are put back where the kind's notation has them: DATE is YYYY-MM-DD,
TIME-OF-DAY hh:mm:ss, DATE-TIME both with T, DURATION starts with P (X.680 38.4.1–38.4.4). -/
def timeNotation (k : TimeKind) (s0 : List Char) : List Char :=
  match k with
  | .time => s0
  | .date => s0.take 4 ++ '-' :: (s0.drop 4).take 2 ++ '-' :: s0.drop 6
  | .timeOfDay => s0.take 2 ++ ':' :: (s0.drop 2).take 2 ++ ':' :: s0.drop 4
  | .dateTime => s0.take 4 ++ '-' :: (s0.drop 4).take 2 ++ '-' :: (s0.drop 6).take 2 ++ 'T' ::
      (s0.drop 8).take 2 ++ ':' :: (s0.drop 10).take 2 ++ ':' :: s0.drop 12
  | .duration => 'P' :: s0

def decTime (p : Profile) (k : TimeKind) (cs : Octets) : Except String TimeV :=
  match decUtf8 cs with
  | none => .error "8.26: not UTF-8"
  | some chars =>
    let s0 := chars.map Char.ofNat
    let s := timeNotation k s0
    match Notation.parse s with
    | none => .error "8.26: not the value notation of a time value"
    | some w =>
      if !w.Wf then .error "X.680 38: not a time value"
      else if k.strip s != s0 then .error "8.26: characters that are removed are present"
      else if utf8String ((k.strip s).map Char.toNat) != cs then .error "8.26: not UTF-8 of characters"
      else if p.restricted && utf8String ((k.strip (TimePrint.time w.norm)).map Char.toNat) != cs then
        .error "11.9: not the canonical form"
      else .ok w

/-- `GenTimeCanon`, decided. -/
def genTimeCanonB (s : List Char) : Bool :=
  s.getLast? == some 'Z' && s.length ≥ 15 &&
  let ymdhms := s.take 14
  let rest := (s.drop 14).dropLast
  ymdhms.all isDig &&
  (rest.isEmpty || (rest.head? == some '.' && rest.length ≥ 2 && (rest.drop 1).all isDig &&
    rest.getLast? != some '0'))

def utcTimeCanonB (s : List Char) : Bool :=
  s.length == 13 && s.getLast? == some 'Z' && (s.take 12).all isDig

/-! ## Open types: which type (X.682 10) -/

/-- A textually enclosing SEQUENCE, SET, CHOICE, SEQUENCE OF or SET OF being decoded (X.682
10.10): what it is, its components' names, scopes and types, the components decoded so far, and the
one being decoded. A SEQUENCE OF or SET OF offers no components (X.682 10.8). -/
structure DFrame where
  kind : FrameKind
  comps : List (String × Scope × Ty)
  done : List (String × Val)
  current : String

/-- X.682 10.8, 10.10: the value an "AtNotation" refers to, while decoding inside `frames`
(innermost first): through the components decoded, or into the one being decoded. -/
def atResolve (E : Env) (n : Nat) (frames : List DFrame) (r : AtRef) : Option (Val × Scope × Ty) :=
  let rec walk : Nat → List String → Option (Val × Scope × Ty)
    | _, [] => none
    | i, p :: rest => match frames[i]? with
      | none => none
      | some fr =>
        if (fr.done.lookup p).isSome then navigate E n fr.comps (.seq fr.done) (p :: rest)
        else if fr.current = p then (if i = 0 then none else walk (i - 1) rest)
        else none
  match r.level with
  -- 10.10 a): the outermost SEQUENCE, SET or CHOICE
  | none => match (frames.zipIdx.filter fun (fr, _) => fr.kind != .seqOf && fr.kind != .setOf).getLast? with
    | some (_, i) => walk i r.path
    | none => none
  -- 10.10 b): up by `k` from the innermost SEQUENCE or SET
  | some k => match frames.findIdx? fun fr => fr.kind == .seq || fr.kind == .set with
    | some i => walk (i + k) r.path
    | none => none

/-- Value notation, evaluated where it can be (references followed). -/
def evalValFn (E : Env) : Nat → Scope → Val → Option Val
  | 0, _, _ => none
  | n + 1, sc, .ref mn name args => (resolveVal E n sc mn name args).bind fun (sc', v) => evalValFn E n sc' v
  | _ + 1, _, .raw _ => none
  | _ + 1, _, v => some v

/-- Equality of the simple values that keys of tables are. -/
def valKeyEq : Val → Val → Bool
  | .oid a, .oid b => a == b
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .chars a, .chars b => a == b
  | .enum a, .enum b => a == b
  | _, _ => false

mutual
  /-- X.681 12: the objects of an object set that can be listed (root and additions). -/
  def objsOfSet (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → ObjSet → List ObjV
    | 0, _, _, _ => []
    | n + 1, sc, cf, .ref mn name args => match resolveObjSet E n sc mn name args with
      | some (sc', c, s) => objsOfSet E n sc' ((c.bind fun c => classFields E n sc' c).or cf) s
      | none => []
    | n + 1, sc, cf, .spec root _ adds =>
      (match root with | some r => objsOfElems E n sc cf r | none => []) ++
      (match adds with | some a => objsOfElems E n sc cf a | none => [])

  def objsOfElems (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → OElems → List ObjV
    | 0, _, _, _ => []
    | n + 1, sc, cf, .obj o => objsOfObj E n sc cf o
    | n + 1, sc, cf, .set s => objsOfSet E n sc cf s
    | n + 1, sc, cf, .union a b => objsOfElems E n sc cf a ++ objsOfElems E n sc cf b
    -- the decoder only looks rows up; a set difference or intersection is not computed
    | n + 1, sc, cf, .inter a _ | n + 1, sc, cf, .except a _ => objsOfElems E n sc cf a
    | _ + 1, _, _, .fromObjects _ _ => []

  def objsOfObj (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → Obj → List ObjV
    | 0, _, _, _ => []
    | _ + 1, sc, cf, .defn settings => let (csc, fs) := cf.getD (sc, []); [⟨sc, settings, csc, fs⟩]
    | n + 1, sc, cf, .ref mn name args => match resolveObj E n sc mn name args with
      | some (sc', c, ob) => objsOfObj E n sc' ((c.bind fun c => classFields E n sc' c).or cf) ob
      | none => []
    | _ + 1, _, _, _ => []
end

/-- X.682 10.19: the type a component relation constraint selects for an open type: the row whose
key field holds the value of the referenced component, and that row's type field. -/
def tableHint (E : Env) (n : Nat) (frames : List DFrame) (sc : Scope) (t : Ty) (c : Constraint) :
    Option (Scope × Ty) := do
  let .table os (r :: _) := c | none
  let (csc, cls, path) ← classFieldOf E n sc t
  let cf ← classFields E n csc cls
  let (v, rsc, rty) ← atResolve E n frames r
  let (_, _, kpath) ← classFieldOf E n rsc rty
  let [kf] := kpath | none
  let [f] := path | none
  let row ← (objsOfSet E n sc (some cf) os).find? fun row =>
    match row.setting kf with
    | some (vsc, .value w) => match evalValFn E n vsc w with
      | some w' => valKeyEq w' v
      | none => false
    | _ => false
  match row.setting f with
  | some (tsc, .type ty) => some (tsc, ty)
  | _ => none

/-- A type for an open type's encoding with a universal tag, when no table says which: the type
with that tag (X.680 8.4, Table 1). -/
def univTy : Tag → Option Ty
  | ⟨.universal, 1⟩ => some .boolean
  | ⟨.universal, 2⟩ => some (.integer [])
  | ⟨.universal, 3⟩ => some (.bitString [])
  | ⟨.universal, 4⟩ => some .octetString
  | ⟨.universal, 5⟩ => some .null
  | ⟨.universal, 6⟩ => some .objectIdentifier
  | ⟨.universal, 9⟩ => some .real
  | ⟨.universal, 12⟩ => some (.restricted .utf8)
  | ⟨.universal, 13⟩ => some .relativeOid
  | ⟨.universal, 18⟩ => some (.restricted .numeric)
  | ⟨.universal, 19⟩ => some (.restricted .printable)
  | ⟨.universal, 20⟩ => some (.restricted .teletex)
  | ⟨.universal, 21⟩ => some (.restricted .videotex)
  | ⟨.universal, 22⟩ => some (.restricted .ia5)
  | ⟨.universal, 23⟩ => some .utcTime
  | ⟨.universal, 24⟩ => some .generalizedTime
  | ⟨.universal, 25⟩ => some (.restricted .graphic)
  | ⟨.universal, 26⟩ => some (.restricted .visible)
  | ⟨.universal, 27⟩ => some (.restricted .general)
  | ⟨.universal, 28⟩ => some (.restricted .universal)
  | ⟨.universal, 30⟩ => some (.restricted .bmp)
  | _ => none

/-- A type for an open type's encoding when no table says which (X.681 14.2: the type is the
application's): the type its universal tag gives (`univTy`); for another constructed SEQUENCE or
SET, SEQUENCE OF or SET OF open types; for a tag of another class, that tag, explicit around an open
type when it holds one encoding and otherwise implicit, on SEQUENCE OF open types if constructed
and on OCTET STRING if primitive. -/
def nodeTy : Node → Option Ty
  | .prim tg _ _ => match univTy tg with
    | some t => some t
    | none => if tg.cls = .universal then none else some (.tagged tg .implicit .octetString)
  | .cons tg _ ch => match univTy tg with
    | some t => some t
    | none =>
      if tg = univ 16 then some (.sequenceOf .openType)
      else if tg = univ 17 then some (.setOf .openType)
      else if tg.cls = .universal then none
      else if ch.length = 1 then some (.tagged tg .explicit .openType)
      else some (.tagged tg .implicit (.sequenceOf .openType))

/-- The tags the encodings `ber E p n sc t` relates can have, by `ber`'s own recursion and fuel
(`ber_encTags`): X.680's `tagsOf`, read with the fuel the encoding is read with. An untagged CHOICE
has its alternatives' tags; an open type any (`none`). -/
def encTags (E : Env) : Nat → Scope → Ty → Option (List Tag)
  | 0, _, _ => some []
  | _ + 1, _, .tagged tg _ _ => some [tg]
  | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => encTags E n sc' t
    | none => some []
  | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => encTags E n sc' t
    | none => some []
  | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
    | some (sc', t) => encTags E n sc' t
    | none => some []
  | n + 1, sc, .constrained t _ => encTags E n sc t
  | n + 1, sc, .selection nm t => match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some a => encTags E n sc' a.ty
      | none => some []
    | _ => some []
  | n + 1, sc, .choice root ext =>
    (altTys E n sc root ext).foldr (fun alt acc => match encTags E n sc alt.2, acc with
      | some a, some b => some (a ++ b)
      | _, _ => none) (some [])
  | _ + 1, _, .openType => none
  | n + 1, sc, .classField cls path =>
    match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => encTags E n sc' t
    | some (_, .typeField _ _) | some (_, .varValue _ _ _) | some (_, .varValueSet _ _ _) => none
    | _ => some []
  | n + 1, sc, .fromObjects src path => match objSetClass E n sc src with
    | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => encTags E n sc' t
      | some (_, _) => none
      | none => some []
    | none => some []
  | _ + 1, _, .instanceOf _ => some [univ 8]
  | _ + 1, _, t => some ((t.universalTag?.map fun k => [univ k]).getD [])

/-- The first of `l` that `f` takes to a value, or else the first error. -/
def firstOk {α β : Type} (f : α → Except String β) (err : String) : List α → Except String β
  | [] => .error err
  | a :: rest => match f a with
    | .ok b => .ok b
    | .error e => match firstOk f err rest with
      | .ok b => .ok b
      | .error _ => .error e

/-- X.690 8.11.2: an assignment of the encodings of a SET, in order, to distinct components among
those `cand` offers for each, that `k` accepts. -/
def setSearch {L : Nat} {β : Type} (cand : Node → List (Fin L)) (k : List (Fin L × Node) → Except String β) :
    List Node → List (Fin L × Node) → Except String β
  | [], acc => k acc.reverse
  | nd :: rest, acc =>
    firstOk (fun i => setSearch cand k rest ((i, nd) :: acc))
      s!"8.11.2: an encoding with tag {repr nd.tag} that no component has"
      ((cand nd).filter fun i => !(acc.any (·.1 == i)))

/-- The tags a value of `t` may have; `none` (an open type) matches any. -/
def tagMatches (E : Env) (n : Nat) (sc : Scope) (t : Ty) (tg : Tag) : Bool :=
  match encTags E n sc t with
  | some ts => ts.contains tg
  | none => true

/-! ## Values (8.2–8.26) -/

/-- X.690 8.9, 8.11.2: the components of a SEQUENCE (in order) from its encodings. A component is
there when the next encoding has one of its tags and decodes as it; otherwise it is left out, and
the search goes on (so a schema whose tags X.680 25 would reject still decodes). `fin` finishes a
complete assignment (the DEFAULT check of 11.5), inside the search. Which components a
value must have is a property of the value set (`presentOkB`), not of the encoding. -/
def decSeqComps {β : Type} (E : Env) (n : Nat) (rec : DFrame → Scope → Ty → Node → Except String Val)
    (all : List (String × Scope × Ty)) (fin : List (String × Val) → Except String β) :
    List (Entry × Ty) → List Node → List (String × Val) → Except String β
  | [], [], acc => fin acc
  | [], nd :: _, _ => .error s!"8.9.2: an encoding with tag {repr nd.tag} that no component has"
  | (en, ty) :: cs, nd :: rest, acc =>
    if tagMatches E n en.scope ty nd.tag then
      match (do
          let x ← rec ⟨.seq, all, acc, en.name⟩ en.scope ty nd
          decSeqComps E n rec all fin cs rest (acc ++ [(en.name, x)])) with
      | .ok r => .ok r
      | .error e => match decSeqComps E n rec all fin cs (nd :: rest) acc with
        | .ok r => .ok r
        | .error _ => .error e
    else decSeqComps E n rec all fin cs (nd :: rest) acc
  | (_, _) :: cs, [], acc => decSeqComps E n rec all fin cs [] acc

/-- X.680 25.12, X.690 11.5: an encoded component equal to its default value (CER, DER). Decided for
the simple values that defaults are; anything else counts as not equal. -/
def isDefaultB (E : Env) (n : Nat) (en : Entry) (x : Val) : Bool :=
  match en.presence with
  | .default_ d => match evalValFn E n en.scope d with
    | some d' => valKeyEq x d'
    | none => false
  | _ => false

/-- Value notation that denotes one simple value (no components), followed through references. -/
def evalLit (E : Env) : Nat → Scope → Val → Option Val
  | 0, _, _ => none
  | n + 1, sc, .ref mn name args =>
    (resolveVal E n sc mn name args).bind fun (sc', v) => evalLit E n sc' v
  | _ + 1, _, .bool b => some (.bool b)
  | _ + 1, _, .int i => some (.int i)
  | _ + 1, _, .enum id => some (.enum id)
  | _ + 1, _, .oid a => some (.oid a)
  | _ + 1, _, .chars cs => some (.chars cs)
  | _ + 1, _, .octets os => some (.octets os)
  | _ + 1, _, .bits bs => some (.bits bs)
  | _ + 1, _, _ => none

/-- Two simple values that are certainly different. -/
def litNeq : Val → Val → Bool
  | .bool a, .bool b => a != b
  | .int a, .int b => a != b
  | .enum a, .enum b => a != b
  | .oid a, .oid b => a != b
  | .chars a, .chars b => a != b
  | .octets a, .octets b => a != b
  | .bits a, .bits b => a != b
  | _, _ => false

/-- The types whose values are the same abstract value only when they are equal (`eqv` is `=`),
through references, tags and constraints. -/
def eqIsEq (E : Env) : Nat → Scope → Ty → Bool
  | 0, _, _ => false
  | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => eqIsEq E n sc' t
    | none => false
  | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => eqIsEq E n sc' t
    | none => false
  | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
    | some (sc', t) => eqIsEq E n sc' t
    | none => false
  | n + 1, sc, .tagged _ _ t => eqIsEq E n sc t
  | n + 1, sc, .constrained t _ => eqIsEq E n sc t
  | _ + 1, _, .boolean | _ + 1, _, .integer _ | _ + 1, _, .enumerated _ _ | _ + 1, _, .null
  | _ + 1, _, .objectIdentifier | _ + 1, _, .relativeOid | _ + 1, _, .octetString
  | _ + 1, _, .restricted _ | _ + 1, _, .utcTime | _ + 1, _, .generalizedTime => true
  | _ + 1, _, .bitString named => named.isEmpty
  | _ + 1, _, _ => false

/-- X.680 25.12, X.690 11.5: the encoded value `x` of component `en` is certainly not its default
value (`¬ IsDefault`, `notDefaultB_spec`): the default is a simple value, and differs from `x`. -/
def notDefaultB (E : Env) (n : Nat) (en : Entry) (x : Val) : Bool :=
  match en.presence with
  | .default_ d => match evalLit E n en.scope d with
    | some d' => eqIsEq E n en.scope en.ty && litNeq x d'
    | none => false
  | _ => true

/-- X.690 11.5: under CER and DER, an encoded component that may equal its default value: an
error, saying whether it does or whether that could not be decided. -/
def defaultErr (E : Env) (n : Nat) (comps : List (Entry × Ty)) (cs : List (String × Val)) :
    Option String :=
  match comps.find? fun (en, _) => match cs.lookup en.name with
    | some x => !notDefaultB E n en x
    | none => false with
  | some (en, _) =>
    if (cs.lookup en.name).any (isDefaultB E n en) then
      some s!"11.5: {en.name}, equal to its default value, is encoded"
    else some s!"11.5: whether {en.name} equals its default value is not decided"
  | none => none

def guardE {α : Type} (b : Bool) (msg : String) (x : α) : Except String α :=
  if b then .ok x else .error msg

/-- A short name for a type, for messages. -/
def tyName : Ty → String
  | .ref n | .extRef _ n | .paramRef _ n _ => n
  | .tagged tg _ _ => s!"[{repr tg.cls} {tg.num}] …"
  | .constrained t _ => tyName t ++ " (…)"
  | .sequence .. => "SEQUENCE" | .set .. => "SET" | .choice .. => "CHOICE"
  | .sequenceOf _ => "SEQUENCE OF" | .setOf _ => "SET OF"
  | .boolean => "BOOLEAN" | .integer _ => "INTEGER" | .bitString _ => "BIT STRING"
  | .octetString => "OCTET STRING" | .null => "NULL" | .objectIdentifier => "OBJECT IDENTIFIER"
  | .restricted k => reprStr k | .utcTime => "UTCTime" | .generalizedTime => "GeneralizedTime"
  | .openType => "open type" | .classField _ p => ".".intercalate p
  | _ => "a type"

/-- The integer of INTEGER contents octets (8.3). -/
def intOrErr (cs : Octets) : Except String (Option Int) :=
  if intContentsB cs then .ok (some (tcValue (bitsOf cs))) else .error "8.3.2: indirect-reference"

/-- Whether the type a contents constraint contains is known: not an open type (a type field of a
class) whose table has no row, or no setting, for the referenced component (X.681 12.9, 14.2). -/
def containedKnown (E : Env) (n : Nat) (frames : List DFrame) (sc : Scope) : Ty → Bool
  | .constrained t c => match classFieldOf E n sc t with
    | some (csc, cls, path) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (_, .typeField _ _) => (tableHint E n frames sc t c).isSome
      | _ => true
    | none => true
  | .classField .. | .openType => false
  | _ => true

/-- The error of an open type whose type nothing says (no table row, no universal tag). -/
def openTypeUnknown : String := "8.15: open type, type unknown"

/-! ### EXTERNAL (8.18) -/

/-- The first encoding, if it satisfies `P`, and the rest. -/
def extTake (P : Node → Bool) : List Node → List Node × List Node
  | c :: rest => if P c then ([c], rest) else ([], c :: rest)
  | [] => ([], [])

/-- A primitive encoding with tag `tg`. -/
def isPrimWith (tg : Tag) : Node → Bool
  | .prim tg' _ _ => tg' == tg
  | .cons .. => false

/-- 8.18.1: the `encoding`, the last encoding. -/
def extEnc : List Node → Except String Node
  | [c] => .ok c
  | _ => .error "8.18.1: encoding"

/-- 8.18.3: the `data-value-descriptor`, if encoded, as `f` decodes it. -/
def extDesc (f : Node → Except String Val) : List Node → Except String (Option Val)
  | [c] => (f c).map some
  | _ => .ok none

/-- X.680 37.5: the abstract value of EXTERNAL. -/
def extVal (id : Val) (d : Option Val) (dv : Octets) : Val :=
  .seq ([("identification", id)] ++ (match d with | some x => [("data-value-descriptor", x)] | none => [])
    ++ [("data-value", .octets dv)])

/-- 8.18.4: the `direct-reference`, if encoded. -/
def extOid : List Node → Except String (Option (List Nat))
  | [.prim _ _ cs] => match decOidArcs false cs with
    | some a => .ok (some a)
    | none => .error "8.19: direct-reference"
  | _ => .ok none

/-- 8.18.4: the `indirect-reference`, if encoded. -/
def extInt : List Node → Except String (Option Int)
  | [.prim _ _ cs] => intOrErr cs
  | _ => .ok none

/-- 8.18.4, Table 2: the "identification" alternative the references give. -/
def extId : Option (List Nat) → Option Int → Except String Val
  | some o, none => .ok (.choice "syntax" (.oid o))
  | none, some i => .ok (.choice "presentation-context-id" (.int i))
  | some o, some i => .ok (.choice "context-negotiation"
      (.seq [("presentation-context-id", .int i), ("transfer-syntax", .oid o)]))
  | none, none => .error "8.18.4, Table 2: no reference"

/-- 8.18.5–8.18.11: the data value octets of the `encoding` CHOICE. -/
def extData (p : Profile) (n : Nat) (enc : Node) : Except String Octets :=
  match enc with
  | .cons ⟨.context, 0⟩ _ [inner] =>
    if lenOkB p inner then .ok inner.octets else .error "8.18.9: single-ASN1-type"
  | .prim ⟨.context, 1⟩ _ _ | .cons ⟨.context, 1⟩ _ _ => decOctets p n (univ 4) (enc.retag (univ 4))
  | .prim ⟨.context, 2⟩ _ _ | .cons ⟨.context, 2⟩ _ _ => do
    let bs ← decBits p n true (univ 3) (enc.retag (univ 3))
    if bs.length % 8 = 0 then .ok (bitsToOctets bs) else .error "8.18.8: arbitrary not whole octets"
  | _ => .error "8.18.5: encoding"

/-- `dec E p n frames hint sc t nd`: the value of type `t` (written in scope `sc`) that `nd`
encodes under profile `p`. `frames` are the textually enclosing values being decoded (X.682
10.10); `hint` is the type a table constraint chose for an open type. -/
def dec (E : Env) (p : Profile) : Nat → List DFrame → Option (Scope × Ty) → Scope → Ty → Node →
    Except String Val
  | 0, _, _, _, _, _ => .error "fuel"
  -- 8.2, 11.1
  | _ + 1, _, _, _, .boolean, .prim ⟨.universal, 1⟩ _ [o] =>
    if p.restricted && o.val != 0 && o.val != 255 then .error "11.1: TRUE not FF"
    else .ok (.bool (o.val != 0))
  -- 8.3
  | _ + 1, _, _, _, .integer _, .prim ⟨.universal, 2⟩ _ cs =>
    if intContentsB cs then .ok (.int (tcValue (bitsOf cs))) else .error "8.3.2: INTEGER not minimal"
  -- 8.4
  | _ + 1, _, _, _, .enumerated r e, .prim ⟨.universal, 10⟩ _ cs =>
    if !intContentsB cs then .error "8.3.2: ENUMERATED not minimal" else
    let k := tcValue (bitsOf cs)
    match (enumNumbers r e).find? (·.2 == k) with
    | some (id, _) => guardE ((enumNumbers r e).lookup id == some k) "X.680 20: two items with one identifier" (.enum id)
    | none => .error s!"8.4: {k} is no item's number"
  -- 8.5
  | _ + 1, _, _, _, .real, .prim ⟨.universal, 9⟩ _ cs => (decReal p cs).map .real
  -- 8.6, 11.2.2
  | n + 1, _, _, _, .bitString named, nd => do
    let bs ← decBits p n true (univ 3) nd
    if named != [] && p.restricted && bs != stripTrailingZeros bs then
      .error "11.2.2: trailing 0 bits of a bit string with named bits"
    else .ok (.bits bs)
  -- 8.7
  | n + 1, _, _, _, .octetString, nd => (decOctets p n (univ 4) nd).map .octets
  -- 8.8
  | _ + 1, _, _, _, .null, .prim ⟨.universal, 5⟩ _ [] => .ok .null
  -- 8.9
  | n + 1, frames, _, sc, .sequence r e r2, .cons ⟨.universal, 16⟩ _ ch => do
    let comps := compTys E n sc r e r2
    let all := comps.map fun (en, ty) => (en.name, en.scope, ty)
    if !decide (comps.map (·.1.name)).Nodup then .error "X.680 25: two components with one identifier" else
    decSeqComps E n (fun fr sc' t nd => dec E p n (fr :: frames) none sc' t nd) all
      (fun cs => match p.restricted, defaultErr E n comps cs with
        | true, some m => .error m
        | _, _ => .ok (.seq cs))
      comps ch []
  -- 8.10
  | n + 1, frames, _, sc, .sequenceOf el, .cons ⟨.universal, 16⟩ _ ch =>
    (ch.mapM fun c => dec E p n (⟨.seqOf, [], [], ""⟩ :: frames) none sc el c).map .seqOf
  -- 8.11, 9.3, 10.3
  | n + 1, frames, _, sc, .set r e r2, .cons ⟨.universal, 17⟩ _ ch =>
    let comps := compTys E n sc r e r2
    let all := comps.map fun (en, ty) => (en.name, en.scope, ty)
    if !decide (comps.map (·.1.name)).Nodup then .error "X.680 27: two components with one identifier" else
    -- each encoding is a component whose tags it has, each component at most once (searched)
    setSearch (fun nd => (List.finRange comps.length).filter fun i =>
        tagMatches E n comps[i].1.scope comps[i].2 nd.tag)
      (fun found => do
        -- in the order of the type
        let srt := found.mergeSort fun a b => decide (a.1 ≤ b.1)
        if !sortedB (fun a b => decide (a < b)) (srt.map (·.1)) then .error "8.11.2: a component encoded twice" else
        let cs ← srt.mapM fun (i, nd) => do
          let x ← dec E p n (⟨.set, all, [], comps[i].1.name⟩ :: frames) none comps[i].1.scope comps[i].2 nd
          .ok (comps[i].1.name, x)
        if p = .der && !sortedB (fun a b => Tag.lt a.tag b.tag) ch then
          .error "10.3: SET components not in tag order"
        else if p = .cer && !sortedB (fun (a b : Fin comps.length × Node) =>
            Tag.lt ((cerKey E n comps[a.1].1.scope comps[a.1].2).getD a.2.tag)
              ((cerKey E n comps[b.1].1.scope comps[b.1].2).getD b.2.tag)) found then
          .error "9.3: SET components not in CER order"
        else match p.restricted, defaultErr E n comps cs with
          | true, some m => .error m
          | _, _ => .ok (.seq cs))
      ch []
  -- 8.12, 11.6
  | n + 1, frames, _, sc, .setOf el, .cons ⟨.universal, 17⟩ _ ch => do
    let vs ← ch.mapM fun c => dec E p n (⟨.setOf, [], [], ""⟩ :: frames) none sc el c
    if p.restricted && !sortedB (fun a b => octLeB a.octets b.octets) ch then
      .error "11.6: SET OF components not in ascending order"
    else .ok (.setOf vs)
  -- 8.13
  | n + 1, frames, _, sc, .choice r e, nd =>
    firstOk (fun (alt : Alt × Ty) => (dec E p n (⟨.choice, (choiceAlts r e).map fun a => (a.name, sc, a.ty), [],
        alt.1.name⟩ :: frames) none sc alt.2 nd).map (.choice alt.1.name))
      s!"8.13: no alternative has tag {repr nd.tag}"
      ((altTys E n sc r e).filter fun alt => tagMatches E n sc alt.2 nd.tag)
  | n + 1, _, _, sc, .selection nm t, nd =>
    match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some alt => dec E p n [] none sc' alt.ty nd
      | none => .error "X.680 30: no such alternative"
    | _ => .error "X.680 30: not a CHOICE"
  -- 8.19–8.22
  | _ + 1, _, _, _, .objectIdentifier, .prim ⟨.universal, 6⟩ _ cs =>
    match decOidArcs false cs with | some a => .ok (.oid a) | none => .error "8.19: OBJECT IDENTIFIER"
  | _ + 1, _, _, _, .relativeOid, .prim ⟨.universal, 13⟩ _ cs =>
    match decOidArcs true cs with | some a => .ok (.oid a) | none => .error "8.20: RELATIVE-OID"
  | _ + 1, _, _, _, .oidIri, .prim ⟨.universal, 35⟩ _ cs =>
    match decIri false cs with | some a => .ok (.iri a) | none => .error "8.21: OID-IRI"
  | _ + 1, _, _, _, .relativeOidIri, .prim ⟨.universal, 36⟩ _ cs =>
    match decIri true cs with | some a => .ok (.iri a) | none => .error "8.22: RELATIVE-OID-IRI"
  -- 8.17, 8.24
  | n + 1, _, _, _, .embeddedPdv, nd =>
    dec E p n [] none (.ofModule assocModule) (.tagged (univ 11) .implicit embeddedPdvAssoc) nd
  | n + 1, _, _, _, .characterString, nd =>
    dec E p n [] none (.ofModule assocModule) (.tagged (univ 29) .implicit characterStringAssoc) nd
  -- 8.18
  | n + 1, _, _, _, .external, .cons ⟨.universal, 8⟩ _ ch => do
    let s1 := extTake (isPrimWith (univ 6)) ch
    let s2 := extTake (isPrimWith (univ 2)) s1.2
    let s3 := extTake (fun c => c.tag == univ 7) s2.2
    let enc ← extEnc s3.2
    let o ← extOid s1.1
    let i ← extInt s2.1
    let id ← extId o i
    let d ← extDesc (fun c => dec E p n [] none (.ofModule externalModule) .objectDescriptor c) s3.1
    let dv ← extData p n enc
    .ok (extVal id d dv)
  -- 8.23
  | n + 1, _, _, _, .restricted k, nd => do
    let tg := ((Ty.restricted k).universalTag?).getD 0
    let os ← decOctets p n (univ tg) nd
    decString p k os
  -- 8.25, 11.7, 11.8
  | n + 1, _, _, _, .generalizedTime, nd => do
    let os ← decOctets p n (univ 24) nd
    let x ← decString p .visible os
    match x with
    | .chars cs => guardE (!p.restricted || genTimeCanonB (cs.map Char.ofNat)) "11.7: GeneralizedTime form" x
    | _ => .error "8.25"
  | n + 1, _, _, _, .utcTime, nd => do
    let os ← decOctets p n (univ 23) nd
    let x ← decString p .visible os
    match x with
    | .chars cs => guardE (!p.restricted || utcTimeCanonB (cs.map Char.ofNat)) "11.8: UTCTime form" x
    | _ => .error "8.25"
  | n + 1, _, _, _, .objectDescriptor, nd => do
    let os ← decOctets p n (univ 7) nd
    decString p .graphic os
  -- references: no enclosing values are visible from the referenced text (X.682 10.10)
  | n + 1, _, _, sc, .ref name, nd => match resolveTy E n sc none name [] with
    | some (sc', t) => dec E p n [] none sc' t nd
    | none => .error s!"reference {name} does not resolve"
  | n + 1, _, _, sc, .extRef mn name, nd => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => dec E p n [] none sc' t nd
    | none => .error s!"reference {mn}.{name} does not resolve"
  | n + 1, _, _, sc, .paramRef mn name args, nd => match resolveTy E n sc mn name args with
    | some (sc', t) => dec E p n [] none sc' t nd
    | none => .error s!"reference {name}{"{…}"} does not resolve"
  -- 8.14
  | n + 1, frames, _, sc, .tagged tg kind t, nd =>
    if isExplicit E n sc kind t then
      match nd with
      | .cons tg' _ [c] => if tg' == tg then dec E p n frames none sc t c
        else .error s!"8.14.3: tag {repr tg'} where {repr tg} belongs"
      | _ => .error "8.14.3: an explicit tag is a constructed encoding of one encoding"
    else if nd.tag != tg then .error s!"8.14.4: tag {repr nd.tag} where {repr tg} belongs"
    else match encTags E n sc t with
      | some [tb] => dec E p n frames none sc t (nd.retag tb)
      | _ => .error "8.14.4: implicit tagging of a type without one tag"
  -- 8.1.1.4; X.682 10 chooses an open type's type; X.682 11.4: a contents constraint's octets are
  -- an encoding of the contained type, under the rules ENCODED BY names (`hook`)
  | n + 1, frames, _, sc, .constrained t c, nd => do
    let v ← dec E p n frames (tableHint E n frames sc t c) sc t nd
    let os? : Option Octets := match v with
      | .octets os => some os
      | .bits bs => if bs.length % 8 = 0 then some (bitsToOctets bs) else none
      | _ => none
    match c, os? with
    | .contents (some ct) enc, some os =>
      let q : Option Profile := match enc with
        | none => some p
        | some e => match evalValFn E n sc e with
          | some (.oid o) => [Profile.ber, .cer, .der].find? (·.oid = o)
          | _ => none
      match q, containedKnown E n frames sc ct with
      | none, _ | _, false => .ok v
      | some q, true => match parseNode (os.length + 1) os with
        | some (nd', []) =>
          let r : Except String Val := if lenOkB q nd' then dec E q n frames none sc ct nd'
            else .error "a length form its rules do not allow"
          match r with
          | .ok _ => .ok v
          | .error e => guardE (e.startsWith openTypeUnknown) s!"X.682 11.4: CONTAINING: {e}" v
        | _ => .error "X.682 11.4: CONTAINING: the octets are not one encoding"
    | _, _ => .ok v
  -- 8.15
  | n + 1, _, hint, sc, .openType, nd =>
    match hint with
    | some (sc', ty) => do
      let w ← dec E p n [] none sc' ty nd
      if valSemB E n sc' ty w then .ok (.open_ ty w)
      else .error "X.680: the open type's value is not a value of the type the table gives"
    | none => match nodeTy nd with
      | some ty => (dec E p n [] none sc ty nd).map (.open_ ty)
      | none => .error s!"{openTypeUnknown} with tag {repr nd.tag}"
  | n + 1, frames, hint, sc, .classField cls path, nd =>
    match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => dec E p n frames none sc' t nd
    | some (_, .typeField _ _) | some (_, .varValue _ _ _) | some (_, .varValueSet _ _ _) =>
      dec E p n frames hint sc .openType nd
    | _ => .error "X.681 14: not a field of the class"
  | n + 1, frames, _, sc, .fromObjects src path, nd => match objSetClass E n sc src with
    | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => dec E p n frames none sc' t nd
      | some (_, _) => dec E p n frames none sc .openType nd
      | none => .error "X.681 15: not a field of the class"
    | none => .error "X.681 15: the object set's class is unknown"
  -- 8.16
  | n + 1, frames, _, sc, .instanceOf cls, nd =>
    dec E p n frames none sc (.tagged (univ 8) .implicit (instanceOfTy cls)) nd
  -- 8.26
  | _ + 1, _, _, _, t, .prim tg _ cs => match timeKind? t, t.universalTag? with
    | some k, some u => if tg != univ u then .error s!"8.26: tag {repr tg}"
      else (decTime p k cs).map .time
    | _, _ => .error s!"tag {repr tg} is not one the type {tyName t} can have"
  | _ + 1, _, _, _, t, nd => .error s!"tag {repr nd.tag} is not one the type {tyName t} can have"

/-- X.680 25.7, 27.1: every SEQUENCE and SET value in `v` has the mandatory root components of its
type, and X.680 41 (Table 8, 41.16): every character string value of a restricted character string
type has only characters of that type (UTF8String: code points up to U+10FFFF, no surrogates,
X680-4); through the components of SEQUENCE, SET, CHOICE, SEQUENCE OF and SET OF values, as
`valSemB`. These are properties of the value set, which `ber` and `per` do not ask. -/
def presentOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) : Bool :=
  match v with
  | .chars cs => match builtinV E n sc t with
    | some (_, .restricted k) => cs.all k.chars.mem
    | _ => true
  | .seq cs => match builtinV E n sc t with
    | some (sc', .sequence ro e r2) | some (sc', .set ro e r2) =>
      let es := entries E n sc' ro e r2
      !entriesKnown E n sc' ro e r2 ||
      ((es.all fun en => !en.presence.isMandatory || en.addition.isSome || (cs.lookup en.name).isSome) &&
       cs.attach.all fun ⟨(nm, w), h⟩ =>
        !(es.any (·.name == nm)) || es.any fun en => en.name == nm && presentOkB E n en.scope en.ty w)
    | _ => true
  | .seqOf vs | .setOf vs => match builtinV E n sc t with
    | some (sc', .sequenceOf el) | some (sc', .setOf el) => vs.attach.all fun ⟨w, h⟩ => presentOkB E n sc' el w
    | _ => true
  | .choice a w => match builtinV E n sc t with
    | some (sc', .choice ro ext) =>
      let alts := choiceAlts ro ext
      !(alts.any (·.name == a)) || alts.any fun alt => alt.name == a && presentOkB E n sc' alt.ty w
    | _ => true
  | _ => true
termination_by v
decreasing_by all_goals decr_syntax

/-- X.690: decode the whole of `os` as one encoding of a value of `t` (written in module `m`) under
profile `p`: the octets are one encoding (8.1), its length forms are the profile's (8.1.3, 9.1,
10.1), and the value is read from it. -/
def decode (E : Env) (p : Profile) (fuel : Nat) (m : Module) (t : Ty) (os : Octets) :
    Except String Val :=
  match parseNode (os.length + 1) os with
  | none => .error "8.1: not an encoding (identifier, length or end-of-contents octets)"
  | some (nd, rest) =>
    if !rest.isEmpty then .error s!"8.1: {rest.length} octets after the encoding"
    else if !lenOkB p nd then .error "8.1.3, 9.1, 10.1: a length form the profile does not allow"
    else do
      let v ← dec E p fuel [] none (.ofModule m) t nd
      -- the value is in the type (X.680): ranges, sizes, alphabets, time formats (`valSemB`)
      if !valSemB E fuel (.ofModule m) t v then
        .error "X.680: the value is not a value of the type (a constraint or format)"
      else if !presentOkB E fuel (.ofModule m) t v then
        .error "X.680 25.7, 27.1, 41: a mandatory component is missing, or a character not of its string type"
      else .ok v

/-! ## Showing values -/

partial def showVal : Val → String
  | .bool b => toString b
  | .int i => toString i
  | .enum id => id
  | .real r => reprStr r
  | .bits bs => s!"'{String.ofList (bs.map fun b => if b then '1' else '0')}'B"
  | .octets os => "'" ++ String.join (os.map fun o =>
      let h := Nat.toDigits 16 o.val; String.ofList (if h.length < 2 then '0' :: h else h)) ++ "'H"
  | .null => "NULL"
  | .seq cs => "{ " ++ ", ".intercalate (cs.map fun (n, v) => n ++ " " ++ showVal v) ++ " }"
  | .seqOf vs | .setOf vs => "{ " ++ ", ".intercalate (vs.map showVal) ++ " }"
  | .choice a v => a ++ " : " ++ showVal v
  | .oid arcs => "{ " ++ " ".intercalate (arcs.map toString) ++ " }"
  | .iri ls => "\"/" ++ "/".intercalate ls ++ "\""
  | .chars cs => "\"" ++ String.ofList (cs.map Char.ofNat) ++ "\""
  | .regChars cs => s!"<{cs.length} register characters>"
  | .time t => reprStr t
  | .open_ t v => s!"({tyName t}) " ++ showVal v
  | _ => "?"

end Asn1.X690

namespace Asn1.X690
open Asn1.X680

def jsonStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\"
    else if c.toNat < 32 then s!"\\u{String.ofList (List.replicate (4 - (Nat.toDigits 16 c.toNat).length) '0' ++ Nat.toDigits 16 c.toNat)}"
    else c.toString) ++ "\""

def hexOf (os : Octets) : String := String.join (os.map fun o =>
  let h := Nat.toDigits 16 o.val; String.ofList (if h.length < 2 then '0' :: h else h))

/-- A value as JSON, for comparing with other decoders: SEQUENCE/SET as objects, SEQUENCE OF and
SET OF as arrays, CHOICE as `{"$choice": name, "v": value}`, OBJECT IDENTIFIER as dotted text, bit
strings as `"b:…"`, octet strings as `"h:…"`, an open type as its value. -/
partial def showJson : Val → String
  | .bool b => toString b
  | .int i => toString i
  | .enum id => jsonStr id
  | .real r => jsonStr (reprStr r)
  | .bits bs => jsonStr ("b:" ++ String.ofList (bs.map fun b => if b then '1' else '0'))
  | .octets os => jsonStr ("h:" ++ hexOf os)
  | .null => "null"
  | .seq cs => "{" ++ ", ".intercalate (cs.map fun (n, v) => jsonStr n ++ ": " ++ showJson v) ++ "}"
  | .seqOf vs | .setOf vs => "[" ++ ", ".intercalate (vs.map showJson) ++ "]"
  | .choice a v => "{\"$choice\": " ++ jsonStr a ++ ", \"v\": " ++ showJson v ++ "}"
  | .oid arcs => jsonStr (".".intercalate (arcs.map toString))
  | .iri ls => jsonStr ("/" ++ "/".intercalate ls)
  | .chars cs => jsonStr (String.ofList (cs.map Char.ofNat))
  | .regChars cs => jsonStr s!"<{cs.length} register characters>"
  | .time t => jsonStr (String.ofList (TimePrint.time t.norm))
  | .open_ _ v => showJson v
  | _ => "\"?\""

end Asn1.X690
