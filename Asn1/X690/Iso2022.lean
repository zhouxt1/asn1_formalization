import Asn1.Bits
import Asn1.X680.Chars

/-!
# ISO/IEC 2022 in an 8-bit environment, as X.690 8.23.5 and 11.4 use it

TeletexString, VideotexString, GraphicString and GeneralString are encoded as "the octets specified
in ISO/IEC 2022 for encodings in an 8-bit environment, using the escape sequence and character
codings registered in accordance with ISO/IEC 2375" (X.690 8.23.5). Their abstract characters are
cells of registered sets (`RegChar`, X.680 39 and X.690 11.4 NOTE 2).

So an encoding is right when an ISO/IEC 2022 decoder, started in the state Table 3 assumes, reads
it back as the value's characters, and it uses only the escape sequences 8.23.5.1 and Table 3
allow. This file is that decoder, for the part of ISO/IEC 2022 those types can reach:
- designation of registered sets into G0–G3, C0 and C1 (ISO/IEC 2022 13.2), with "identify revised
  registration" (13.3);
- the locking shifts LS0 (SI), LS1 (SO), LS2, LS3, LS1R, LS2R, LS3R, and the single shifts SS2 and
  SS3 in their escape sequence form (9.3);
- characters from GL (2/1–7/14, or 2/0–7/15 for a 96-set), GR (10/1–15/14, or 10/0–15/15), C0
  (0/0–1/15) and C1 (8/0–9/15), each read as a cell of the set designated there; 2/0 and 7/15 in GL
  are SPACE and DELETE when the set there has 94 characters.

OPEN (ledger X690-6): ISO/IEC 2022 and the register's tables are not transcribed. The subset above
is what the escape sequences of register sections 2.1–2.6 can do; announcers (8.23.5.4), other
coding systems (2.8) and single control functions (2.7) are not allowed. 8.23.5.1 allows only
escape sequences "specified by one of the registration numbers used to define the type"; read
literally that excludes every shift, so G1–G3 could never be used. We allow the shifts wherever
Table 3 allows explicit escape sequences.
-/

namespace Asn1.X690

open Asn1.X680

/-- The decoder's state: the registration designated as G0–G3, C0 and C1, and which G set is
invoked into GL and GR (ISO/IEC 2022 9). -/
structure Iso2022State where
  g : Fin 4 → Option String
  c0 : Option String
  c1 : Option String
  gl : Fin 4
  gr : Option (Fin 4)

/-- X.690 8.23.5.2, Table 3: the registrations assumed designated and invoked at the start of each
string, and whether explicit escape sequences are allowed. -/
def assumed : StrType → Iso2022State
  | .teletex => ⟨fun i => if i = 0 then some "102" else none, some "106", some "107", 0, none⟩
  | .videotex => ⟨fun i => if i = 0 then some "102" else none, some "1", some "73", 0, none⟩
  | .ia5 | .general => ⟨fun i => if i = 0 then some "6" else none, some "1", none, 0, none⟩
  | _ => ⟨fun i => if i = 0 then some "6" else none, none, none, 0, none⟩

/-- X.690 Table 3, last column: explicit escape sequences allowed. -/
def escapesAllowed : StrType → Bool
  | .teletex | .videotex | .graphic | .general => true
  | _ => false

/-- X.690 8.23.5.1: a registration the type is defined by (X.680 Table 8). -/
def defines (k : StrType) (e : RegEntry) : Bool :=
  match k with
  | .teletex => e.no ∈ teletexEntries
  | .videotex => e.no ∈ videotexEntries
  | .graphic => e.kind.isG
  | .general => e.kind.isG || e.kind.isC
  | _ => false

/-- What an escape sequence designates: the set's kind (which fixes the Intermediate bytes), the
target (0–3 for G0–G3, 4 for C0, 5 for C1), and its Final byte. -/
structure Designation where
  kind : SetKind
  target : Nat
  final : Nat

/-- ISO/IEC 2022 13.2.2, Table 4: reads the bytes of a designating escape sequence after ESC. -/
def readDesignation : List Nat → Option (Designation × List Nat)
  | 0x24 :: 0x28 :: f :: r => some (⟨.multi, 0, f⟩, r)
  | 0x24 :: 0x29 :: f :: r => some (⟨.multi, 1, f⟩, r)
  | 0x24 :: 0x2A :: f :: r => some (⟨.multi, 2, f⟩, r)
  | 0x24 :: 0x2B :: f :: r => some (⟨.multi, 3, f⟩, r)
  -- ESC 2/4 F, for F = 4/0 to 4/2, designates G0 (13.2.2 NOTE)
  | 0x24 :: f :: r => if 0x40 ≤ f ∧ f ≤ 0x42 then some (⟨.multi, 0, f⟩, r) else none
  | 0x28 :: 0x21 :: f :: r => some (⟨.g94x, 0, f⟩, r)
  | 0x29 :: 0x21 :: f :: r => some (⟨.g94x, 1, f⟩, r)
  | 0x2A :: 0x21 :: f :: r => some (⟨.g94x, 2, f⟩, r)
  | 0x2B :: 0x21 :: f :: r => some (⟨.g94x, 3, f⟩, r)
  | 0x28 :: f :: r => some (⟨.g94, 0, f⟩, r)
  | 0x29 :: f :: r => some (⟨.g94, 1, f⟩, r)
  | 0x2A :: f :: r => some (⟨.g94, 2, f⟩, r)
  | 0x2B :: f :: r => some (⟨.g94, 3, f⟩, r)
  | 0x2D :: f :: r => some (⟨.g96, 1, f⟩, r)
  | 0x2E :: f :: r => some (⟨.g96, 2, f⟩, r)
  | 0x2F :: f :: r => some (⟨.g96, 3, f⟩, r)
  | 0x21 :: f :: r => some (⟨.c0, 4, f⟩, r)
  | 0x22 :: f :: r => some (⟨.c1, 5, f⟩, r)
  | _ => none

/-- The registration an escape sequence designates: the entry with its kind and Final byte, and the
"identify revised registration" byte if one preceded it (ISO/IEC 2022 13.3). -/
def entryFor (d : Designation) (irr : Option Nat) : Option RegEntry :=
  register.find? fun e => e.kind == d.kind && e.final == d.final && e.irr == irr

/-- X.690 11.4: the smallest numbered G or C set that a set of this kind can be designated into. -/
def smallestSet : SetKind → Nat
  | .g96 => 1
  | .c0 => 4
  | .c1 => 5
  | _ => 0

def Iso2022State.designated (st : Iso2022State) (no : String) : Bool :=
  (List.finRange 4).any (fun i => st.g i == some no) || st.c0 == some no || st.c1 == some no

def Iso2022State.set (st : Iso2022State) (target : Nat) (no : String) : Iso2022State :=
  if target < 4 then { st with g := fun i => if i.val = target then some no else st.g i }
  else if target = 4 then { st with c0 := some no } else { st with c1 := some no }

/-- The kind of the registration `no`. -/
def kindOf (no : String) : Option SetKind := (RegEntry.find? no).map (·.kind)

/-- The cell of G set `i` at the 7-bit code(s) that start `bs`, with the rest. `low` is the GL
range's offset: 0 for GL, 0x80 for GR. -/
def gCell (st : Iso2022State) (i : Fin 4) (off : Nat) (bs : List Nat) : Option (RegChar × List Nat) :=
  match st.g i with
  | some no => match kindOf no, bs with
    | some .multi, b1 :: b2 :: r =>
      if SetKind.hasCell .multi [b1 - off, b2 - off] && off ≤ b1 && off ≤ b2 then
        some (.cell no [b1 - off, b2 - off], r) else none
    | some k, b :: r => if off ≤ b && k.hasCell [b - off] then some (.cell no [b - off], r) else none
    | _, _ => none
  | none => none

/-- What one step of ISO/IEC 2022 decoding reads. -/
inductive Iso2022Ev where
  /-- 9.3: a locking shift, to the new state; `smallest` for LS0 and LS1, which invoke the
  smallest numbered G sets into GL -/
  | shift (st : Iso2022State) (smallest : Bool)
  /-- 13.2: a designation of registration `e` as G0–G3 (`target` 0–3), C0 (4) or C1 (5) -/
  | designate (target : Nat) (e : RegEntry)
  /-- a character; `no` is the registration whose cell it is (none for SPACE and DELETE in GL), and
  `single` whether a single shift (9.4) selected it -/
  | char (no : Option String) (ch : RegChar) (single : Bool)

/-- ISO/IEC 2022 in an 8-bit environment: the next event in `bs`, read in state `st`, using only
the escape sequences type `k` allows (X.690 8.23.5.1, 8.23.5.3, Table 3), and the rest. -/
def iso2022Step (k : StrType) (st : Iso2022State) : List Nat → Option (Iso2022Ev × List Nat)
  | [] => none
  | b :: rest =>
    if b = 0x1B then
      if !escapesAllowed k then none else
      match rest with
      -- 9.3.1: LS2, LS3, LS1R, LS2R, LS3R
      | 0x6E :: r => some (.shift { st with gl := 2 } false, r)
      | 0x6F :: r => some (.shift { st with gl := 3 } false, r)
      | 0x7E :: r => some (.shift { st with gr := some 1 } false, r)
      | 0x7D :: r => some (.shift { st with gr := some 2 } false, r)
      | 0x7C :: r => some (.shift { st with gr := some 3 } false, r)
      -- 9.4: SS2, SS3: one character from G2 or G3, in the GL or the GR range
      | 0x4E :: r | 0x4F :: r =>
        let i : Fin 4 := if rest.head? = some 0x4E then 2 else 3
        match gCell st i 0 r, gCell st i 0x80 r with
        | some (ch@(.cell no _), r'), _ | none, some (ch@(.cell no _), r') => some (.char (some no) ch true, r')
        | _, _ => none
      | r =>
        -- 13.3: identify revised registration, ESC 2/6 F', then the designation
        let (irr, r) : Option Nat × List Nat := match r with
          | 0x26 :: f' :: 0x1B :: r' => (some f', r')
          | _ => (none, r)
        match readDesignation r with
        | some (d, r') => match entryFor d irr with
          | some e => if defines k e then some (.designate d.target e, r') else none
          | none => none
        | none => none
    -- 9.3.1: LS0 (SI) and LS1 (SO)
    else if b = 0x0F then some (.shift { st with gl := 0 } true, rest)
    else if b = 0x0E then
      if !escapesAllowed k then none else some (.shift { st with gl := 1 } true, rest)
    -- C0
    else if b < 0x20 then (st.c0.map fun no => (.char (some no) (.cell no [b]) false, rest))
    -- C1
    else if 0x80 ≤ b ∧ b < 0xA0 then (st.c1.map fun no => (.char (some no) (.cell no [b]) false, rest))
    -- GL: SPACE and DELETE unless the set there has 96 characters
    else if b < 0x80 then
      let is96 := (st.g st.gl).bind kindOf == some .g96
      if !is96 && b = 0x20 then some (.char none .space false, rest)
      else if !is96 && b = 0x7F then some (.char none .delete false, rest)
      else match gCell st st.gl 0 (b :: rest) with
        | some (ch@(.cell no _), r) => some (.char (some no) ch false, r)
        | _ => none
    -- GR
    else match st.gr with
      | some i => match gCell st i 0x80 (b :: rest) with
        | some (ch@(.cell no _), r) => some (.char (some no) ch false, r)
        | _ => none
      | none => none

/-- In canonical mode (X.690 11.4), the registration a designation was made for, which the next
character must come from ("only when the register entry for the character is not currently
designated"). -/
abbrev Pending := Option String

/-- The characters `bs` denote from state `st`, reading event by event (`iso2022Step`). With
`canon`, X.690 11.4 applies too: a designation only of a set not designated, into the smallest
numbered G or C set its kind allows, immediately before a character of it; and no invocation
other than LS0 and LS1 (no single shifts either).

OPEN (ledger X690-7): 11.4 says designations "and invocations" go "into the smallest numbered G or
C set". Read as: LS0 and LS1 only. -/
def iso2022Decode (k : StrType) (canon : Bool) : Nat → Iso2022State → Pending → List Nat →
    Option (List RegChar)
  | _, _, pend, [] => if pend.isNone then some [] else none
  | 0, _, _, _ :: _ => none
  | fuel + 1, st, pend, b :: rest =>
    match iso2022Step k st (b :: rest) with
    | none => none
    | some (.shift st' smallest, r) =>
      if canon && !smallest then none else iso2022Decode k canon fuel st' pend r
    | some (.designate tgt e, r) =>
      if canon && (pend.isSome || st.designated e.no || tgt != smallestSet e.kind) then none
      else iso2022Decode k canon fuel (st.set tgt e.no) (if canon then some e.no else none) r
    | some (.char no ch single, r) =>
      if canon && (single || (pend.isSome && pend != no)) then none
      else (iso2022Decode k canon fuel st none r).map (ch :: ·)

/-- X.690 11.4 restricts 8.23.5: a canonical encoding is a basic one. -/
theorem iso2022Decode_canon (k : StrType) :
    ∀ fuel st pend bs cs, iso2022Decode k true fuel st pend bs = some cs →
      iso2022Decode k false fuel st none bs = some cs := by
  intro fuel
  induction fuel with
  | zero =>
    intro st pend bs cs h
    cases bs with
    | nil => simp [iso2022Decode] at h ⊢; exact h.2
    | cons b r => simp [iso2022Decode] at h
  | succ fuel ih =>
    intro st pend bs cs h
    cases bs with
    | nil => simp [iso2022Decode] at h ⊢; exact h.2
    | cons b rest =>
      simp only [iso2022Decode] at h ⊢
      split at h
      · simp at h
      · simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false] at h ⊢
        split at h
        · simp at h
        · exact ih _ _ _ _ h
      · simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false] at h ⊢
        split at h
        · simp at h
        · exact ih _ _ _ _ h
      · simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false] at h ⊢
        split at h
        · simp at h
        · simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨xs, hx, rfl⟩ := h
          exact ⟨xs, ih _ _ _ _ hx, rfl⟩

/-- X.690 8.23.5, 11.4: `os` encodes the characters `cs` of a value of type `k`, under clause 11's
restrictions if `canon`. -/
def Iso2022Enc (canon : Bool) (k : StrType) (cs : List RegChar) (os : Octets) : Prop :=
  iso2022Decode k canon (os.length + 1) (assumed k) none (os.map (·.val)) = some cs

end Asn1.X690
