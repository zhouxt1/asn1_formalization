import Asn1.X691.Field

/-!
# The encoding procedures (X.691 11.5–11.9)

These are the building blocks that clauses 12–32 invoke: whole numbers in four flavours, and the
length determinant with its fragmentation. The text gives each one as a procedure with no encoder
choice, so each one is a function here.

The bit-fields come from `nnbFn` and `tcMinFn`. `Asn1/Bits.lean` proves those are the unique fields
whose bits *sum to* the value, which is how 11.3 and 11.4 define them.
-/

namespace Asn1.X691

/-- 16K and 64K, as X.691 uses them (11.9). -/
def K16 : Nat := 16384
def K64 : Nat := 65536

/-- The result of a whole-number procedure: its field-list, and, in the indefinite length case,
the number of octets "len" that the invoking clause must encode as a length (11.5.7.4, 11.7.4,
11.8.3). -/
structure WholeEnc where
  fields : FieldList
  len : Option Nat
  deriving DecidableEq, Repr

/-- X.691 11.5: a constrained whole number `n`, with `lb ≤ n ≤ ub` from the PER-visible
constraints (11.5.2). -/
def constrainedWhole (v : Variant) (lb ub n : Int) : WholeEnc :=
  -- 11.5.3
  let range := (ub - lb + 1).toNat
  let off := (n - lb).toNat
  -- 11.5.4
  if range = 1 then ⟨[], none⟩
  -- 11.5.6: UNALIGNED, the minimum number of bits for the range
  else if !v.aligned then ⟨[.unaligned (nnbFn (bitsFor range) off)], none⟩
  -- 11.5.7.1: the bit-field case; its table is `bitsFor` (`table_11_5_7_1`)
  else if range ≤ 255 then ⟨[.unaligned (nnbFn (bitsFor range) off)], none⟩
  -- 11.5.7.2: the one-octet case
  else if range = 256 then ⟨[.aligned (nnbFn 8 off)], none⟩
  -- 11.5.7.3: the two-octet case
  else if range ≤ K64 then ⟨[.aligned (nnbFn 16 off)], none⟩
  -- 11.5.7.4: the indefinite length case
  else ⟨[.aligned (nnbMinFn off)], some (octetsFor off)⟩

/-- X.691 11.7: a semi-constrained whole number `n ≥ lb`. Always the indefinite length case (11.7.3). -/
def semiWhole (lb n : Int) : WholeEnc :=
  let off := (n - lb).toNat
  ⟨[.aligned (nnbMinFn off)], some (octetsFor off)⟩

/-- X.691 11.8: an unconstrained whole number. Always the indefinite length case (11.8.2). -/
def unconstrainedWhole (n : Int) : WholeEnc :=
  ⟨[.aligned (tcMinFn n)], some (tcOctetsFor n)⟩

/-! ## Length determinants (11.9) -/

/-- X.691 11.9.3.1: what the invoking clause found the length determinant to be. -/
inductive LenKind where
  /-- a) a normally small length, with lower bound one -/
  | normallySmall
  /-- b) and c): a constrained whole number. Whether `ub < 64K` decides between them. -/
  | constrained (lb ub : Nat)
  /-- c) a semi-constrained whole number -/
  | semi (lb : Nat)
  deriving DecidableEq, Repr

/-- The octets of a bit string whose length is a multiple of eight, in order. -/
def octetsOf (bs : Bits) : List Bits :=
  if _h : bs = [] then [] else bs.take 8 :: octetsOf (bs.drop 8)
termination_by bs.length
decreasing_by simp only [List.length_drop]; have := List.length_pos_of_ne_nil _h; omega

/-- X.691 11.9.2: the associated field or list of fields, as the list of units the length counts. -/
inductive Assoc where
  /-- 11.9.2 a), b), d): a single bit-field, given as its units: octets, single bits, or the
  characters of a known-multiplier character string. `aligned` is the alignment the invoking
  clause gave the field. -/
  | field (aligned : Bool) (units : List Bits)
  /-- 11.9.2 c): one field-list per component of a sequence-of or set-of -/
  | comps (cs : List FieldList)
  deriving DecidableEq, Repr

/-- "n": the length determinant's value (11.9.2). -/
def Assoc.count : Assoc → Nat
  | .field _ us => us.length
  | .comps cs => cs.length

/-- The associated field(s) themselves. -/
def Assoc.fields : Assoc → FieldList
  | .field al us => [if al then .aligned us.flatten else .unaligned us.flatten]
  | .comps cs => cs.flatten

/-- X.691 11.9.3.8.2: the first `m` units, appended as a fragment. A bit-field fragment is
octet-aligned in the ALIGNED variant, whatever the field's own alignment. -/
def Assoc.fragment (m : Nat) : Assoc → FieldList
  | .field _ us => [.aligned (us.take m).flatten]
  | .comps cs => (cs.take m).flatten

/-- X.691 11.9.3.8.3: the remaining part of the associated field(s). -/
def Assoc.rest (m : Nat) : Assoc → Assoc
  | .field al us => .field al (us.drop m)
  | .comps cs => .comps (cs.drop m)

@[simp] theorem Assoc.count_rest (a : Assoc) (m : Nat) : (a.rest m).count = a.count - m := by
  cases a <;> simp [Assoc.rest, Assoc.count]

/-- X.691 11.9.3.5–11.9.3.8.4: an unconstrained length "n" (or one with a large "ub"), and the
fragmentation procedure. The same in both variants (11.9.4.2). -/
def unconstrainedLength (a : Assoc) : FieldList :=
  let n := a.count
  -- 11.9.3.6: one octet, bit 8 zero
  if n ≤ 127 then .aligned (false :: nnbFn 7 n) :: a.fields
  -- 11.9.3.7: two octets, bits 8 and 7 of the first set to 1 and 0
  else if n < K16 then .aligned (true :: false :: nnbFn 14 n) :: a.fields
  -- 11.9.3.8: one octet, bits 8 and 7 set, and the multiplier 1 to 4 in bits 6 to 1.
  -- OPEN (ledger X691-3): the text encodes the multiplier "using the procedures of 11.8", the
  -- unconstrained (2's-complement) whole number, which has no fixed width. 11.3 is what fits.
  else
    -- 11.9.3.8.1: the largest multiplier such that at least "m" units remain
    let q := min 4 (n / K16)
    let m := q * K16
    .aligned (true :: true :: nnbFn 6 q) :: a.fragment m ++ unconstrainedLength (a.rest m)
termination_by a.count
decreasing_by
  simp only [Assoc.count_rest]
  have : 1 ≤ min 4 (a.count / K16) := by
    simp only [K16] at *; apply le_min (by norm_num); apply Nat.le_div_iff_mul_le (by norm_num) |>.2; omega
  have : K16 ≤ min 4 (a.count / K16) * K16 := by simpa using Nat.mul_le_mul_right K16 this
  simp only [K16] at *; omega

/-- X.691 11.9: add the associated field(s) to the field-list, preceded by a length determinant
of kind `k`. 11.9.1: the invoking clause does not call this when the length is fixed below 64K. -/
def lengthDet (v : Variant) (k : LenKind) (a : Assoc) : FieldList :=
  let n := a.count
  match k with
  | .constrained lb ub =>
    if ub < K64 then
      -- 11.9.3.3 (ALIGNED) and 11.9.4.1 (UNALIGNED): "n" as a constrained whole number, and
      -- nothing more when "n" is zero
      (constrainedWhole v lb ub n).fields ++ (if n = 0 then [] else a.fields)
    else
      -- 11.9.3.5, 11.9.4.2: a large "ub" is encoded as if it were absent
      unconstrainedLength a
  | .normallySmall =>
    -- 11.9.3.4, and 11.9.4.2 for UNALIGNED
    if n ≤ 64 then .unaligned [false] :: .unaligned (nnbFn 6 (n - 1)) :: a.fields
    else .unaligned [true] :: unconstrainedLength a
  | .semi _ => unconstrainedLength a

/-- X.691 11.6: a normally small non-negative whole number.

OPEN (ledger X691-4): 11.6.2 invokes 11.9 for a semi-constrained whole number, but does not say
which kind of length determinant (11.9.3.1) counts its octets. The only one that fits is an
unconstrained length in octets, and that is what implementations use. -/
def normallySmall (n : Nat) : FieldList :=
  if n ≤ 63 then [.unaligned [false], .unaligned (nnbFn 6 n)]
  else
    -- 11.7: the octets of the semi-constrained encoding with "lb" zero, octet-aligned in ALIGNED
    .unaligned [true] :: unconstrainedLength (.field true (octetsOf (nnbMinFn n)))

end Asn1.X691
