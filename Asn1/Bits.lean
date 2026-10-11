import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Bit strings and the integer encodings

X.691 11.3 and 11.4 define which bits *denote* a whole number. They do not say how to compute
the bits: a field is an encoding of `n` when its bits sum to `n`. This file states exactly that
(`nnbValue`, `tcValue`, and the `…In` predicates), then gives the executable encoders and proves that
they satisfy it. X.690 8.3 and X.696 10 use the same two sums.

Bits are `List Bool`, leading bit first, matching `Seq<bool>` on the Verus side.
-/

namespace Asn1

abbrev Bits := List Bool

/-! ## Non-negative-binary-integer (X.691 11.3) -/

/-- X.691 11.3.3–11.3.4: the whole number a field denotes. Bit `k`, counted from the trailing
bit, is worth `2^k` when set. Folding from the leading bit computes the same sum. -/
def nnbValue (bs : Bits) : Nat := bs.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- X.691 11.3.5: `bs` is a non-negative-binary-integer encoding of `n` in a field of `w` bits.
The NOTE to 11.3.5 says this has one solution when `n < 2^w` (`nnbIn_unique`). -/
def NnbIn (w n : Nat) (bs : Bits) : Prop := bs.length = w ∧ nnbValue bs = n

/-- X.691 11.3.6: a minimum octet non-negative-binary-integer encoding of `n`. The field is a
multiple of eight bits, and its leading eight bits are not all zero unless it is exactly eight bits.

OPEN (ledger X691-1): read literally, the condition is vacuous for an empty field, and an empty
field sums to 0, so 0 would have a zero-octet encoding. Every use (11.5.7.4, 11.7.4, 13.2.6) needs
at least one octet: 13.2.6 b) gives the length a lower bound of one, and X.690 8.3.1 requires one or
more contents octets. We require one or more octets. -/
def NnbMinOctets (n : Nat) (bs : Bits) : Prop :=
  bs.length % 8 = 0 ∧ 0 < bs.length ∧ nnbValue bs = n ∧
    (bs.length = 8 ∨ bs.take 8 ≠ List.replicate 8 false)

/-! ## 2's-complement-binary-integer (X.691 11.4) -/

/-- X.691 11.4.4: as `nnbValue`, except that the leading bit, if set, is worth `-2^k`. -/
def tcValue : Bits → Int
  | [] => 0
  | b :: rest => (if b then -(2 : Int) ^ rest.length else 0) + nnbValue rest

/-- X.691 11.4.6: a minimum octet 2's-complement-binary-integer encoding of `i`. The field is a
non-empty multiple of eight bits, and its leading nine bits are neither all zeros nor all ones.

OPEN (ledger X691-2): as in 11.3.6, the text does not say "non-empty", and an eight-bit field has
no nine leading bits. We take the condition to bind only when there are nine bits, and require at
least one octet (X.690 8.3.2 states the same rule over the first nine bits). -/
def TcMinOctets (i : Int) (bs : Bits) : Prop :=
  bs.length % 8 = 0 ∧ 0 < bs.length ∧ tcValue bs = i ∧
    (bs.length = 8 ∨
      (bs.take 9 ≠ List.replicate 9 false ∧ bs.take 9 ≠ List.replicate 9 true))

/-! ## Executable encoders -/

/-- The `w`-bit non-negative-binary-integer field for `n mod 2^w`, leading bit first. -/
def nnbFn : Nat → Nat → Bits
  | 0, _ => []
  | w + 1, n => nnbFn w (n / 2) ++ [n % 2 == 1]

/-- The minimum number of bits that represent every number below `range` (X.691 11.5.6 and
11.9.4.1). Zero bits for a range of one. -/
def bitsFor (range : Nat) : Nat := Nat.size (range - 1)

/-- The minimum number of octets for `n` as a non-negative-binary-integer (11.3.6): one octet for 0. -/
def octetsFor (n : Nat) : Nat := max 1 ((Nat.size n + 7) / 8)

/-- The minimum octet field for `n` (X.691 11.3.6). -/
def nnbMinFn (n : Nat) : Bits := nnbFn (8 * octetsFor n) n

/-- The minimum number of octets for `i` as a 2's-complement-binary-integer (11.4.6): enough
octets for the magnitude plus a sign bit. -/
def tcOctetsFor (i : Int) : Nat :=
  if 0 ≤ i then (Nat.size i.toNat + 8) / 8 else (Nat.size (-i - 1).toNat + 8) / 8

/-- The minimum octet 2's-complement field for `i` (X.691 11.4.6). -/
def tcMinFn (i : Int) : Bits :=
  let w := 8 * tcOctetsFor i
  nnbFn w (if 0 ≤ i then i.toNat else (2 ^ w + i).toNat)

/-! ## Facts about the sums -/

@[simp] theorem nnbValue_nil : nnbValue [] = 0 := rfl

theorem nnbValue_append_single (bs : Bits) (b : Bool) :
    nnbValue (bs ++ [b]) = 2 * nnbValue bs + b.toNat := by
  simp [nnbValue, List.foldl_append]

theorem nnbValue_cons (b : Bool) (bs : Bits) :
    nnbValue (b :: bs) = b.toNat * 2 ^ bs.length + nnbValue bs := by
  induction bs using List.reverseRecOn with
  | nil => simp [nnbValue]
  | append_singleton bs c ih =>
    rw [← List.cons_append, nnbValue_append_single, ih, nnbValue_append_single]
    simp [pow_succ]; ring

theorem nnbValue_lt (bs : Bits) : nnbValue bs < 2 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs b ih =>
    rw [nnbValue_append_single]; simp [pow_succ]
    cases b <;> simp <;> omega

@[simp] theorem nnbFn_length (w n : Nat) : (nnbFn w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [nnbFn, ih]

theorem nnbValue_nnbFn (w n : Nat) : nnbValue (nnbFn w n) = n % 2 ^ w := by
  induction w generalizing n with
  | zero => simp [nnbFn, Nat.mod_one]
  | succ w ih =>
    have h2 : (n % 2 == 1).toNat = n % 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    rw [nnbFn, nnbValue_append_single, ih, h2, pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mod_mul]
    ring

/-- `nnbFn` is the 11.3.5 encoding, whenever `n` fits. -/
theorem nnbFn_nnbIn {w n : Nat} (h : n < 2 ^ w) : NnbIn w n (nnbFn w n) :=
  ⟨nnbFn_length w n, by rw [nnbValue_nnbFn, Nat.mod_eq_of_lt h]⟩

/-- The NOTE to X.691 11.3.5: in a field of fixed size, the encoding is unique. -/
theorem nnbIn_unique {w n : Nat} {bs : Bits} (h : NnbIn w n bs) : bs = nnbFn w n := by
  obtain ⟨hl, hv⟩ := h
  subst hl hv
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton, nnbFn]
    rw [nnbValue_append_single]
    have hb : (2 * nnbValue bs + b.toNat) / 2 = nnbValue bs := by cases b <;> simp; omega
    have hm : ((2 * nnbValue bs + b.toNat) % 2 == 1) = b := by cases b <;> simp
    rw [hb, hm, ← ih]

/-- `bitsFor` is the minimum of 11.5.6: `range` values fit in `bitsFor range` bits, and in no fewer. -/
theorem bitsFor_spec {range m : Nat} (h : 0 < range) : range ≤ 2 ^ m ↔ bitsFor range ≤ m := by
  unfold bitsFor; rw [Nat.size_le]; omega

/-- The table of X.691 11.5.7.1 is `bitsFor`, for every range it lists. -/
theorem table_11_5_7_1 : ∀ r ∈ List.range' 2 254,
    bitsFor r = (if r ≤ 2 then 1 else if r ≤ 4 then 2 else if r ≤ 8 then 3 else if r ≤ 16 then 4
      else if r ≤ 32 then 5 else if r ≤ 64 then 6 else if r ≤ 128 then 7 else 8) := by
  decide +kernel

end Asn1

namespace Asn1

/-! ## Octets

X.690 works in octets; X.691 in bits. An octet is `Fin 256`, as in `Val.octets`, with bit 8 (the
most significant) leading when it becomes bits. -/

abbrev Octets := List (Fin 256)

/-- An octet's eight bits, bit 8 first. -/
def octetBits (o : Fin 256) : Bits := nnbFn 8 o.val

/-- Octets as bits, each octet bit 8 first (X.690 8.1.2–8.1.5 number bits 8 to 1). -/
def bitsOf (os : Octets) : Bits := os.flatMap octetBits

/-- The octet whose bits, bit 8 first, are the first eight of `bs` (missing bits are zero). -/
def octetOf (bs : Bits) : Fin 256 :=
  ⟨nnbValue (bs.take 8 ++ List.replicate (8 - (bs.take 8).length) false) % 256,
   Nat.mod_lt _ (by norm_num)⟩

/-- Bits as octets, the last octet filled with zero bits. -/
def bitsToOctets (bs : Bits) : Octets := go bs.length bs
where
  /-- structural on a bound on the number of octets, so that it reduces in the kernel -/
  go : Nat → Bits → Octets
    | 0, _ => []
    | _ + 1, [] => []
    | k + 1, bs@(_ :: _) => octetOf bs :: go k (bs.drop 8)

/-- A number below 256 as an octet. -/
def octet (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by norm_num)⟩

/-- The octets of a whole number as an unsigned binary number in `k` octets, most significant first
(X.690 8.1.3.5, 8.5.7.5). -/
def beOctets (k n : Nat) : Octets := bitsToOctets (nnbFn (8 * k) n)

end Asn1

/-! ## The executable encoders meet their definitions -/
namespace Asn1

theorem nnbFn_succ_cons (w n : Nat) : nnbFn (w + 1) n = (n / 2 ^ w % 2 == 1) :: nnbFn w n := by
  induction w generalizing n with
  | zero => simp [nnbFn]
  | succ w ih =>
    rw [nnbFn, ih (n / 2), nnbFn]
    simp [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem tcValue_eq (b : Bool) (rest : Bits) :
    tcValue (b :: rest) = (nnbValue (b :: rest) : Int) - (if b then 2 ^ (rest.length + 1) else 0) := by
  rw [tcValue, nnbValue_cons]; cases b <;> simp [pow_succ]; ring

theorem tcValue_nnbFn (w m : Nat) (h : m < 2 ^ (w + 1)) :
    tcValue (nnbFn (w + 1) m) = (m : Int) - (if 2 ^ w ≤ m then 2 ^ (w + 1) else 0) := by
  rw [nnbFn_succ_cons, tcValue_eq, ← nnbFn_succ_cons, nnbValue_nnbFn, Nat.mod_eq_of_lt h,
    nnbFn_length]
  have : (m / 2 ^ w % 2 == 1) = decide (2 ^ w ≤ m) := by
    have hq : m / 2 ^ w < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at h; linarith
    rcases Nat.lt_or_ge m (2 ^ w) with hm | hm
    · have : m / 2 ^ w = 0 := Nat.div_eq_of_lt hm
      simp [this, Nat.not_le.mpr hm]
    · have : m / 2 ^ w = 1 := by
        have : 1 ≤ m / 2 ^ w := (Nat.le_div_iff_mul_le (Nat.two_pow_pos w)).mpr (by simpa using hm)
        omega
      simp [this, hm]
  rw [this]; by_cases hm : 2 ^ w ≤ m <;> simp [hm]

end Asn1
namespace Asn1

theorem nnbFn_add (a b n : Nat) : nnbFn (a + b) n = nnbFn a (n / 2 ^ b) ++ nnbFn b n := by
  induction b generalizing n with
  | zero => simp [nnbFn]
  | succ b ih =>
    rw [← Nat.add_assoc, nnbFn, ih, nnbFn, List.append_assoc]
    simp [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The leading nine bits of a `w`-bit field, `w ≥ 9`, are those of `n / 2^(w-9)`. -/
theorem nnbFn_take9 (w n : Nat) (hw : 9 ≤ w) :
    (nnbFn w n).take 9 = nnbFn 9 (n / 2 ^ (w - 9)) := by
  have : w = 9 + (w - 9) := by omega
  rw [this, nnbFn_add]; simp

theorem nnbValue_replicate_false (k : Nat) : nnbValue (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', nnbValue_append_single, ih]; rfl

theorem nnbFn_eq_replicate_false {k n : Nat} (h : nnbFn k n = List.replicate k false) :
    n % 2 ^ k = 0 := by
  have := nnbValue_nnbFn k n
  rw [h, nnbValue_replicate_false] at this
  omega

theorem nnbFn_eq_replicate_true {k n : Nat} (h : nnbFn k n = List.replicate k true) :
    n % 2 ^ k = 2 ^ k - 1 := by
  have := nnbValue_nnbFn k n
  rw [h] at this
  have h1 : nnbValue (List.replicate k true) = 2 ^ k - 1 := by
    clear h this
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', nnbValue_append_single, ih]
      have := Nat.one_le_two_pow (n := k); simp [pow_succ]; omega
  omega

theorem tcOctetsFor_pos (i : Int) : 0 < tcOctetsFor i := by
  unfold tcOctetsFor; split <;> omega

/-- X.691 11.4.6, X.690 8.3: `tcMinFn i` is a minimum octet 2's-complement-binary-integer
encoding of `i`. -/
theorem tcMinFn_spec (i : Int) : TcMinOctets i (tcMinFn i) := by
  have hk := tcOctetsFor_pos i
  set k := tcOctetsFor i with hkdef
  obtain ⟨w, hw⟩ : ∃ w, 8 * k = w + 1 := ⟨8 * k - 1, by omega⟩
  have hlen : (tcMinFn i).length = 8 * k := by simp [tcMinFn, ← hkdef]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · -- the value
    unfold tcMinFn; simp only [← hkdef, hw]
    by_cases hi : 0 ≤ i
    · have hs : Nat.size i.toNat + 1 ≤ w + 1 := by
        have : k = (Nat.size i.toNat + 8) / 8 := by simp [hkdef, tcOctetsFor, hi]
        omega
      have hlt : i.toNat < 2 ^ w := by
        have := Nat.lt_size_self i.toNat
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp only [hi, ↓reduceIte]; rw [tcValue_nnbFn _ _ (by rw [pow_succ]; omega)]
      simp [Nat.not_le.mpr hlt]; omega
    · have hs : Nat.size (-i - 1).toNat + 1 ≤ w + 1 := by
        have : k = (Nat.size (-i - 1).toNat + 8) / 8 := by simp [hkdef, tcOctetsFor, hi]
        omega
      have hlt : (-i - 1).toNat < 2 ^ w := by
        have := Nat.lt_size_self (-i - 1).toNat
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hlt' : -i - 1 < ((2 ^ w : Nat) : Int) := by
        have := Int.toNat_of_nonneg (show 0 ≤ -i - 1 by omega)
        rw [← this]; exact_mod_cast hlt
      have hP : ((2 : Int) ^ (w + 1)) = 2 * ((2 ^ w : Nat) : Int) := by push_cast; ring
      have hm : ((2 ^ (w + 1) + i).toNat : Int) = 2 * ((2 ^ w : Nat) : Int) + i := by
        rw [Int.toNat_of_nonneg (by rw [hP]; omega), hP]
      have hb : (2 ^ (w + 1) + i).toNat < 2 ^ (w + 1) := by
        zify; rw [hm, hP]; omega
      simp only [hi, ↓reduceIte]; rw [tcValue_nnbFn _ _ hb]
      have hge : 2 ^ w ≤ (2 ^ (w + 1) + i).toNat := by zify; rw [hm]; omega
      simp only [hge, ite_true]
      rw [hm]; push_cast; ring
  · -- the leading nine bits
    by_cases h8 : 8 * k = 8
    · left; omega
    · right
      have h9 : 9 ≤ 8 * k := by omega
      obtain ⟨v, hv⟩ : ∃ v, 8 * k = v + 9 := ⟨8 * k - 9, by omega⟩
      set M := (if 0 ≤ i then i.toNat else (2 ^ (8 * k) + i).toNat) with hM
      have htake : (tcMinFn i).take 9 = nnbFn 9 (M / 2 ^ v) := by
        unfold tcMinFn; simp only [← hkdef]; rw [nnbFn_take9 _ _ h9, show 8 * k - 9 = v by omega]
      -- the field's value and the size bounds the minimum octet count gives
      have hP : (2 : Nat) ^ (8 * k) = 512 * 2 ^ v := by rw [hv, pow_add]; ring
      have hd : 0 < 2 ^ v := Nat.two_pow_pos v
      have hsize : ∀ j : Nat, k = (Nat.size j + 8) / 8 → 2 ^ v ≤ j := by
        intro j hj
        by_contra hlt
        have : Nat.size j ≤ v := Nat.size_le.mpr (by omega)
        omega
      rw [htake]
      by_cases hi : 0 ≤ i
      · have hMv : M = i.toNat := by simp [hM, hi]
        have hk' : k = (Nat.size i.toNat + 8) / 8 := by simp [hkdef, tcOctetsFor, hi]
        have hge := hsize _ hk'
        have hlt : i.toNat < 2 ^ (8 * k - 1) := by
          have := Nat.lt_size_self i.toNat
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hlt' : i.toNat < 256 * 2 ^ v := by
          have : 2 ^ (8 * k - 1) = 256 * 2 ^ v := by
            rw [show 8 * k - 1 = 8 + v by omega, pow_add]; norm_num
          omega
        constructor
        · intro hz
          have hz := nnbFn_eq_replicate_false hz
          have : M / 2 ^ v < 2 ^ 9 := by
            rw [Nat.div_lt_iff_lt_mul hd]; norm_num; omega
          have h0 : M / 2 ^ v = 0 := by rw [Nat.mod_eq_of_lt this] at hz; exact hz
          rw [Nat.div_eq_zero_iff_lt hd] at h0
          omega
        · intro ho
          have ho := nnbFn_eq_replicate_true ho
          have : M / 2 ^ v < 2 ^ 9 := by
            rw [Nat.div_lt_iff_lt_mul hd]; norm_num; omega
          rw [Nat.mod_eq_of_lt this] at ho
          have : 511 * 2 ^ v ≤ M := by
            have := (Nat.le_div_iff_mul_le hd).mp (show 511 ≤ M / 2 ^ v by norm_num at ho; omega)
            exact this
          omega
      · have hk' : k = (Nat.size (-i - 1).toNat + 8) / 8 := by simp [hkdef, tcOctetsFor, hi]
        have hge := hsize _ hk'
        have hj : ((-i - 1).toNat : Int) = -i - 1 := Int.toNat_of_nonneg (by omega)
        have hlt : (-i - 1).toNat < 256 * 2 ^ v := by
          have := Nat.lt_size_self (-i - 1).toNat
          have : 2 ^ (Nat.size (-i - 1).toNat) ≤ 256 * 2 ^ v := by
            have : 256 * 2 ^ v = 2 ^ (8 + v) := by rw [pow_add]; norm_num
            rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hlt' : -i - 1 < 256 * (2 : Int) ^ v := by
          have := hlt; zify at this; rw [hj] at this; exact_mod_cast this
        have h2 : (2 : Int) ^ (8 * k) = 512 * 2 ^ v := by rw [hv, pow_add]; norm_num; ring
        have hMv : (M : Int) = 512 * 2 ^ v + i := by
          simp only [hM, hi, ite_false]
          rw [Int.toNat_of_nonneg (by rw [h2]; omega), h2]
        constructor
        · intro hz
          have hz := nnbFn_eq_replicate_false hz
          have hMlt : M < 512 * 2 ^ v := by zify; rw [hMv]; omega
          have : M / 2 ^ v < 2 ^ 9 := by
            rw [Nat.div_lt_iff_lt_mul hd]; norm_num; omega
          have h0 : M / 2 ^ v = 0 := by rw [Nat.mod_eq_of_lt this] at hz; exact hz
          rw [Nat.div_eq_zero_iff_lt hd] at h0
          zify at h0 hlt; rw [hMv] at h0; omega
        · intro ho
          have ho := nnbFn_eq_replicate_true ho
          have hMlt : M < 512 * 2 ^ v := by zify; rw [hMv]; omega
          have : M / 2 ^ v < 2 ^ 9 := by
            rw [Nat.div_lt_iff_lt_mul hd]; norm_num; omega
          rw [Nat.mod_eq_of_lt this] at ho
          have : 511 * 2 ^ v ≤ M :=
            (Nat.le_div_iff_mul_le hd).mp (show 511 ≤ M / 2 ^ v by norm_num at ho; omega)
          zify at this hge; rw [hMv] at this; rw [hj] at hge; omega

end Asn1
namespace Asn1

/-- Eight bits make an octet and back. -/
theorem octetBits_octetOf {bs : Bits} (h : 8 ≤ bs.length) : octetBits (octetOf bs) = bs.take 8 := by
  have hl : (bs.take 8).length = 8 := by simp; omega
  have hv : nnbValue (bs.take 8) < 256 := by have := nnbValue_lt (bs.take 8); rw [hl] at this; simpa using this
  unfold octetBits octetOf
  simp only [hl, Nat.sub_self, List.replicate_zero, List.append_nil, Nat.mod_eq_of_lt hv]
  exact (nnbIn_unique ⟨hl, rfl⟩).symm

theorem bitsOf_go (k : Nat) (bs : Bits) (hk : bs.length ≤ 8 * k) (h8 : bs.length % 8 = 0) :
    bitsOf (bitsToOctets.go k bs) = bs := by
  induction k generalizing bs with
  | zero => have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst this; rfl
  | succ k ih =>
    match bs, hk, h8 with
    | [], _, _ => rfl
    | b :: bs', hk, h8 =>
      have hl : 8 ≤ (b :: bs').length := by
        have : 0 < (b :: bs').length := by simp
        omega
      have hd1 : ((b :: bs').drop 8).length ≤ 8 * k := by
        rw [List.length_drop]; omega
      have hd2 : ((b :: bs').drop 8).length % 8 = 0 := by
        rw [List.length_drop]; omega
      have := ih ((b :: bs').drop 8) hd1 hd2
      unfold bitsOf at this ⊢
      rw [bitsToOctets.go, List.flatMap_cons, this, octetBits_octetOf hl, List.take_append_drop]

/-- Bits that fill whole octets survive the round trip through octets. -/
theorem bitsOf_bitsToOctets (bs : Bits) (h8 : bs.length % 8 = 0) : bitsOf (bitsToOctets bs) = bs :=
  bitsOf_go _ _ (by omega) h8

theorem bitsOf_length (os : Octets) : (bitsOf os).length = 8 * os.length := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [bitsOf, octetBits] at *; rw [ih]; ring

theorem bitsToOctets_length {bs : Bits} (h : bs.length % 8 = 0) :
    (bitsToOctets bs).length = bs.length / 8 := by
  have := congrArg List.length (bitsOf_bitsToOctets bs h)
  rw [bitsOf_length] at this; omega

theorem tcMinFn_length (i : Int) : (tcMinFn i).length = 8 * tcOctetsFor i := by simp [tcMinFn]
end Asn1
