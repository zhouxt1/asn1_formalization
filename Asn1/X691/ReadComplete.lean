import Asn1.X691.Decode
import Asn1.X690.DecSound

/-!
# The PER readers read back what the procedures lay out

For the completeness of the decoder: each reader of `Decode.lean`, run on the bits that a
procedure of clause 11 lays out (`layout`) followed by anything, returns the value laid out and
leaves the rest. `Reads m pos bits a` says it for a reader `m` started `pos` bits into the
encoding.
-/

namespace Asn1.X691

open Asn1.X680

/-- `m`, started `pos` bits into an encoding, reads exactly `bits` and returns `a`. -/
def Reads {α : Type} (m : PM α) (pos : Nat) (bits : Bits) (a : α) : Prop :=
  ∀ rest, m.run ⟨pos, bits ++ rest⟩ = .ok (a, ⟨pos + bits.length, rest⟩)

theorem Reads.pure {α : Type} (a : α) (pos : Nat) : Reads (Pure.pure a : PM α) pos [] a := by
  intro rest; simp [Reads, StateT.run, Pure.pure, StateT.pure, Except.pure]

theorem Reads.bind {α β : Type} {m : PM α} {f : α → PM β} {pos : Nat} {b1 b2 : Bits} {a : α} {c : β}
    (h1 : Reads m pos b1 a) (h2 : Reads (f a) (pos + b1.length) b2 c) :
    Reads (m >>= f) pos (b1 ++ b2) c := by
  intro rest
  have e1 := h1 (b2 ++ rest)
  have e2 := h2 rest
  simp only [StateT.run] at e1 e2 ⊢
  show (StateT.bind m f) _ = _
  simp only [StateT.bind, List.append_assoc, e1]
  show f a _ = _
  rw [e2, Nat.add_assoc, List.length_append]

theorem Reads.bind' {α β : Type} {m : PM α} {f : α → PM β} {pos : Nat} {b1 b2 bits : Bits} {a : α} {c : β}
    (h1 : Reads m pos b1 a) (h2 : Reads (f a) (pos + b1.length) b2 c) (he : bits = b1 ++ b2) :
    Reads (m >>= f) pos bits c := he ▸ h1.bind h2

theorem Reads.congr {α : Type} {m : PM α} {pos : Nat} {b b' : Bits} {a : α} (h : Reads m pos b a)
    (e : b = b') : Reads m pos b' a := e ▸ h

theorem takeN_reads (pos : Nat) (bs : Bits) : Reads (takeN bs.length) pos bs bs := by
  intro rest
  simp [takeN, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, Pure.pure, StateT.pure, Except.bind, Except.pure, List.take_left',
    List.drop_left']

/-- The padding before an octet-aligned field `pos` bits into an encoding (11.1.4). -/
def padOf (v : Variant) (pos : Nat) : Nat := if v.aligned then (8 - pos % 8) % 8 else 0

theorem alignR_reads (v : Variant) (pos : Nat) :
    Reads (alignR v) pos (List.replicate (padOf v pos) false) () := by
  intro rest
  unfold alignR padOf
  cases hv : v.aligned
  · simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
  · have h := takeN_reads pos (List.replicate ((8 - pos % 8) % 8) false) rest
    simp only [List.length_replicate] at h
    simp only [ite_true, StateT.run] at h ⊢
    show (StateT.bind get fun r => discard (takeN ((8 - r.pos % 8) % 8))) _ = _
    simp only [StateT.bind]
    show (discard (takeN ((8 - pos % 8) % 8))) _ = _
    simp only [discard, Functor.discard, Functor.mapConst, StateT.map]
    show StateT.map (Function.const Bits ()) (takeN ((8 - pos % 8) % 8)) _ = _
    simp only [StateT.map, h, List.length_replicate]
    rfl

/-! ## Layout -/

theorem layout_append (al : Bool) : ∀ (p : Nat) (f1 f2 : FieldList),
    layout al p (f1 ++ f2) = layout al p f1 ++ layout al (p + (layout al p f1).length) f2
  | p, [], f2 => by simp [layout]
  | p, .unaligned bs :: fs, f2 => by
    simp only [List.cons_append, layout, layout_append al (p + bs.length) fs f2, List.append_assoc,
      List.length_append, Nat.add_assoc]
  | p, .aligned bs :: fs, f2 => by
    simp only [List.cons_append, layout, layout_append al _ fs f2, List.append_assoc,
      List.length_append, List.length_replicate, Nat.add_assoc]

@[simp] theorem layout_nil (al : Bool) (p : Nat) : layout al p [] = [] := rfl

theorem layout_unaligned (al : Bool) (p : Nat) (bs : Bits) : layout al p [.unaligned bs] = bs := by
  simp [layout]

theorem layout_aligned (v : Variant) (p : Nat) (bs : Bits) :
    layout v.aligned p [.aligned bs] = List.replicate (padOf v p) false ++ bs := by
  simp [layout, padOf]

theorem fieldR_reads (v : Variant) (al : Bool) (p : Nat) (bs : Bits) :
    Reads (fieldR v al bs.length) p
      (layout v.aligned p [if al then .aligned bs else .unaligned bs]) bs := by
  cases al
  · simp only [fieldR, Bool.false_eq_true, ↓reduceIte, layout_unaligned]
    have := (Reads.pure () p).bind (f := fun _ => takeN bs.length) (takeN_reads (p + 0) bs)
    simpa using this
  · simp only [fieldR, ↓reduceIte, layout_aligned]
    exact (alignR_reads v p).bind (by simpa using takeN_reads _ bs)

/-! ## Whole numbers (11.5) -/

theorem Reads.map_pure {α β : Type} {m : PM α} {g : α → β} {p : Nat} {b : Bits} {a : α}
    (h : Reads m p b a) : Reads (m >>= fun x => Pure.pure (g x)) p b (g a) := by
  have := h.bind (f := fun x => (Pure.pure (g x) : PM β)) (Reads.pure (g a) _)
  simpa using this

theorem off_lt_pow {range off : Nat} (h : off < range) : off < 2 ^ bitsFor range := by
  have := (bitsFor_spec (range := range) (m := bitsFor range) (by omega)).2 le_rfl
  omega

theorem nnbValue_nnbFn_of_lt {w off : Nat} (h : off < 2 ^ w) : nnbValue (nnbFn w off) = off := by
  rw [nnbValue_nnbFn, Nat.mod_eq_of_lt h]

theorem nnbFn_length : ∀ (w n : Nat), (nnbFn w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [nnbFn, nnbFn_length w]

theorem wholeR_reads (v : Variant) (p : Nat) {lb ub i : Int} (hl : lb ≤ i) (hu : i ≤ ub)
    (hr : v.aligned = false ∨ (ub - lb + 1).toNat ≤ K64) :
    Reads (wholeR v lb ub) p (layout v.aligned p (constrainedWhole v lb ub i).fields) i := by
  have hoff : (i - lb).toNat < (ub - lb + 1).toNat := by omega
  have hval : lb + ((nnbValue (nnbFn (bitsFor (ub - lb + 1).toNat) (i - lb).toNat) : Nat) : Int) = i := by
    rw [nnbValue_nnbFn_of_lt (off_lt_pow hoff)]; omega
  unfold wholeR constrainedWhole
  by_cases h1 : (ub - lb + 1).toNat = 1
  · simp only [h1, ↓reduceIte, layout_nil]
    have : i = lb := by omega
    subst this; exact Reads.pure _ _
  simp only [h1, ↓reduceIte]
  cases hv : v.aligned
  · simp only [Bool.not_false, ↓reduceIte, layout_unaligned]
    have := (takeN_reads p (nnbFn (bitsFor (ub - lb + 1).toNat) (i - lb).toNat)).map_pure
      (g := fun x => lb + (nnbValue x : Int))
    rw [nnbFn_length] at this
    simpa [hval] using this
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (ub - lb + 1).toNat ≤ 255
    · simp only [h2, ↓reduceIte, layout_unaligned]
      have := (takeN_reads p (nnbFn (bitsFor (ub - lb + 1).toNat) (i - lb).toNat)).map_pure
        (g := fun x => lb + (nnbValue x : Int))
      rw [nnbFn_length] at this
      simpa [hval] using this
    simp only [h2, ↓reduceIte]
    by_cases h3 : (ub - lb + 1).toNat = 256
    · simp only [h3, ↓reduceIte]
      have := (fieldR_reads v true p (nnbFn 8 (i - lb).toNat)).map_pure (g := fun x => lb + (nnbValue x : Int))
      rw [nnbFn_length, hv] at this
      simp only [↓reduceIte] at this
      rw [nnbValue_nnbFn_of_lt (by omega)] at this
      have e : lb + ((i - lb).toNat : Int) = i := by omega
      rw [e] at this; exact this
    simp only [h3, ↓reduceIte]
    have h4 : (ub - lb + 1).toNat ≤ K64 := by rcases hr with h | h <;> simp_all
    simp only [h4, ↓reduceIte]
    have := (fieldR_reads v true p (nnbFn 16 (i - lb).toNat)).map_pure (g := fun x => lb + (nnbValue x : Int))
    rw [nnbFn_length, hv] at this
    simp only [↓reduceIte] at this
    rw [nnbValue_nnbFn_of_lt (by simp only [K64] at h4; omega)] at this
    have e : lb + ((i - lb).toNat : Int) = i := by omega
    rw [e] at this; exact this

/-! ## Unconstrained lengths and fragments (11.9.3.5–11.9.3.8) -/

/-- What a length determinant counts, as the decoder reads it: items of type `α`, the `Assoc` they
make (11.9.2), and its fields. -/
structure AView (α : Type) where
  A : Bool → List α → Assoc
  F : Bool → List α → FieldList
  count : ∀ al ys, (A al ys).count = ys.length
  fields : ∀ al ys, (A al ys).fields = F al ys
  frag : ∀ al ys m, (A al ys).fragment m = F true (ys.take m)
  rest : ∀ al ys m, (A al ys).rest m = A al (ys.drop m)

/-- Units of a bit-field (11.9.2 a), b), d)). -/
def fieldView : AView Bits where
  A al us := .field al us
  F al us := [if al then .aligned us.flatten else .unaligned us.flatten]
  count _ _ := rfl
  fields _ _ := rfl
  frag _ _ _ := rfl
  rest _ _ _ := rfl

/-- Components (11.9.2 c)), with their values. -/
def compsView : AView (Val × FieldList) where
  A _ xs := .comps (xs.map (·.2))
  F _ xs := (xs.map (·.2)).flatten
  count _ _ := by simp [Assoc.count]
  fields _ _ := rfl
  frag _ ys m := by simp [Assoc.fragment, List.map_take]
  rest _ ys m := by simp [Assoc.rest, List.map_drop]

theorem unconstrainedLength_small (a : Assoc) (h : a.count ≤ 127) :
    unconstrainedLength a = .aligned (false :: nnbFn 7 a.count) :: a.fields := by
  rw [unconstrainedLength]; simp [h]

theorem unconstrainedLength_mid (a : Assoc) (h1 : ¬ a.count ≤ 127) (h2 : a.count < K16) :
    unconstrainedLength a = .aligned (true :: false :: nnbFn 14 a.count) :: a.fields := by
  rw [unconstrainedLength]; simp [h1, h2]

theorem unconstrainedLength_big (a : Assoc) (h : K16 ≤ a.count) :
    unconstrainedLength a = .aligned (true :: true :: nnbFn 6 (min 4 (a.count / K16))) ::
      a.fragment (min 4 (a.count / K16) * K16) ++ unconstrainedLength (a.rest (min 4 (a.count / K16) * K16)) := by
  rw [unconstrainedLength]
  have h1 : ¬ a.count ≤ 127 := by simp only [K16] at h; omega
  have h2 : ¬ a.count < K16 := by omega
  simp [h1, h2]

theorem fieldR8_reads (v : Variant) (p : Nat) (b : Bits) (hb : b.length = 8) :
    Reads (fieldR v true 8) p (layout v.aligned p [.aligned b]) b := by
  have := fieldR_reads v true p b
  rw [hb] at this; simpa using this

theorem layout_cons_aligned (v : Variant) (p : Nat) (b : Bits) (F : FieldList) :
    layout v.aligned p (.aligned b :: F) =
      layout v.aligned p [.aligned b] ++ layout v.aligned (p + (layout v.aligned p [.aligned b]).length) F := by
  have := layout_append v.aligned p [.aligned b] F
  simpa using this

theorem ulR_reads {α : Type} (v : Variant) (V : AView α) (readK : Bool → Nat → PM (List α)) (xs : List α)
    (hk : ∀ (al' : Bool) (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads (readK al' ys.length) p (layout v.aligned p (V.F al' ys)) ys) :
    ∀ (f : Nat) (al : Bool) (ys : List α), (∀ y ∈ ys, y ∈ xs) → ys.length / K16 < f → ∀ p,
      Reads (ulR v readK al f) p (layout v.aligned p (unconstrainedLength (V.A al ys))) ys
  | 0, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, al, ys, hys, hf, p => by
    have hc := V.count al ys
    by_cases h1 : ys.length ≤ 127
    · rw [unconstrainedLength_small _ (by omega), V.fields, hc, layout_cons_aligned]
      refine Reads.bind (fieldR8_reads v p _ (by simp [nnbFn_length])) ?_
      show Reads (readK al (nnbValue (nnbFn 7 ys.length))) _ _ _
      rw [nnbValue_nnbFn_of_lt (by omega)]
      exact hk al ys hys _
    by_cases h2 : ys.length < K16
    · rw [unconstrainedLength_mid _ (by omega) (by omega), V.fields, hc, layout_cons_aligned]
      have hn := nnbFn_length 14 ys.length
      set b := nnbFn 14 ys.length with hb
      have e : layout v.aligned p [.aligned (true :: false :: b)] =
          layout v.aligned p [.aligned (true :: false :: b.take 6)] ++ b.drop 6 := by
        simp only [layout_aligned, List.append_assoc, List.cons_append]
        rw [← List.take_append_drop 6 b]; simp
      rw [e, List.append_assoc]
      refine Reads.bind (fieldR8_reads v p _ (by simp [hn])) ?_
      show Reads (takeN 8 >>= fun o2 => readK al (nnbValue (b.take 6 ++ o2))) _ _ _
      have h8 : (b.drop 6).length = 8 := by simp [hn]
      refine Reads.bind (h8 ▸ takeN_reads _ (b.drop 6)) ?_
      rw [List.take_append_drop, hb, nnbValue_nnbFn_of_lt (by simp only [K16] at h2; omega)]
      have := hk al ys hys (p + (layout v.aligned p [.aligned (true :: false :: (nnbFn 14 ys.length).take 6)] ++
        (nnbFn 14 ys.length).drop 6).length)
      simpa [Nat.add_assoc] using this
    · have hq1 : 1 ≤ min 4 (ys.length / K16) := by
        apply le_min (by norm_num); apply Nat.le_div_iff_mul_le (by simp [K16]) |>.2; omega
      have hq4 : min 4 (ys.length / K16) ≤ 4 := min_le_left _ _
      have hqn : min 4 (ys.length / K16) * K16 ≤ ys.length :=
        le_trans (Nat.mul_le_mul_right _ (min_le_right _ _)) (Nat.div_mul_le_self _ _)
      rw [unconstrainedLength_big _ (by omega), hc, V.frag, V.rest, List.cons_append, layout_cons_aligned]
      set q := min 4 (ys.length / K16) with hq
      refine Reads.bind (fieldR8_reads v p _ (by simp [nnbFn_length])) ?_
      dsimp only
      have hv : nnbValue (List.drop 2 (true :: true :: nnbFn 6 q)) = q := by
        simp only [List.drop_succ_cons, List.drop_zero]; exact nnbValue_nnbFn_of_lt (by omega)
      rw [hv]
      have hc' : (decide (q < 1) || decide (q > 4)) = false := by simp; omega
      rw [hc']; simp only [Bool.false_eq_true, ↓reduceIte]
      set p' := p + (layout v.aligned p [Field.aligned (true :: true :: nnbFn 6 q)]).length
      rw [layout_append]
      have htk : (ys.take (q * K16)).length = q * K16 := by simp; omega
      have h1 := hk true (ys.take (q * K16)) (fun y hy => hys y (List.mem_of_mem_take hy)) p'
      rw [htk] at h1
      refine Reads.bind h1 ?_
      have h2 := ulR_reads v V readK xs hk f al (ys.drop (q * K16))
        (fun y hy => hys y (List.mem_of_mem_drop hy)) (by
          simp only [List.length_drop]
          have : (ys.length - q * K16) / K16 = ys.length / K16 - q := by
            rw [Nat.mul_comm q K16, Nat.sub_mul_div]
          rw [this]; omega) (p' + (layout v.aligned p' (V.F true (List.take (q * K16) ys))).length)
      have h3 := h2.bind (Reads.pure (ys.take (q * K16) ++ ys.drop (q * K16)) _)
        (f := fun more => (Pure.pure (ys.take (q * K16) ++ more) : PM (List α)))
      simpa using h3

theorem bitR_reads (p : Nat) (b : Bool) : Reads bitR p [b] b := by
  unfold bitR
  have := (takeN_reads p [b]).map_pure (g := fun bs => bs.headD false)
  simpa using this

theorem layout_cons_unaligned (al : Bool) (p : Nat) (b : Bits) (F : FieldList) :
    layout al p (.unaligned b :: F) = b ++ layout al (p + b.length) F := rfl

/-! ## Units and length determinants (11.9) -/

theorem chunks_flatten (w : Nat) : ∀ (us : List Bits), (∀ u ∈ us, u.length = w) →
    chunks w us.length us.flatten = us
  | [], _ => rfl
  | u :: us, h => by
    have hu := h u (by simp)
    simp only [List.length_cons, chunks, List.flatten_cons]
    rw [← hu, List.take_left', List.drop_left', chunks_flatten u.length us (fun x hx => (h x (by simp [hx])).trans hu.symm)]
    all_goals rfl

theorem flatten_length_of (w : Nat) : ∀ (us : List Bits), (∀ u ∈ us, u.length = w) →
    us.flatten.length = w * us.length
  | [], _ => by simp
  | u :: us, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      flatten_length_of w us (fun x hx => h x (by simp [hx])), h u (by simp)]
    ring

theorem unitsR_reads (v : Variant) (w : Nat) (al : Bool) (p : Nat) (us : List Bits)
    (h : ∀ u ∈ us, u.length = w) :
    Reads (unitsR v w al us.length) p (layout v.aligned p (fieldView.F al us)) us := by
  unfold unitsR
  have := (fieldR_reads v al p us.flatten).map_pure (g := chunks w us.length)
  rw [flatten_length_of w us h, chunks_flatten w us h] at this
  cases al <;> simpa [fieldView] using this

/-- The count a constrained length determinant below 64K can carry. -/
def LenKind.CountOk : LenKind → Nat → Prop
  | .constrained lb ub, n => ub < K64 → lb ≤ n ∧ n ≤ ub
  | _, _ => True

/-- The length determinants that may be unconstrained lengths, which `ulR` reads with fuel. -/
def LenKind.usesUL : LenKind → Prop
  | .constrained _ ub => K64 ≤ ub
  | _ => True

theorem lenDetR_reads {α : Type} (v : Variant) (V : AView α) (readK : Bool → Nat → PM (List α))
    (xs : List α)
    (hk : ∀ (al' : Bool) (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads (readK al' ys.length) p (layout v.aligned p (V.F al' ys)) ys)
    (k : LenKind) (al : Bool) (fuel : Nat) (hf : k.usesUL → xs.length / K16 < fuel)
    (hlen : k.CountOk xs.length)
    (hns : k = .normallySmall → 1 ≤ xs.length) (p : Nat) :
    Reads (lenDetR v k readK al fuel) p (layout v.aligned p (lengthDet v k (V.A al xs))) xs := by
  have hc := V.count al xs
  have hul := fun hu => ulR_reads v V readK xs hk fuel al xs (fun _ h => h) (hf hu)
  cases k with
  | constrained lb ub =>
    simp only [lenDetR, lengthDet, hc]
    by_cases hu : ub < K64
    · obtain ⟨hl1, hl2⟩ := (show ub < K64 → lb ≤ xs.length ∧ xs.length ≤ ub from hlen) hu
      simp only [hu, ↓reduceIte, layout_append]
      have hw := wholeR_reads v p (lb := lb) (ub := ub) (i := xs.length) (by omega) (by omega)
        (Or.inr (by simp only [K64] at hu ⊢; omega))
      refine Reads.bind hw ?_
      by_cases h0 : xs.length = 0
      · have : xs = [] := List.eq_nil_of_length_eq_zero h0
        subst this; simpa using Reads.pure ([] : List α) _
      · simp only [Int.toNat_natCast, h0, ↓reduceIte, V.fields]
        exact hk al xs (fun _ h => h) _
    · simp only [hu, ↓reduceIte]; exact hul (by simp [LenKind.usesUL]; omega) p
  | normallySmall =>
    simp only [lenDetR, lengthDet, hc]
    have h1 := hns rfl
    by_cases h64 : xs.length ≤ 64
    · simp only [h64, ↓reduceIte, layout_cons_unaligned, V.fields]
      refine Reads.bind (bitR_reads p false) ?_
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_singleton]
      have h6 := nnbFn_length 6 (xs.length - 1)
      refine Reads.bind (h6 ▸ takeN_reads _ (nnbFn 6 (xs.length - 1))) ?_
      rw [nnbValue_nnbFn_of_lt (by omega), show xs.length - 1 + 1 = xs.length by omega, h6]
      exact hk al xs (fun _ h => h) _
    · simp only [h64, ↓reduceIte, layout_cons_unaligned]
      refine Reads.bind (bitR_reads p true) ?_
      simpa using hul trivial _
  | semi lb => simp only [lenDetR, lengthDet]; exact hul trivial p

theorem ul_layout_len {α : Type} (v : Variant) (V : AView α) :
    ∀ (N : Nat) (al : Bool) (ys : List α) (p : Nat), ys.length / K16 < N →
      ys.length / K16 ≤ (layout v.aligned p (unconstrainedLength (V.A al ys))).length
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, al, ys, p, h => by
    have hc := V.count al ys
    by_cases h1 : ys.length < K16
    · rw [Nat.div_eq_of_lt h1]; exact Nat.zero_le _
    have hq1 : 1 ≤ min 4 (ys.length / K16) := by
      apply le_min (by norm_num); apply Nat.le_div_iff_mul_le (by simp [K16]) |>.2; omega
    have hqn : min 4 (ys.length / K16) * K16 ≤ ys.length :=
      le_trans (Nat.mul_le_mul_right _ (min_le_right _ _)) (Nat.div_mul_le_self _ _)
    rw [unconstrainedLength_big _ (by omega), hc, V.frag, V.rest, List.cons_append, layout_cons_aligned,
      layout_append]
    set q := min 4 (ys.length / K16)
    have hdiv : (ys.drop (q * K16)).length / K16 = ys.length / K16 - q := by
      simp only [List.length_drop]; rw [Nat.mul_comm q K16, Nat.sub_mul_div]
    have ih := ul_layout_len v V N al (ys.drop (q * K16)) (p + (layout v.aligned p [Field.aligned (true :: true :: nnbFn 6 q)]).length +
      (layout v.aligned (p + (layout v.aligned p [Field.aligned (true :: true :: nnbFn 6 q)]).length) (V.F true (List.take (q * K16) ys))).length) (by omega)
    have h8 : 8 ≤ (layout v.aligned p [Field.aligned (true :: true :: nnbFn 6 q)]).length := by
      rw [layout_aligned]; simp [nnbFn_length]
    simp only [List.length_append] at ih ⊢
    have : q ≤ 4 := min_le_left _ _
    omega

theorem fragFuel_bind {α : Type} {m : Nat → PM α} {p : Nat} {bits : Bits} {a : α}
    (h : ∀ f, bits.length < f → Reads (m f) p bits a) : Reads (fragFuel >>= m) p bits a := by
  intro rest
  have := h ((bits ++ rest).length + 1) (by simp) rest
  show (StateT.bind fragFuel m) _ = _
  simp only [StateT.bind, fragFuel]
  exact this

theorem lenDetF_reads {α : Type} (v : Variant) (V : AView α) (readK : Bool → Nat → PM (List α))
    (xs : List α)
    (hk : ∀ (al' : Bool) (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads (readK al' ys.length) p (layout v.aligned p (V.F al' ys)) ys)
    (k : LenKind) (al : Bool)
    (hlen : k.CountOk xs.length)
    (hns : k = .normallySmall → 1 ≤ xs.length) (p : Nat) :
    Reads (fragFuel >>= lenDetR v k readK al) p (layout v.aligned p (lengthDet v k (V.A al xs))) xs := by
  apply fragFuel_bind
  intro f hf
  apply lenDetR_reads v V readK xs hk k al f _ hlen hns p
  intro hu
  have hul := ul_layout_len v V (xs.length / K16 + 1) al xs
  cases k with
  | constrained lb ub =>
    simp only [LenKind.usesUL] at hu
    simp only [lengthDet, show ¬ ub < K64 by omega, ↓reduceIte] at hf
    have := hul p (by omega); omega
  | normallySmall =>
    by_cases h64 : (V.A al xs).count ≤ 64
    · rw [V.count] at h64
      have : xs.length / K16 = 0 := Nat.div_eq_of_lt (by simp only [K16]; omega)
      omega
    · simp only [lengthDet, h64, ↓reduceIte, layout_cons_unaligned, List.length_append] at hf
      rw [V.count] at h64
      have := hul (p + [true].length) (by omega)
      simp only [List.length_singleton] at hf this ⊢; omega
  | semi lb =>
    simp only [lengthDet] at hf
    have := hul p (by omega); omega

/-! ## Octets -/

theorem octetBits_length' (o : Fin 256) : (octetBits o).length = 8 := by simp [octetBits, nnbFn_length]

theorem octetsOf_spec : ∀ (k : Nat) (bs : Bits), bs.length = 8 * k →
    (∀ u ∈ octetsOf bs, u.length = 8) ∧ (octetsOf bs).flatten = bs ∧ (octetsOf bs).length = k
  | 0, bs, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [octetsOf]
  | k + 1, bs, h => by
    have hne : bs ≠ [] := by intro e; subst e; simp at h
    rw [octetsOf]; simp only [hne, dite_false]
    obtain ⟨h1, h2, h3⟩ := octetsOf_spec k (bs.drop 8) (by simp; omega)
    refine ⟨?_, ?_, ?_⟩
    · intro u hu; simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · simp; omega
      · exact h1 u hu
    · simp [h2]
    · simp [h3]

theorem octetsFor_le {a b : Nat} (h : a ≤ b) : octetsFor a ≤ octetsFor b := by
  unfold octetsFor
  have := Nat.size_le_size h
  omega

theorem lt_pow_octetsFor (n : Nat) : n < 2 ^ (8 * octetsFor n) := by
  unfold octetsFor
  have h1 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h2 : Nat.size n ≤ 8 * max 1 ((Nat.size n + 7) / 8) := by omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

theorem nnbValue_nnbMinFn (n : Nat) : nnbValue (nnbMinFn n) = n :=
  nnbValue_nnbFn_of_lt (lt_pow_octetsFor n)

theorem nnbMinFn_length (n : Nat) : (nnbMinFn n).length = 8 * octetsFor n := nnbFn_length _ _

theorem octetsOf_nnbMinFn (n : Nat) :
    (∀ u ∈ octetsOf (nnbMinFn n), u.length = 8) ∧ (octetsOf (nnbMinFn n)).flatten = nnbMinFn n ∧
      (octetsOf (nnbMinFn n)).length = octetsFor n :=
  octetsOf_spec _ _ (nnbMinFn_length n)

theorem constrainedR_reads (v : Variant) (p : Nat) {lb ub i : Int} (hl : lb ≤ i) (hu : i ≤ ub) :
    Reads (constrainedR v lb ub) p (layout v.aligned p (constrainedInt v lb ub i)) i := by
  unfold constrainedR constrainedInt
  by_cases hb : v.aligned = true ∧ (ub - lb + 1).toNat > K64
  · obtain ⟨hv, hr⟩ := hb
    have hw : constrainedWhole v lb ub i = ⟨[.aligned (nnbMinFn (i - lb).toNat)], some (octetsFor (i - lb).toNat)⟩ := by
      simp only [constrainedWhole, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have h1 : ¬ (ub - lb + 1).toNat = 1 := by simp only [K64] at hr; omega
      have h2 : ¬ (ub - lb + 1).toNat ≤ 255 := by simp only [K64] at hr; omega
      have h3 : ¬ (ub - lb + 1).toNat = 256 := by simp only [K64] at hr; omega
      have h4 : ¬ (ub - lb + 1).toNat ≤ K64 := by omega
      simp [h1, h2, h3, h4]
    simp only [hv, hr, decide_true, Bool.and_self, ↓reduceIte, hw]
    obtain ⟨o1, o2, o3⟩ := octetsOf_nnbMinFn (i - lb).toNat
    have hfl : [Field.aligned (nnbMinFn (i - lb).toNat)].flatMap Field.bits = nnbMinFn (i - lb).toNat := by
      simp [Field.bits]
    rw [hfl]
    have hread := lenDetF_reads v fieldView (unitsR v 8) (octetsOf (nnbMinFn (i - lb).toNat))
      (fun al' ys hys p' => unitsR_reads v 8 al' p' ys (fun u hu => o1 u (hys u hu)))
      (.constrained 1 (octetsFor (ub - lb).toNat)) true
      (by
        intro _; rw [o3]
        exact ⟨by unfold octetsFor; omega, octetsFor_le (by omega)⟩)
      (by intro h; cases h) p
    have := hread.map_pure (g := fun us => lb + (nnbValue us.flatten : Int))
    rw [o2, nnbValue_nnbMinFn] at this
    have e : lb + ((i - lb).toNat : Int) = i := by omega
    rw [e, hv] at this
    simpa [bind_assoc, fieldView] using this
  · have hlen : (constrainedWhole v lb ub i).len = none := by
      unfold constrainedWhole
      split_ifs <;> simp_all <;> split_ifs <;> simp
    simp only [hlen]
    have hb' : (v.aligned && decide ((ub - lb + 1).toNat > K64)) = false := by
      cases hv : v.aligned <;> simp_all
    rw [hb']; simp only [Bool.false_eq_true, ↓reduceIte]
    apply wholeR_reads v p hl hu
    cases hv : v.aligned
    · exact Or.inl rfl
    · right; simp_all

/-- An unconstrained length and units of `w` bits, with the fuel the decoder gives. -/
theorem ulF_reads (v : Variant) (w : Nat) (al : Bool) (us : List Bits) (h : ∀ u ∈ us, u.length = w) (p : Nat) :
    Reads (fragFuel >>= fun f => ulR v (unitsR v w) al f) p
      (layout v.aligned p (unconstrainedLength (.field al us))) us :=
  lenDetF_reads v fieldView (unitsR v w) us (fun al' ys hys p' => unitsR_reads v w al' p' ys (fun u hu => h u (hys u hu)))
    (.semi 0) al trivial (by intro h; cases h) p

theorem normallySmallR_reads (v : Variant) (p : Nat) (n : Nat) :
    Reads (normallySmallR v) p (layout v.aligned p (normallySmall n)) n := by
  unfold normallySmallR normallySmall
  by_cases h : n ≤ 63
  · simp only [h, ↓reduceIte]
    rw [show layout v.aligned p [.unaligned [false], .unaligned (nnbFn 6 n)] = [false] ++ nnbFn 6 n by
      simp [layout]]
    refine Reads.bind (bitR_reads p false) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h6 := nnbFn_length 6 n
    have := (h6 ▸ takeN_reads (p + [false].length) (nnbFn 6 n)).map_pure (g := nnbValue)
    rw [nnbValue_nnbFn_of_lt (by omega)] at this
    exact this
  · simp only [h, ↓reduceIte, layout_cons_unaligned]
    refine Reads.bind (bitR_reads p true) ?_
    simp only [↓reduceIte]
    obtain ⟨o1, o2, _⟩ := octetsOf_nnbMinFn n
    have := (ulF_reads v 8 true _ o1 (p + [true].length)).map_pure (g := fun us => nnbValue us.flatten)
    rw [o2, nnbValue_nnbMinFn] at this
    simpa [bind_assoc] using this

theorem octetUnits_spec (os : Octets) : ∀ u ∈ octetUnits os, u.length = 8 := by
  intro u hu; simp only [octetUnits, List.mem_map] at hu
  obtain ⟨o, _, rfl⟩ := hu; exact octetBits_length' o

theorem octetOf_octetBits' (o : Fin 256) : octetOf (octetBits o) = o := by
  have := X690.octetOf_octetBits o []; simpa using this

theorem octetsUL_reads (v : Variant) (p : Nat) (os : Octets) :
    Reads (octetsUL v) p (layout v.aligned p (unconstrainedLength (.field true (octetUnits os)))) os := by
  unfold octetsUL
  have := (ulF_reads v 8 true _ (octetUnits_spec os) p).map_pure (g := fun us => us.map octetOf)
  have e : (octetUnits os).map octetOf = os := by
    simp [octetUnits, List.map_map, Function.comp_def, octetOf_octetBits']
  rw [e] at this
  simpa [bind_assoc] using this

theorem bitUnits_spec (bs : Bits) : (∀ u ∈ bitUnits bs, u.length = 1) ∧ (bitUnits bs).flatten = bs ∧
    (bitUnits bs).length = bs.length := by
  refine ⟨?_, ?_, by simp [bitUnits]⟩
  · intro u hu; simp only [bitUnits, List.mem_map] at hu; obtain ⟨b, _, rfl⟩ := hu; rfl
  · induction bs with
    | nil => rfl
    | cons b bs ih => simp only [bitUnits, List.map_cons, List.flatten_cons] at ih ⊢; rw [ih]; rfl

theorem bitsRootR_reads (v : Variant) (p : Nat) (lb : Nat) (ub : Option Nat) (bs : Bits)
    (h : ∀ u, ub = some u → lb ≤ bs.length ∧ bs.length ≤ u) :
    Reads (bitsRootR v lb ub) p (layout v.aligned p (bitsRootFields v lb ub bs)) bs := by
  obtain ⟨b1, b2, b3⟩ := bitUnits_spec bs
  have hlen := fun (k : LenKind) (hk : k.CountOk (bitUnits bs).length) (hns : k ≠ .normallySmall) =>
    (lenDetF_reads v fieldView (unitsR v 1) (bitUnits bs)
      (fun al' ys hys p' => unitsR_reads v 1 al' p' ys (fun u hu => b1 u (hys u hu))) k true hk
      (fun e => absurd e hns) p).map_pure (g := List.flatten)
  unfold bitsRootR bitsRootFields
  cases ub with
  | none =>
    have := hlen (.semi lb) trivial (by simp)
    rw [b2] at this; simpa [bind_assoc, fieldView] using this
  | some u =>
    obtain ⟨hl, hu⟩ := h u rfl
    by_cases h0 : u = 0
    · subst h0
      have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact Reads.pure _ _
    simp only [h0]
    by_cases h1 : lb = u ∧ u ≤ 16
    · simp only [h1, and_self, ↓reduceIte, layout_unaligned]
      have : bs.length = u := by omega
      rw [← this]; exact takeN_reads p bs
    simp only [h1, ↓reduceIte]
    by_cases h2 : lb = u ∧ u < K64
    · simp only [h2, and_self, ↓reduceIte]
      have : bs.length = u := by omega
      rw [← this]; simpa using fieldR_reads v true p bs
    simp only [h2, ↓reduceIte]
    have := hlen (.constrained lb u) (by intro _; rw [b3]; exact ⟨hl, hu⟩) (by simp)
    rw [b2] at this; simpa [bind_assoc, fieldView] using this

theorem octetsRootR_reads (v : Variant) (p : Nat) (lb : Nat) (ub : Option Nat) (os : Octets)
    (h : ∀ u, ub = some u → lb ≤ os.length ∧ os.length ≤ u) :
    Reads (octetsRootR v lb ub) p (layout v.aligned p (octetsRootFields v lb ub os)) os := by
  have e : (octetUnits os).map octetOf = os := by
    simp [octetUnits, List.map_map, Function.comp_def, octetOf_octetBits']
  have hlen := fun (k : LenKind) (hk : k.CountOk (octetUnits os).length) (hns : k ≠ .normallySmall) =>
    (lenDetF_reads v fieldView (unitsR v 8) (octetUnits os)
      (fun al' ys hys p' => unitsR_reads v 8 al' p' ys (fun u hu => octetUnits_spec os u (hys u hu))) k true hk
      (fun e => absurd e hns) p).map_pure (g := List.map octetOf)
  have hbl : (bitsOf os).length = 8 * os.length := bitsOf_length os
  unfold octetsRootR octetsRootFields
  cases ub with
  | none =>
    have := hlen (.semi lb) trivial (by simp)
    rw [e] at this; simpa [bind_assoc, fieldView] using this
  | some u =>
    obtain ⟨hl, hu⟩ := h u rfl
    by_cases h0 : u = 0
    · subst h0
      have : os = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact Reads.pure _ _
    simp only [h0]
    by_cases h1 : lb = u ∧ u ≤ 2
    · simp only [h1, and_self, ↓reduceIte, layout_unaligned]
      have hl' : 8 * u = (bitsOf os).length := by omega
      rw [hl']
      have := (takeN_reads p (bitsOf os)).map_pure (g := bitsToOctets)
      rwa [X690.bitsToOctets_bitsOf] at this
    simp only [h1, ↓reduceIte]
    by_cases h2 : lb = u ∧ u < K64
    · simp only [h2, and_self, ↓reduceIte]
      have hl' : 8 * u = (bitsOf os).length := by omega
      rw [hl']
      have := (fieldR_reads v true p (bitsOf os)).map_pure (g := bitsToOctets)
      rw [X690.bitsToOctets_bitsOf] at this; simpa using this
    simp only [h2, ↓reduceIte]
    have := hlen (.constrained lb u) (by intro _; simp only [octetUnits, List.length_map]; exact ⟨hl, hu⟩) (by simp)
    rw [e] at this; simpa [bind_assoc, fieldView] using this

theorem le_foldl_max : ∀ (l : List Nat) (a c : Nat), c ∈ l → c ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | x :: xs, a, c, h => by
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact le_trans (le_max_right a c) (foldl_max_ge xs (max a c))
    · exact le_foldl_max xs _ c h
where
  foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
    | [], _ => le_rfl
    | x :: xs, a => le_trans (le_max_left a x) (foldl_max_ge xs (max a x))

theorem charWidth_ge (v : Variant) (N : Nat) : N ≤ 2 ^ charWidth v N := by
  unfold charWidth
  have hB : N ≤ 2 ^ bitsFor N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · exact (bitsFor_spec h).2 le_rfl
  cases v.aligned
  · simpa using hB
  · simp only [↓reduceIte, pow2Ceil]
    split_ifs with h1
    · have : bitsFor N ≤ 1 := h1
      calc N ≤ 2 ^ bitsFor N := hB
        _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    · apply le_trans hB
      apply Nat.pow_le_pow_right (by norm_num)
      have := Nat.lt_size_self (bitsFor N - 1)
      omega

theorem charOf_charField (v : Variant) (alpha : List Nat) (c : Nat) (hc : c ∈ alpha) :
    charOf v alpha (charField v alpha c) = .ok c := by
  unfold charOf charField
  have hN := charWidth_ge v alpha.length
  by_cases h : alpha.foldl max 0 ≤ 2 ^ charWidth v alpha.length - 1
  · simp only [h, ↓reduceIte]
    have := le_foldl_max alpha 0 c hc
    rw [nnbValue_nnbFn_of_lt (by have := Nat.one_le_two_pow (n := charWidth v alpha.length); omega)]
  · simp only [h, ↓reduceIte]
    have hi : alpha.idxOf c < alpha.length := List.idxOf_lt_length_iff.mpr hc
    rw [nnbValue_nnbFn_of_lt (by omega), List.getElem?_idxOf hc]

theorem mapM_charOf (v : Variant) (alpha : List Nat) : ∀ (cs : List Nat), (∀ c ∈ cs, c ∈ alpha) →
    (cs.map (charField v alpha)).mapM (charOf v alpha) = .ok cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.map_cons, List.mapM_cons, charOf_charField v alpha c (h c (by simp)),
      mapM_charOf v alpha cs (fun x hx => h x (by simp [hx]))]
    rfl

theorem charField_length (v : Variant) (alpha : List Nat) (c : Nat) :
    (charField v alpha c).length = charWidth v alpha.length := by
  simp [charField, nnbFn_length]

theorem kmR_reads (v : Variant) (p : Nat) (alpha : List Nat) (alb : Nat) (aub : Option Nat) (cs : List Nat)
    (hc : ∀ c ∈ cs, c ∈ alpha) (h : ∀ u, aub = some u → alb ≤ cs.length ∧ cs.length ≤ u) :
    Reads (kmR v alpha alb aub) p (layout v.aligned p (kmBody v alpha alb aub cs)) cs := by
  have hu1 : ∀ u ∈ cs.map (charField v alpha), u.length = charWidth v alpha.length := by
    intro u hu; simp only [List.mem_map] at hu; obtain ⟨c, _, rfl⟩ := hu; exact charField_length v alpha c
  have hul : (cs.map (charField v alpha)).length = cs.length := by simp
  have hm := mapM_charOf v alpha cs hc
  let K : List Bits → PM (List Nat) := fun us => match us.mapM (charOf v alpha) with
    | .ok cs => (Pure.pure cs : PM (List Nat))
    | .error e => throw e
  have fin : ∀ (p' : Nat), Reads (K (cs.map (charField v alpha))) p' [] cs := by
    intro p'; show Reads (match (cs.map (charField v alpha)).mapM (charOf v alpha) with
      | .ok cs => (Pure.pure cs : PM (List Nat))
      | .error e => throw e) p' [] cs
    rw [hm]; exact Reads.pure _ _
  have hlen := fun (k : LenKind) (al : Bool) (hk : k.CountOk cs.length) (hns : k ≠ .normallySmall) =>
    (lenDetF_reads v fieldView (unitsR v (charWidth v alpha.length)) (cs.map (charField v alpha))
      (fun al' ys hys p' => unitsR_reads v _ al' p' ys (fun u hu => hu1 u (hys u hu))) k al (hul ▸ hk)
      (fun e => absurd e hns) p).bind (f := K) (fin _)
  unfold kmR kmBody
  cases aub with
  | none =>
    have := hlen (.semi alb) true trivial (by simp)
    simp only [bind_assoc, fieldView, List.append_nil] at this; exact this
  | some u =>
    obtain ⟨hl, hu⟩ := h u rfl
    by_cases h1 : alb = u ∧ u < K64
    · simp only [h1, and_self, ↓reduceIte]
      have hfl : (cs.map (charField v alpha)).flatten.length = u * charWidth v alpha.length := by
        rw [flatten_length_of _ _ hu1, hul, Nat.mul_comm]; congr 1; omega
      have hch : chunks (charWidth v alpha.length) u (cs.map (charField v alpha)).flatten = cs.map (charField v alpha) := by
        have := chunks_flatten _ _ hu1; rw [hul] at this
        rwa [show cs.length = u by omega] at this
      have r0 := (fieldR_reads v (u * charWidth v alpha.length > 16) p (cs.map (charField v alpha)).flatten).map_pure
        (g := chunks (charWidth v alpha.length) u)
      rw [hfl, hch] at r0
      have r1 := r0.bind (f := K) (fin _)
      rw [List.append_nil] at r1
      simp only [bind_assoc, pure_bind] at r1
      simp only [pure_bind]
      by_cases hgt : u * charWidth v alpha.length > 16
      · simp only [hgt, decide_true, ↓reduceIte] at r1 ⊢; exact r1
      · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte] at r1 ⊢; exact r1
    · simp only [h1, ↓reduceIte]
      have := hlen (.constrained alb u) (u * charWidth v alpha.length ≥ 16) (by intro _; exact ⟨hl, hu⟩) (by simp)
      simp only [bind_assoc, fieldView, List.append_nil] at this; exact this

theorem sizeBounds_reads (S : CSet) (e : Bool) (he : S.ext = false → e = false) (p : Nat) :
    Reads (sizeBounds S) p (if S.ext then [e] else [])
      (e, if e then (0, none) else (lbOf S, ubOf S)) := by
  unfold sizeBounds
  cases hs : S.ext
  · rw [he hs]; simpa using Reads.pure (false, lbOf S, ubOf S) p
  · simp only [↓reduceIte]
    refine Reads.bind' (b2 := []) (bitR_reads p e) ?_ (by simp)
    cases e
    · simpa using Reads.pure _ _
    · simpa using Reads.pure _ _

/-- Components read one after another (11.9.2 c), 20, 22). -/
theorem compsR_reads (v : Variant) (m : PM (Val × FieldList)) (xs : List (Val × FieldList))
    (h : ∀ x ∈ xs, ∀ p, Reads m p (layout v.aligned p x.2) x) :
    ∀ (ys : List (Val × FieldList)), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads ((List.replicate ys.length ()).mapM fun _ => m) p (layout v.aligned p (ys.map (·.2)).flatten) ys
  | [], _, p => by simpa using Reads.pure ([] : List (Val × FieldList)) p
  | y :: ys, hys, p => by
    simp only [List.length_cons, List.replicate_succ, List.mapM_cons, List.map_cons, List.flatten_cons,
      layout_append]
    refine Reads.bind (h y (hys y (by simp)) p) ?_
    refine Reads.bind' (b2 := []) (compsR_reads v m xs h ys (fun z hz => hys z (by simp [hz])) _) ?_ (by simp)
    simpa using Reads.pure (y :: ys) _

end Asn1.X691
