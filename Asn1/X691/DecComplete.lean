import Asn1.X691.ReadComplete
import Asn1.X691.ViewCSound
import Asn1.X690.DecComplete

/-!
# The PER decoder reads back every encoding (completeness)

Each case of `pdecB`, run on the bits that `per` lays out for a value, followed by anything,
returns that value and its field-list, and stops where the field-list ends (`Reads`).
-/

namespace Asn1.X691

open Asn1.X680

/-! ## Readers followed by more -/

theorem lenDet_fuel {α : Type} (v : Variant) (V : AView α) (k : LenKind) (al : Bool) (xs : List α)
    (p : Nat) (hu : k.usesUL) :
    xs.length / K16 ≤ (layout v.aligned p (lengthDet v k (V.A al xs))).length := by
  have hul := ul_layout_len v V (xs.length / K16 + 1) al xs
  cases k with
  | constrained lb ub =>
    simp only [LenKind.usesUL] at hu
    simp only [lengthDet, show ¬ ub < K64 by omega, ↓reduceIte]
    exact hul p (by omega)
  | normallySmall =>
    by_cases h64 : (V.A al xs).count ≤ 64
    · rw [V.count] at h64
      have : xs.length / K16 = 0 := Nat.div_eq_of_lt (by simp only [K16]; omega)
      omega
    · simp only [lengthDet, h64, ↓reduceIte, layout_cons_unaligned, List.length_append]
      have := hul (p + [true].length) (by omega)
      omega
  | semi lb =>
    simp only [lengthDet]
    exact hul p (by omega)

theorem fragFuel_app {α β : Type} {m : Nat → PM α} {k : α → PM β} {p : Nat} {b1 b2 : Bits} {a : α} {c : β}
    (hm : ∀ f, b1.length < f → Reads (m f) p b1 a) (hk : Reads (k a) (p + b1.length) b2 c) :
    Reads (fragFuel >>= fun f => m f >>= k) p (b1 ++ b2) c := by
  apply fragFuel_bind
  intro f hf
  exact (hm f (by simp at hf; omega)).bind hk

theorem lenDetF_app {α β : Type} (v : Variant) (V : AView α) (readK : Bool → Nat → PM (List α))
    (xs : List α)
    (hk : ∀ (al' : Bool) (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads (readK al' ys.length) p (layout v.aligned p (V.F al' ys)) ys)
    (k : LenKind) (al : Bool) (hlen : k.CountOk xs.length)
    (hns : k = .normallySmall → 1 ≤ xs.length) (p : Nat) {k' : List α → PM β} {b2 : Bits} {c : β}
    (hk' : Reads (k' xs) (p + (layout v.aligned p (lengthDet v k (V.A al xs))).length) b2 c) :
    Reads (fragFuel >>= fun f => lenDetR v k readK al f >>= k') p
      (layout v.aligned p (lengthDet v k (V.A al xs)) ++ b2) c :=
  fragFuel_app (fun f hf => lenDetR_reads v V readK xs hk k al f
    (fun hu => by have := lenDet_fuel v V k al xs p hu; omega) hlen hns p) hk'

theorem ulF_app {β : Type} (v : Variant) (w : Nat) (al : Bool) (us : List Bits) (h : ∀ u ∈ us, u.length = w)
    (p : Nat) {k' : List Bits → PM β} {b2 : Bits} {c : β}
    (hk' : Reads (k' us) (p + (layout v.aligned p (unconstrainedLength (.field al us))).length) b2 c) :
    Reads (fragFuel >>= fun f => ulR v (unitsR v w) al f >>= k') p
      (layout v.aligned p (unconstrainedLength (.field al us)) ++ b2) c :=
  lenDetF_app v fieldView (unitsR v w) us (fun al' ys hys p' => unitsR_reads v w al' p' ys (fun u hu => h u (hys u hu)))
    (.semi 0) al trivial (by intro h; cases h) p hk'

/-! ## Integers (13) -/

theorem unconstrainedInt_reads (v : Variant) (p : Nat) (i : Int) :
    Reads (fragFuel >>= fun f => ulR v (unitsR v 8) true f >>= fun us => Pure.pure (tcValue us.flatten))
      p (layout v.aligned p (unconstrainedInt i)) i := by
  obtain ⟨o1, o2, _⟩ := octetsOf_spec _ (tcMinFn i) (tcMinFn_length i)
  have := (ulF_reads v 8 true _ o1 p).map_pure (g := fun us => tcValue us.flatten)
  rw [o2, (tcMinFn_spec i).2.2.1] at this
  have hf : (unconstrainedWhole i).fields.flatMap Field.bits = tcMinFn i := by
    simp [unconstrainedWhole, Field.bits]
  simp only [unconstrainedInt, hf]
  simpa [bind_assoc] using this

theorem semiInt_reads (v : Variant) (p : Nat) (lb i : Int) (hl : lb ≤ i) :
    Reads (fragFuel >>= fun f => ulR v (unitsR v 8) true f >>= fun us => Pure.pure (lb + nnbValue us.flatten))
      p (layout v.aligned p (semiInt lb i)) i := by
  obtain ⟨o1, o2, _⟩ := octetsOf_nnbMinFn (i - lb).toNat
  have := (ulF_reads v 8 true _ o1 p).map_pure (g := fun us => lb + (nnbValue us.flatten : Int))
  rw [o2, nnbValue_nnbMinFn, show lb + ((i - lb).toNat : Int) = i by omega] at this
  have hf : (semiWhole lb i).fields.flatMap Field.bits = nnbMinFn (i - lb).toNat := by
    simp [semiWhole, Field.bits]
  simp only [semiInt, hf]
  simpa [bind_assoc] using this

theorem int_complete {E : Env} {v : Variant} {n : Nat} {rec : List X690.DFrame → Scope → Ty → PM (Val × FieldList)}
    {frames : List X690.DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}
    {nl : List (String × Int)} {i : Int} {fl : FieldList} {C : CSet}
    (hC : pIntC E n sc t = some C) (h : IntFields v (pInt E n sc t) i fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.integer nl)) p (layout v.aligned p fl) (.int i, fl) := by
  obtain ⟨hr, ha, he⟩ := pIntC_sound hC
  obtain ⟨hai, hcase⟩ := h
  have hlu := least?_eq hr
  have hgu := greatest?_eq hr
  -- the root's reading: the number, from its root fields
  have hroot : C.r.mem i = true → ∀ p', Reads (match C.r.least?, C.r.greatest? with
      | some lb, some ub => constrainedR v lb ub
      | some lb, none => fragFuel >>= fun f => ulR v (unitsR v 8) true f >>= fun us => Pure.pure (lb + nnbValue us.flatten)
      | none, _ => fragFuel >>= fun f => ulR v (unitsR v 8) true f >>= fun us => Pure.pure (tcValue us.flatten))
      p' (layout v.aligned p' (intRootFieldsC v C.r i)) i := by
    intro hm p'
    unfold intRootFieldsC
    cases hl : C.r.least? with
    | none => exact unconstrainedInt_reads v p' i
    | some lb =>
      have hlb := ((Ivs.least?_spec _ _).mp hl).2 hm
      cases hg : C.r.greatest? with
      | none => exact semiInt_reads v p' lb i hlb
      | some ub =>
        have hub := ((Ivs.greatest?_spec _ _).mp hg).2 hm
        exact constrainedR_reads v p' hlb hub
  have hfl : intRootFields v (pInt E n sc t).r i = intRootFieldsC v C.r i := by
    unfold intRootFields intRootFieldsC; rw [hlu, hgu]
    cases C.r.least? <;> cases C.r.greatest? <;> rfl
  have hamem : C.a.mem i = true := (ha i).mp hai
  obtain ⟨o1, o2, _⟩ := octetsOf_spec _ (tcMinFn i) (tcMinFn_length i)
  have htc : tcValue (tcMinFn i) = i := (tcMinFn_spec i).2.2.1
  have hU : ∀ p', layout v.aligned p' (unconstrainedInt i) =
      layout v.aligned p' (unconstrainedLength (.field true (octetsOf (tcMinFn i)))) ++ [] := by
    intro p'; simp [unconstrainedInt, unconstrainedWhole, Field.bits]
  unfold pdecB
  simp only [hC]
  cases hx : C.ext
  · rw [he, hx] at hcase
    simp only [Bool.false_eq_true, ↓reduceIte] at hcase
    obtain ⟨hri, rfl⟩ := hcase
    have hm := (hr i).mp hri
    rw [hfl]
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, intFl, hx]
    unfold intRootFieldsC
    cases hl : C.r.least? with
    | none =>
      simp only [hl]
      rw [hU]
      refine ulF_app v 8 true _ o1 p ?_
      simp only [o2, htc, hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _
    | some lb =>
      have hlb := ((Ivs.least?_spec _ _).mp hl).2 hm
      cases hg : C.r.greatest? with
      | none =>
        simp only [hl, hg]
        obtain ⟨s1, s2, _⟩ := octetsOf_nnbMinFn (i - lb).toNat
        have hS : layout v.aligned p (semiInt lb i) =
            layout v.aligned p (unconstrainedLength (.field true (octetsOf (nnbMinFn (i - lb).toNat)))) ++ [] := by
          simp [semiInt, semiWhole, Field.bits]
        rw [hS]
        refine ulF_app v 8 true _ s1 p ?_
        have hv : lb + ((nnbValue (octetsOf (nnbMinFn (i - lb).toNat)).flatten : Nat) : Int) = i := by
          rw [s2, nnbValue_nnbMinFn]; omega
        simp only [hv, hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte]
        exact Reads.pure _ _
      | some ub =>
        have hub := ((Ivs.greatest?_spec _ _).mp hg).2 hm
        simp only [hl, hg]
        refine Reads.bind' (b2 := []) (constrainedR_reads v p hlb hub) ?_ (by simp)
        simp only [hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte]
        exact Reads.pure _ _
  · rw [he, hx] at hcase
    simp only [↓reduceIte] at hcase
    simp only [↓reduceIte]
    rcases hcase with ⟨hri, rfl⟩ | ⟨hri, rfl⟩
    · have hm := (hr i).mp hri
      rw [hfl, layout_cons_unaligned]
      refine Reads.bind (bitR_reads p false) ?_
      simp only [Bool.false_eq_true, ↓reduceIte, intFl, hx, hm]
      unfold intRootFieldsC
      cases hl : C.r.least? with
      | none =>
        simp only [hl]
        rw [hU]
        refine ulF_app v 8 true _ o1 _ ?_
        simp only [o2, htc, hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, Bool.true_and, bne_self_eq_false, pure_bind]
        exact Reads.pure _ _
      | some lb =>
        have hlb := ((Ivs.least?_spec _ _).mp hl).2 hm
        cases hg : C.r.greatest? with
        | none =>
          simp only [hl, hg]
          obtain ⟨s1, s2, _⟩ := octetsOf_nnbMinFn (i - lb).toNat
          have hS : layout v.aligned (p + [false].length) (semiInt lb i) =
              layout v.aligned (p + [false].length) (unconstrainedLength (.field true (octetsOf (nnbMinFn (i - lb).toNat)))) ++ [] := by
            simp [semiInt, semiWhole, Field.bits]
          rw [hS]
          refine ulF_app v 8 true _ s1 _ ?_
          have hv : lb + ((nnbValue (octetsOf (nnbMinFn (i - lb).toNat)).flatten : Nat) : Int) = i := by
            rw [s2, nnbValue_nnbMinFn]; omega
          simp only [hv, hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Bool.true_and, bne_self_eq_false, pure_bind]
          exact Reads.pure _ _
        | some ub =>
          have hub := ((Ivs.greatest?_spec _ _).mp hg).2 hm
          simp only [hl, hg]
          refine Reads.bind' (b2 := []) (constrainedR_reads v _ hlb hub) ?_ (by simp)
          simp only [hamem, hm, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Bool.true_and, bne_self_eq_false, pure_bind]
          exact Reads.pure _ _
    · have hm : C.r.mem i = false := by
        cases h' : C.r.mem i
        · rfl
        · exact absurd ((hr i).mpr h') hri
      rw [layout_cons_unaligned]
      refine Reads.bind (bitR_reads p true) ?_
      simp only [↓reduceIte]
      rw [hU]
      refine ulF_app v 8 true _ o1 _ ?_
      simp only [o2, htc, hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Bool.true_and, bne_self_eq_false, intFl, pure_bind]
      exact Reads.pure _ _

/-! ## ENUMERATED (14) -/

theorem idx_sorted : ∀ (L : List (String × Int)), L.Pairwise (fun a b => a.2 < b.2) →
    ∀ x ∈ L, L[(L.filter (fun a => decide (a.2 < x.2))).length]? = some x
  | [], _, x, hx => by simp at hx
  | y :: L, hp, x, hx => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hx with rfl | hx'
    · have : (L.filter (fun a => decide (a.2 < x.2))) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha; have := hp.1 a ha; simp; omega
      simp [this]
    · have hyx := hp.1 x hx'
      simp only [List.filter_cons, hyx, decide_true, ↓reduceIte, List.length_cons,
        List.getElem?_cons_succ]
      exact idx_sorted L hp.2 x hx'

theorem byIndex_enumIndex {items : List (String × Int)} {id : String} {k : Nat}
    (hv : (items.map (·.2)).Nodup) (h : enumIndex items id = some k) :
    ((items.mergeSort fun a b => decide (a.2 ≤ b.2))[k]?).map (·.1) = some id := by
  unfold enumIndex at h
  cases hf : items.find? (·.1 == id) with
  | none => simp [hf] at h
  | some x =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    have hxm := List.mem_of_find?_eq_some hf
    have hxn : x.1 = id := by simpa using List.find?_some hf
    set L := items.mergeSort fun a b => decide (a.2 ≤ b.2)
    have hperm : L.Perm items := List.mergeSort_perm _ _
    have hsort : L.Pairwise (fun a b => decide (a.2 ≤ b.2) = true) :=
      List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) _
    have hnd : (L.map (·.2)).Nodup := (hperm.map _).nodup_iff.mpr hv
    have hstrict : L.Pairwise (fun a b => a.2 < b.2) := by
      have h2 := List.pairwise_map.mp hnd
      exact (hsort.and h2).imp fun ⟨h1, h3⟩ => by simp at h1; omega
    have hlen : (items.filter (fun a => decide (a.2 < x.2))).length = (L.filter (fun a => decide (a.2 < x.2))).length :=
      ((hperm.filter _).length_eq).symm
    rw [hlen, idx_sorted L hstrict x (hperm.mem_iff.mpr hxm)]
    simp [hxn]

theorem enumIndex_lt {items : List (String × Int)} {id : String} {k : Nat} (h : enumIndex items id = some k) :
    k < items.length := by
  unfold enumIndex at h
  cases hf : items.find? (·.1 == id) with
  | none => simp [hf] at h
  | some x =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨x, List.mem_of_find?_eq_some hf, by simp⟩

/-! ## The other leaves -/

section Leaves

variable {E : Env} {v : Variant} {n : Nat} {rec : List X690.DFrame → Scope → Ty → PM (Val × FieldList)}
  {frames : List X690.DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}

/-- 12 -/
theorem bool_complete (b : Bool) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .boolean) p (layout v.aligned p [.unaligned [b]])
      (.bool b, [.unaligned [b]]) := by
  unfold pdecB; dsimp only
  rw [layout_unaligned]
  exact Reads.bind' (b2 := []) (bitR_reads p b) (Reads.pure _ _) (by simp)

/-- 18 -/
theorem null_complete (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .null) p (layout v.aligned p []) (.null, []) := by
  unfold pdecB; dsimp only
  exact Reads.pure _ _

theorem layout_octetsWithLength (al : Bool) (p : Nat) (os : Octets) :
    layout al p (octetsWithLength os) = layout al p (unconstrainedLength (.field true (octetUnits os))) ++ [] := by
  simp [octetsWithLength]

/-- 15 -/
theorem real_complete {r : RealVal} {os : Octets} (h : X690.RealContents .der r os) (hw : r.Wf) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .real) p (layout v.aligned p (octetsWithLength os))
      (.real r, octetsWithLength os) := by
  unfold pdecB; dsimp only
  rw [layout_octetsWithLength]
  refine Reads.bind (octetsUL_reads v p os) ?_
  simp only [X690.decReal_complete h hw]
  exact Reads.pure _ _

/-- 24 -/
theorem oid_complete {arcs : List Nat} (h : X690.OidWf arcs) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .objectIdentifier) p
      (layout v.aligned p (octetsWithLength (X690.oidContents arcs))) (.oid arcs, octetsWithLength (X690.oidContents arcs)) := by
  unfold pdecB; dsimp only
  rw [layout_octetsWithLength]
  refine Reads.bind (octetsUL_reads v p _) ?_
  simp only [X690.decOidArcs_complete h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure _ _

/-- 25 -/
theorem relOid_complete (arcs : List Nat) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .relativeOid) p
      (layout v.aligned p (octetsWithLength (X690.relOidContents arcs))) (.oid arcs, octetsWithLength (X690.relOidContents arcs)) := by
  unfold pdecB; dsimp only
  rw [layout_octetsWithLength]
  refine Reads.bind (octetsUL_reads v p _) ?_
  simp only [X690.decOidArcs_rel_complete, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure _ _

/-- 26 (the decoder's IRI reading is assumed to invert `iriContents`) -/
theorem oidIri_complete {arcs : List String} (h : X690.decIri false (X690.iriContents arcs) = some arcs) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .oidIri) p
      (layout v.aligned p (octetsWithLength (X690.iriContents arcs))) (.iri arcs, octetsWithLength (X690.iriContents arcs)) := by
  unfold pdecB; dsimp only
  rw [layout_octetsWithLength]
  refine Reads.bind (octetsUL_reads v p _) ?_
  simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure _ _

/-- 27 -/
theorem relOidIri_complete {arcs : List String} (h : X690.decIri true (X690.relIriContents arcs) = some arcs) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .relativeOidIri) p
      (layout v.aligned p (octetsWithLength (X690.relIriContents arcs))) (.iri arcs, octetsWithLength (X690.relIriContents arcs)) := by
  unfold pdecB; dsimp only
  rw [layout_octetsWithLength]
  refine Reads.bind (octetsUL_reads v p _) ?_
  simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure _ _

/-- 30.6: a restricted character string type that is not known-multiplier. -/
theorem otherString_complete {k : StrType} {x : Val} {fl : FieldList} (hk : k.knownMultiplier = false)
    (h : OtherStringFields v k x fl) (hb : X690.StrBound k x) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.restricted k)) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨os, hs, rfl⟩ := h
  unfold pdecB; dsimp only
  simp only [hk, Bool.false_eq_true, ↓reduceIte]
  rw [← List.append_nil (layout _ _ (unconstrainedLength _))]
  refine Reads.bind (octetsUL_reads v p os) ?_
  simp only [X690.decString_complete hs hb]
  exact Reads.pure _ _

/-- 10.6.5: ObjectDescriptor, a GraphicString. -/
theorem objectDescriptor_complete {x : Val} {fl : FieldList} (h : OtherStringFields v .graphic x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .objectDescriptor) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨os, hs, rfl⟩ := h
  unfold pdecB; dsimp only
  rw [← List.append_nil (layout _ _ (unconstrainedLength _))]
  refine Reads.bind (octetsUL_reads v p os) ?_
  simp only [X690.decString_complete hs trivial]
  exact Reads.pure _ _

theorem sized_bounds {S : PSet Nat} {C : CSet} (h : DenN C S) {len : Nat} (hr : S.r len) :
    ∀ u, ubOf C = some u → lbOf C ≤ len ∧ len ≤ u := by
  intro u hu
  have hl : lbOf C = (natLeast? S.r).getD 0 := by rw [natLeast?_eq h.1]; rfl
  have hg : ubOf C = natGreatest? S.r := (natGreatest?_eq h.1).symm
  constructor
  · rw [hl]; unfold natLeast?
    split
    · rename_i hx; exact hx.choose_spec.2 hr
    · exact Nat.zero_le _
  · rw [hg] at hu; unfold natGreatest? at hu
    split at hu
    · rename_i hx; cases hu; exact hx.choose_spec.2 hr
    · cases hu

/-- 17 -/
theorem octets_complete {os : Octets} {fl : FieldList} {C : CSet} (hC : pSizeC E n sc t = some C)
    (h : OctetsFields v (pSize E n sc t) os fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .octetString) p (layout v.aligned p fl) (.octets os, fl) := by
  have hD := pSizeC_sound hC
  obtain ⟨hr, ha, he⟩ := hD
  obtain ⟨hal, hcase⟩ := h
  have hlb : (natLeast? (pSize E n sc t).r).getD 0 = lbOf C := by rw [natLeast?_eq hr]; rfl
  have hub : natGreatest? (pSize E n sc t).r = ubOf C := natGreatest?_eq hr
  have hamem := (ha _).mp hal
  unfold pdecB; dsimp only; simp only [hC]
  cases hx : C.ext
  · rw [he, hx] at hcase
    simp only [Bool.false_eq_true, ↓reduceIte] at hcase
    obtain ⟨hri, rfl⟩ := hcase
    have hm := (hr _).mp hri
    rw [hlb, hub]
    have hsb := sizeBounds_reads C false (fun _ => rfl) p
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
    refine Reads.bind' hsb ?_ (List.nil_append _).symm
    simp only [List.length_nil, Nat.add_zero]
    refine Reads.bind' (b2 := []) (octetsRootR_reads v p _ _ os (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
    simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, sizedFl]
    exact Reads.pure _ _
  · rw [he, hx] at hcase
    simp only [↓reduceIte] at hcase
    rcases hcase with ⟨hri, rfl⟩ | ⟨hri, rfl⟩
    · have hm := (hr _).mp hri
      rw [hlb, hub]
      have hsb := sizeBounds_reads C false (fun h => by simp [hx] at h) p
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (octetsRootR_reads v _ _ _ os (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
      simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      exact Reads.pure _ _
    · have hm : C.r.mem os.length = false := by
        cases h' : C.r.mem os.length
        · rfl
        · exact absurd ((hr _).mpr h') hri
      have hsb := sizeBounds_reads C true (fun h => by simp [hx] at h) p
      simp only [hx, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (octetsRootR_reads v _ _ _ os (by intro u hu; cases hu)) ?_ (by simp)
      simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      exact Reads.pure _ _

/-- 16 -/
theorem bits_complete {named : List (String × Nat)} {bs : Bits} {fl : FieldList} {C : CSet} (hC : pSizeC E n sc t = some C)
    (h : BitsFields v (pSize E n sc t) bs fl)
    (hn : named ≠ [] → NamedBitsSent (pSize E n sc t) bs bs) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.bitString named)) p (layout v.aligned p fl) (.bits bs, fl) := by
  have hD := pSizeC_sound hC
  obtain ⟨hr, ha, he⟩ := hD
  obtain ⟨hal, hcase⟩ := h
  have hlb : (natLeast? (pSize E n sc t).r).getD 0 = lbOf C := by rw [natLeast?_eq hr]; rfl
  have hub : natGreatest? (pSize E n sc t).r = ubOf C := natGreatest?_eq hr
  have hamem := (ha _).mp hal
  have hall : (named != []) = true →
      ((List.range bs.length).all fun k => decide (k < (stripTrailingZeros bs).length) || !C.a.mem k) = true := by
    intro hne
    have hne' : named ≠ [] := by simpa using hne
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hn hne'
    have hkl : bs.length = k := by
      have := congrArg List.length hk1; simp at this; omega
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    intro k' hk'
    by_cases hc : k' < (stripTrailingZeros bs).length
    · exact Or.inl hc
    · right
      cases h' : C.a.mem k'
      · rfl
      · have := hk4 k' (by omega) ((ha k').mpr h'); omega
  unfold pdecB; dsimp only; simp only [hC]
  cases hx : C.ext
  · rw [he, hx] at hcase
    simp only [Bool.false_eq_true, ↓reduceIte] at hcase
    obtain ⟨hri, rfl⟩ := hcase
    have hm := (hr _).mp hri
    rw [hlb, hub]
    have hsb := sizeBounds_reads C false (fun _ => rfl) p
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
    refine Reads.bind' hsb ?_ (List.nil_append _).symm
    simp only [List.length_nil, Nat.add_zero]
    refine Reads.bind' (b2 := []) (bitsRootR_reads v p _ _ bs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
    simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, sizedFl]
    by_cases hnm : (named != []) = true
    · simp only [hnm, hall hnm, ↓reduceIte, Bool.not_true, Bool.false_eq_true]; exact Reads.pure _ _
    · simp only [hnm, Bool.false_eq_true, ↓reduceIte]; exact Reads.pure _ _
  · rw [he, hx] at hcase
    simp only [↓reduceIte] at hcase
    rcases hcase with ⟨hri, rfl⟩ | ⟨hri, rfl⟩
    · have hm := (hr _).mp hri
      rw [hlb, hub]
      have hsb := sizeBounds_reads C false (fun h => by simp [hx] at h) p
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (bitsRootR_reads v _ _ _ bs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
      simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      by_cases hnm : (named != []) = true
      · simp only [hnm, hall hnm, ↓reduceIte, Bool.not_true, Bool.false_eq_true]; exact Reads.pure _ _
      · simp only [hnm, Bool.false_eq_true, ↓reduceIte]; exact Reads.pure _ _
    · have hm : C.r.mem bs.length = false := by
        cases h' : C.r.mem bs.length
        · rfl
        · exact absurd ((hr _).mpr h') hri
      have hsb := sizeBounds_reads C true (fun h => by simp [hx] at h) p
      simp only [hx, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (bitsRootR_reads v _ _ _ bs (by intro u hu; cases hu)) ?_ (by simp)
      simp only [hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      by_cases hnm : (named != []) = true
      · simp only [hnm, hall hnm, ↓reduceIte, Bool.not_true, Bool.false_eq_true]; exact Reads.pure _ _
      · simp only [hnm, Bool.false_eq_true, ↓reduceIte]; exact Reads.pure _ _

/-- 30: a known-multiplier character string type. -/
theorem km_complete {k : StrType} {cs : List Nat} {fl : FieldList} {P : CSet × CSet} (hk : k.knownMultiplier = true)
    (hC : pStrC E n sc t = some P) (h : KmFields v k (pStr E n sc t) cs fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.restricted k)) p (layout v.aligned p fl) (.chars cs, fl) := by
  obtain ⟨C, A⟩ := P
  obtain ⟨hD, hA⟩ := pStrC_sound hC
  have halpha := effAlphabet_eq (k := k) hA
  obtain ⟨hr, ha, he⟩ := hD
  unfold KmFields at h
  simp only [halpha] at h
  obtain ⟨hcs, hal, hcase⟩ := h
  have hlb : (natLeast? (pStr E n sc t).1.r).getD 0 = lbOf C := by rw [natLeast?_eq hr]; rfl
  have hub : natGreatest? (pStr E n sc t).1.r = ubOf C := natGreatest?_eq hr
  have hamem := (ha _).mp hal
  have hcon : (cs.all fun c => (effAlphabetC k A).contains c) = true := by
    simp only [List.all_eq_true, List.contains_iff_mem]; exact hcs
  unfold pdecB; dsimp only; simp only [hk, ↓reduceIte, hC]
  cases hx : C.ext
  · rw [he, hx] at hcase
    simp only [Bool.false_eq_true, ↓reduceIte] at hcase
    obtain ⟨hri, rfl⟩ := hcase
    have hm := (hr _).mp hri
    rw [hlb, hub]
    have hsb := sizeBounds_reads C false (fun _ => rfl) p
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
    refine Reads.bind' hsb ?_ (List.nil_append _).symm
    simp only [List.length_nil, Nat.add_zero]
    refine Reads.bind' (b2 := []) (kmR_reads v p _ _ _ cs hcs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
    simp only [hcon, hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, sizedFl]
    exact Reads.pure _ _
  · rw [he, hx] at hcase
    simp only [↓reduceIte] at hcase
    rcases hcase with ⟨hri, rfl⟩ | ⟨hri, rfl⟩
    · have hm := (hr _).mp hri
      rw [hlb, hub]
      have hsb := sizeBounds_reads C false (fun h => by simp [hx] at h) p
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (kmR_reads v _ _ _ _ cs hcs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
      simp only [hcon, hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      exact Reads.pure _ _
    · have hm : C.r.mem cs.length = false := by
        cases h' : C.r.mem cs.length
        · rfl
        · exact absurd ((hr _).mpr h') hri
      have hsb := sizeBounds_reads C true (fun h => by simp [hx] at h) p
      simp only [hx, ↓reduceIte] at hsb
      refine Reads.bind' hsb ?_ rfl
      simp only [List.length_singleton]
      refine Reads.bind' (b2 := []) (kmR_reads v _ _ _ _ cs hcs (by intro u hu; cases hu)) ?_ (by simp)
      simp only [hcon, hamem, hm, hx, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, sizedFl, bne_self_eq_false]
      exact Reads.pure _ _

/-- 10.6.5: GeneralizedTime. -/
theorem genTime_complete {x : Val} {fl : FieldList} (h : UsefulTimeFields v X690.GenTimeCanon x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .generalizedTime) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨cs, rfl, hcan, h⟩ := h
  have hD : DenN CSet.univ PSet.univ := DenF.plain (s := Ivs.univ) (g := fun _ => True) (fun x => by simp)
  have hA : DenN (CSet.plain (rangeIvs visibleChars)) (PSet.plain fun c => visibleChars.mem c) :=
    DenF.plain (fun c => by simp [mem_rangeIvs])
  have halpha := effAlphabet_eq (k := .visible) hA
  obtain ⟨hr, ha, he⟩ := hD
  unfold KmFields at h
  simp only [halpha] at h
  obtain ⟨hcs, hal, hcase⟩ := h
  have hcon : (cs.all fun c => (effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))).contains c) = true := by
    simp only [List.all_eq_true, List.contains_iff_mem]; exact hcs
  have hlb : (natLeast? (PSet.univ : PSet Nat).r).getD 0 = lbOf CSet.univ := by rw [natLeast?_eq hr]; rfl
  have hub : natGreatest? (PSet.univ : PSet Nat).r = ubOf CSet.univ := natGreatest?_eq hr
  have hx : (PSet.univ : PSet Nat).ext = false := rfl
  simp only [hx, Bool.false_eq_true, ↓reduceIte] at hcase
  obtain ⟨hri, rfl⟩ := hcase
  rw [hlb, hub]
  unfold pdecB; dsimp only
  have hsb := sizeBounds_reads CSet.univ false (fun _ => rfl) p
  simp only [show CSet.univ.ext = false from rfl, Bool.false_eq_true, ↓reduceIte] at hsb
  refine Reads.bind' hsb ?_ (List.nil_append _).symm
  simp only [List.length_nil, Nat.add_zero]
  refine Reads.bind' (b2 := []) (kmR_reads v p _ _ _ cs hcs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
  have hm : CSet.univ.r.mem cs.length = true := (hr _).mp hri
  simp only [hcon, X690.genTimeCanonB_complete hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte, sizedFl,
    show CSet.univ.ext = false from rfl]
  exact Reads.pure _ _

/-- 10.6.5: UTCTime. -/
theorem utcTime_complete {x : Val} {fl : FieldList} (h : UsefulTimeFields v X690.UtcTimeCanon x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .utcTime) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨cs, rfl, hcan, h⟩ := h
  have hD : DenN CSet.univ PSet.univ := DenF.plain (s := Ivs.univ) (g := fun _ => True) (fun x => by simp)
  have hA : DenN (CSet.plain (rangeIvs visibleChars)) (PSet.plain fun c => visibleChars.mem c) :=
    DenF.plain (fun c => by simp [mem_rangeIvs])
  have halpha := effAlphabet_eq (k := .visible) hA
  obtain ⟨hr, ha, he⟩ := hD
  unfold KmFields at h
  simp only [halpha] at h
  obtain ⟨hcs, hal, hcase⟩ := h
  have hcon : (cs.all fun c => (effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))).contains c) = true := by
    simp only [List.all_eq_true, List.contains_iff_mem]; exact hcs
  have hlb : (natLeast? (PSet.univ : PSet Nat).r).getD 0 = lbOf CSet.univ := by rw [natLeast?_eq hr]; rfl
  have hub : natGreatest? (PSet.univ : PSet Nat).r = ubOf CSet.univ := natGreatest?_eq hr
  have hx : (PSet.univ : PSet Nat).ext = false := rfl
  simp only [hx, Bool.false_eq_true, ↓reduceIte] at hcase
  obtain ⟨hri, rfl⟩ := hcase
  rw [hlb, hub]
  unfold pdecB; dsimp only
  have hsb := sizeBounds_reads CSet.univ false (fun _ => rfl) p
  simp only [show CSet.univ.ext = false from rfl, Bool.false_eq_true, ↓reduceIte] at hsb
  refine Reads.bind' hsb ?_ (List.nil_append _).symm
  simp only [List.length_nil, Nat.add_zero]
  refine Reads.bind' (b2 := []) (kmR_reads v p _ _ _ cs hcs (sized_bounds ⟨hr, ha, he⟩ hri)) ?_ (by simp)
  have hm : CSet.univ.r.mem cs.length = true := (hr _).mp hri
  simp only [hcon, X690.utcTimeCanonB_complete hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte, sizedFl,
    show CSet.univ.ext = false from rfl]
  exact Reads.pure _ _

/-- 14 -/
theorem enum_complete {root : List (String × Option Int)} {ext : Option (List (String × Option Int))}
    {id : String} {fl : FieldList}
    (h : EnumFields v root ext sc'.mod.header.extImplied id fl)
    (hv : ((enumNumbers root ext).map (·.2)).Nodup) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.enumerated root ext)) p (layout v.aligned p fl) (.enum id, fl) := by
  have hvr : (((enumNumbers root ext).take root.length).map (·.2)).Nodup :=
    hv.sublist ((List.take_sublist _ _).map _)
  have hva : (((enumNumbers root ext).drop root.length).map (·.2)).Nodup :=
    hv.sublist ((List.drop_sublist _ _).map _)
  unfold EnumFields at h
  unfold pdecB; dsimp only
  cases hx : (ext.isSome || sc'.mod.header.extImplied)
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨k, hk, rfl⟩ := h
    have hlt := enumIndex_lt hk
    simp only [pure_bind, Bool.not_false, ↓reduceIte]
    refine Reads.bind' (b2 := []) (constrainedR_reads v p (i := (k : Int)) (by omega) (by omega)) ?_ (by simp)
    simp only [Int.toNat_natCast, byIndex_enumIndex hvr hk, hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact Reads.pure _ _
  · simp only [hx, ↓reduceIte] at h ⊢
    rcases h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · have hlt := enumIndex_lt hk
      rw [layout_cons_unaligned]
      refine Reads.bind (bitR_reads p false) ?_
      simp only [Bool.not_false, ↓reduceIte]
      refine Reads.bind' (b2 := []) (constrainedR_reads v _ (i := (k : Int)) (by omega) (by omega)) ?_ (by simp)
      simp only [Int.toNat_natCast, byIndex_enumIndex hvr hk, hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _
    · rw [layout_cons_unaligned]
      refine Reads.bind (bitR_reads p true) ?_
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Reads.bind' (b2 := []) (normallySmallR_reads v _ k) ?_ (by simp)
      simp only [byIndex_enumIndex hva hk, hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _

end Leaves

end Asn1.X691
