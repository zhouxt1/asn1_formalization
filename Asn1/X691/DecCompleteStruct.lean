import Asn1.X691.DecComplete
import Asn1.X691.DecodeLemmas

/-!
# The PER decoder reads back every encoding: the composite types, and unambiguity

`DecComplete.lean` proves the leaf cases of `pdecB`. This file adds the open type fields, CHOICE,
SEQUENCE OF, SET OF, the open type, SEQUENCE and SET, and puts them together by induction on fuel
(`pdec_complete`). With the decoder's determinism that gives `decode_complete` and unambiguity on the
values the decoder reads back (`per_unambiguous`).
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (DFrame)

/-! ## Open type fields (11.2) -/

theorem pad8_length_mod (bs : Bits) : (pad8 bs).length % 8 = 0 := by
  simp only [pad8, List.length_append, List.length_replicate]; omega

/-- The complete encoding (11.1) of a field-list as an octetstring: its layout, then padding. -/
theorem complete_other (v : Variant) (fl : FieldList) :
    ∃ pad, complete v .other fl = layout v.aligned 0 fl ++ pad ∧
      (complete v .other fl).length % 8 = 0 := by
  rw [← completeFast_eq]
  unfold completeFast
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    show ((Carrier.other == Carrier.bitString) = false) from rfl]
  split_ifs with h
  · exact ⟨List.replicate 8 false, by simp [h], by simp⟩
  · exact ⟨_, rfl, pad8_length_mod _⟩

theorem openR_reads (v : Variant) (p : Nat) (afl : FieldList) :
    Reads (openR v) p (layout v.aligned p (openField v afl)) (octetsOf (complete v .other afl)) := by
  obtain ⟨_, _, h8⟩ := complete_other v afl
  obtain ⟨o1, _, _⟩ := octetsOf_spec _ _ (show (complete v .other afl).length = 8 * ((complete v .other afl).length / 8) by omega)
  unfold openR openField
  exact ulF_reads v 8 true _ o1 p

/-- A decoder that reads back `afl` from the start reads it back from its complete encoding. -/
theorem runInner_complete {v : Variant} {m : PM (Val × FieldList)} {y : Val} {afl : FieldList}
    (h : Reads m 0 (layout v.aligned 0 afl) (y, afl)) :
    runInner m (octetsOf (complete v .other afl)).flatten = .ok (y, afl) := by
  obtain ⟨pad, he, h8⟩ := complete_other v afl
  obtain ⟨_, o2, _⟩ := octetsOf_spec _ _ (show (complete v .other afl).length = 8 * ((complete v .other afl).length / 8) by omega)
  rw [o2, he]
  unfold runInner
  rw [h pad]; rfl

theorem openCheck_false (v : Variant) (afl : FieldList) :
    (octetsOf (complete v .other afl) != octetsOf (completeFast v .other afl)) = false := by
  rw [completeFast_eq]; simp

/-! ## CHOICE (23) -/

/-- The root alternatives and the additions, each sorted as 23.2 and the decoder sort them. -/
def choiceRootS (E : Env) (n : Nat) (sc' : Scope) (root : List Alt) (ext : Option (List AltAdd)) :
    List (Alt × Option (List Tag)) :=
  let alts := altTags E n sc' root ext
  let auto := autoChoice sc'.mod.header.tagDefault root ext
  let key (p : Alt × Option (List Tag)) : Option Tag :=
    if auto then p.2.bind List.head? else sortTag E n sc' p.1.ty
  sortByTag key (alts.take root.length)

def choiceAddS (E : Env) (n : Nat) (sc' : Scope) (root : List Alt) (ext : Option (List AltAdd)) :
    List (Alt × Option (List Tag)) :=
  let alts := altTags E n sc' root ext
  let auto := autoChoice sc'.mod.header.tagDefault root ext
  let key (p : Alt × Option (List Tag)) : Option Tag :=
    if auto then p.2.bind List.head? else sortTag E n sc' p.1.ty
  sortByTag key (alts.drop root.length)

/-- The frame the decoder pushes for alternative `a` (X.682 10.10). -/
def choiceFrame (sc' : Scope) (root : List Alt) (ext : Option (List AltAdd)) (a : Alt) : DFrame :=
  ⟨.choice, (choiceAlts root ext).map fun a => (a.name, sc', a.ty), [], a.name⟩

/-- What the decoder needs of a CHOICE value `x` with field-list `fl`: the alternative, at an index
the decoder's lookup finds, and its value, which `R` (the components' condition) reads back. -/
def ChoiceDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (sc' : Scope) (root : List Alt) (ext : Option (List AltAdd)) (x : Val)
    (fl : FieldList) : Prop :=
  let rootS := choiceRootS E n sc' root ext
  let addS := choiceAddS E n sc' root ext
  let isExt := ext.isSome || sc'.mod.header.extImplied
  ∃ (k : Nat) (a : Alt) (tg : Option (List Tag)) (y : Val) (afl : FieldList),
    x = .choice a.name y ∧ R (choiceFrame sc' root ext a :: frames) sc' a.ty y afl ∧
    ((rootS[k]? = some (a, tg) ∧ (rootS.map (·.1.name)).idxOf? a.name = some k ∧
      fl = (if isExt then .unaligned [false] :: (constrainedInt v 0 (rootS.length - 1 : Nat) k ++ afl)
        else constrainedInt v 0 (rootS.length - 1 : Nat) k ++ afl)) ∨
     (isExt = true ∧ addS[k]? = some (a, tg) ∧ (addS.map (·.1.name)).idxOf? a.name = some k ∧
      fl = .unaligned [true] :: normallySmall k ++ openField v afl))

theorem choice_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}
    {root : List Alt} {ext : Option (List AltAdd)} {x : Val} {fl : FieldList}
    (h : ChoiceDec E v n R frames sc' root ext x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.choice root ext)) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨k, a, tg, y, afl, rfl, hR, hcase⟩ := h
  have eR : sortByTag (fun p => if autoChoice sc'.mod.header.tagDefault root ext = true then p.2.bind List.head?
      else sortTag E n sc' p.1.ty) (List.take root.length (altTags E n sc' root ext)) =
      choiceRootS E n sc' root ext := rfl
  have eA : sortByTag (fun p => if autoChoice sc'.mod.header.tagDefault root ext = true then p.2.bind List.head?
      else sortTag E n sc' p.1.ty) (List.drop root.length (altTags E n sc' root ext)) =
      choiceAddS E n sc' root ext := rfl
  have hfr : (DFrame.mk FrameKind.choice (List.map (fun a => (a.name, sc', a.ty)) (choiceAlts root ext))
      [] a.name) = choiceFrame sc' root ext a := rfl
  have hr := hrec _ _ _ _ _ hR
  unfold pdecB
  simp only [eR, eA, hfr]
  rcases hcase with ⟨hk, hidx, rfl⟩ | ⟨hext, hk, hidx, rfl⟩
  · have hklt : k < (choiceRootS E n sc' root ext).length := (List.getElem?_eq_some_iff.mp hk).1
    cases hx : (ext.isSome || sc'.mod.header.extImplied)
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_false]
      rw [layout_append]
      refine Reads.bind (constrainedR_reads v p (i := (k : Int)) (by omega) (by omega)) ?_
      simp only [Int.toNat_natCast, hk, hidx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have := (hr (p + (layout v.aligned p (constrainedInt v 0 ↑((choiceRootS E n sc' root ext).length - 1) ↑k)).length)).map_pure
        (g := fun z => (Val.choice a.name z.1, constrainedInt v 0 ↑((choiceRootS E n sc' root ext).length - 1) ↑k ++ z.2))
      exact this
    · simp only [↓reduceIte]
      rw [layout_cons_unaligned, layout_append]
      refine Reads.bind (bitR_reads p false) ?_
      simp only [Bool.not_false, ↓reduceIte]
      refine Reads.bind (constrainedR_reads v _ (i := (k : Int)) (by omega) (by omega)) ?_
      simp only [Int.toNat_natCast, hk, hidx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (hr _).map_pure
        (g := fun z => (Val.choice a.name z.1, Field.unaligned [false] :: (constrainedInt v 0 ↑((choiceRootS E n sc' root ext).length - 1) ↑k ++ z.2)))
  · have hin : runInner (rec (DFrame.mk FrameKind.choice (List.map (fun a => (a.name, sc', a.ty)) (choiceAlts root ext))
        [] a.name :: frames) sc' a.ty) (octetsOf (complete v .other afl)).flatten = .ok (y, afl) :=
      runInner_complete (hr 0)
    simp only [hext, ↓reduceIte]
    rw [layout_append, layout_cons_unaligned, List.append_assoc, List.length_append, ← Nat.add_assoc]
    refine Reads.bind (bitR_reads p true) ?_
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Reads.bind (normallySmallR_reads v _ k) ?_
    simp only [hk, hidx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine Reads.bind' (b2 := []) (openR_reads v _ afl) ?_ (by simp)
    simp only [hin, openCheck_false, Bool.false_eq_true, ↓reduceIte]
    exact Reads.pure _ _

/-! ## SEQUENCE OF and SET OF (20, 22) -/

/-- What the decoder needs of a SEQUENCE OF (`isSet = false`) or SET OF value: the computed size
view, the components in the order encoded, each read back by `R`, a size of the view, and, for a
CANONICAL-PER SET OF, the components in ascending order (22.1). -/
def SeqOfDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (sc : Scope) (t : Ty) (sc' : Scope) (isSet : Bool) (el : Ty) (x : Val)
    (fl : FieldList) : Prop :=
  ∃ (C : CSet) (xs : List (Val × FieldList)), pSizeC E n sc t = some C ∧
    (∀ z ∈ xs, R (⟨if isSet then .setOf else .seqOf, [], [], ""⟩ :: frames) sc' el z.1 z.2) ∧
    x = (if isSet then Val.setOf (xs.map (·.1)) else Val.seqOf (xs.map (·.1))) ∧
    fl = seqOfFl v C (xs.map (·.2)) ∧ C.a.mem xs.length = true ∧ (C.ext = false → C.r.mem xs.length = true) ∧
    (isSet = true → v.canonical = true →
      (xs.map (·.2)).Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b) = true)

/-- The components and the length determinant (or none) of a sequence-of value, read back, and then
the rest of the decoder `K`, as the decoder's `match` has it in each arm. -/
theorem seqOfBody_reads {β : Type} {v : Variant} {m : PM (Val × FieldList)} {xs : List (Val × FieldList)}
    (hm : ∀ z ∈ xs, ∀ p, Reads m p (layout v.aligned p z.2) z) (lb : Nat) (ub : Option Nat)
    (hb : ∀ u, ub = some u → lb ≤ xs.length ∧ xs.length ≤ u) (K : List (Val × FieldList) → PM β) {res : β}
    (hK : ∀ q, Reads (K xs) q [] res) (p : Nat) :
    Reads (match ub.filter (fun x => decide (x < K64)) with
      | some u => if lb = u then ((List.replicate u ()).mapM (fun _ => m) >>= K)
        else fragFuel >>= fun f => lenDetR v (.constrained lb u) (fun _ k => (List.replicate k ()).mapM fun _ => m) true f >>= K
      | none => fragFuel >>= fun f => lenDetR v (.semi lb) (fun _ k => (List.replicate k ()).mapM fun _ => m) true f >>= K) p
      (layout v.aligned p (match ub.filter (fun x => decide (x < K64)) with
        | some u => if lb = u then (xs.map (·.2)).flatten
          else lengthDet v (.constrained lb u) (.comps (xs.map (·.2)))
        | none => lengthDet v (.semi lb) (.comps (xs.map (·.2))))) res := by
  have hk : ∀ (al' : Bool) (ys : List (Val × FieldList)), (∀ y ∈ ys, y ∈ xs) → ∀ p,
      Reads ((fun (_ : Bool) (k : Nat) => (List.replicate k ()).mapM fun _ => m) al' ys.length) p
        (layout v.aligned p (compsView.F al' ys)) ys :=
    fun al' ys hys p => compsR_reads v m xs hm ys hys p
  cases hu : ub.filter (fun x => decide (x < K64)) with
  | none =>
    have := lenDetF_app v compsView (fun (_ : Bool) (k : Nat) => (List.replicate k ()).mapM fun _ => m) xs hk (.semi lb) true trivial (by intro h; cases h) p (hK _)
    simpa [compsView] using this
  | some u =>
    have hu' : ub = some u ∧ u < K64 := by
      cases ub with
      | none => simp at hu
      | some w => simp only [Option.filter_some] at hu; split_ifs at hu with h <;> simp_all
    obtain ⟨hl1, hl2⟩ := hb u hu'.1
    by_cases h1 : lb = u
    · simp only [h1, ↓reduceIte]
      have := (compsR_reads v m xs hm xs (fun _ h => h) p).bind (hK _)
      rw [show xs.length = u by omega] at this
      simpa using this
    · simp only [h1, ↓reduceIte]
      have := lenDetF_app v compsView (fun (_ : Bool) (k : Nat) => (List.replicate k ()).mapM fun _ => m) xs hk (.constrained lb u) true (fun _ => ⟨hl1, hl2⟩)
        (by intro h; cases h) p (hK _)
      simpa [compsView] using this

theorem seqOf_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}
    {el : Ty} {x : Val} {fl : FieldList}
    (h : SeqOfDec E v n R frames sc t sc' false el x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.sequenceOf el)) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨C, xs, hC, hR, rfl, rfl, ha, hr, -⟩ := h
  have hm : ∀ z ∈ xs, ∀ p, Reads (rec (⟨.seqOf, [], [], ""⟩ :: frames) sc' el) p (layout v.aligned p z.2) z :=
    fun z hz p => hrec _ _ _ _ _ (hR z hz) p
  have hD := pSizeC_sound hC
  unfold pdecB
  simp only [hC]
  unfold seqOfFl sizedFl
  simp only [List.length_map]
  cases hext : C.ext
  · have hrm := hr hext
    have hb := sized_bounds hD ((hD.1 xs.length).mpr hrm)
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hsb := sizeBounds_reads C false (fun _ => rfl) p
    simp only [hext, Bool.false_eq_true, ↓reduceIte] at hsb
    rw [← List.nil_append (layout v.aligned p _)]
    refine Reads.bind hsb ?_
    simp only [List.length_nil, Nat.add_zero]
    refine seqOfBody_reads hm _ _ hb _ ?_ p
    intro q
    simp [ha, hrm, hext]
    exact Reads.pure _ _
  · simp only [↓reduceIte]
    cases hrm : C.r.mem xs.length
    · have hsb := sizeBounds_reads C true (fun h => by simp_all) p
      simp only [hext, ↓reduceIte] at hsb
      simp only [hrm, Bool.false_eq_true, ↓reduceIte, layout_cons_unaligned]
      refine Reads.bind hsb ?_
      refine seqOfBody_reads hm 0 none (by simp) _ ?_ _
      intro q
      simp [ha, hrm, hext]
      exact Reads.pure _ _
    · have hb := sized_bounds hD ((hD.1 xs.length).mpr hrm)
      have hsb := sizeBounds_reads C false (fun h => rfl) p
      simp only [hext, ↓reduceIte] at hsb
      simp only [hrm, ↓reduceIte, layout_cons_unaligned]
      refine Reads.bind hsb ?_
      refine seqOfBody_reads hm _ _ hb _ ?_ _
      intro q
      simp [ha, hrm, hext]
      exact Reads.pure _ _

theorem setOf_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}
    {el : Ty} {x : Val} {fl : FieldList}
    (h : SeqOfDec E v n R frames sc t sc' true el x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' (.setOf el)) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨C, xs, hC, hR, rfl, rfl, ha, hr, hcan⟩ := h
  have hm : ∀ z ∈ xs, ∀ p, Reads (rec (⟨.setOf, [], [], ""⟩ :: frames) sc' el) p (layout v.aligned p z.2) z :=
    fun z hz p => hrec _ _ _ _ _ (hR z hz) p
  have hD := pSizeC_sound hC
  unfold pdecB
  simp only [hC]
  unfold seqOfFl sizedFl
  simp only [List.length_map]
  cases hext : C.ext
  · have hrm := hr hext
    have hb := sized_bounds hD ((hD.1 xs.length).mpr hrm)
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hsb := sizeBounds_reads C false (fun _ => rfl) p
    simp only [hext, Bool.false_eq_true, ↓reduceIte] at hsb
    rw [← List.nil_append (layout v.aligned p _)]
    refine Reads.bind hsb ?_
    simp only [List.length_nil, Nat.add_zero]
    refine seqOfBody_reads hm _ _ hb _ ?_ p
    intro q
    by_cases hv : v.canonical = true
    · simp [ha, hrm, hext, hv, hcan rfl hv]; exact Reads.pure _ _
    · simp [ha, hrm, hext, hv]; exact Reads.pure _ _
  · simp only [↓reduceIte]
    cases hrm : C.r.mem xs.length
    · have hsb := sizeBounds_reads C true (fun h => by simp_all) p
      simp only [hext, ↓reduceIte] at hsb
      simp only [hrm, Bool.false_eq_true, ↓reduceIte, layout_cons_unaligned]
      refine Reads.bind hsb ?_
      refine seqOfBody_reads hm 0 none (by simp) _ ?_ _
      intro q
      by_cases hv : v.canonical = true
      · simp [ha, hrm, hext, hv, hcan rfl hv]; exact Reads.pure _ _
      · simp [ha, hrm, hext, hv]; exact Reads.pure _ _
    · have hb := sized_bounds hD ((hD.1 xs.length).mpr hrm)
      have hsb := sizeBounds_reads C false (fun h => rfl) p
      simp only [hext, ↓reduceIte] at hsb
      simp only [hrm, ↓reduceIte, layout_cons_unaligned]
      refine Reads.bind hsb ?_
      refine seqOfBody_reads hm _ _ hb _ ?_ _
      intro q
      by_cases hv : v.canonical = true
      · simp [ha, hrm, hext, hv, hcan rfl hv]; exact Reads.pure _ _
      · simp [ha, hrm, hext, hv]; exact Reads.pure _ _

/-! ## Open types (11.2) -/

/-- What the decoder needs of an open type's value: the table constraint gives its type (`hint`),
the value is a value of it that `R` reads back, and passes `valSemB`. -/
def OpenDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (hint : Option (Scope × Ty)) (x : Val) (fl : FieldList) : Prop :=
  ∃ (sc'' : Scope) (ty : Ty) (y : Val) (afl : FieldList), hint = some (sc'', ty) ∧ x = .open_ ty y ∧
    R [] sc'' ty y afl ∧ valSemB E n sc'' ty y = true ∧ fl = openField v afl

theorem open_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope}
    {x : Val} {fl : FieldList} (h : OpenDec E v n R hint x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' .openType) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨sc'', ty, y, afl, rfl, rfl, hR, hsem, rfl⟩ := h
  have hin := runInner_complete (hrec _ _ _ _ _ hR 0)
  unfold pdecB
  simp only
  refine Reads.bind' (b2 := []) (openR_reads v p afl) ?_ (by simp)
  simp only [hin, openCheck_false, hsem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact Reads.pure _ _

/-! ## SEQUENCE and SET (19, 21) -/

/-- What the decoder needs of the components `es` of a SEQUENCE or SET (or of an addition group),
read after `acc`: for each, its value and field-list (`R` reads it back, `presentOkB` holds) or
nothing (it is not mandatory, `absentOkB` holds); `cs` is `acc` with the values read. -/
def CompsDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (all : List (String × Scope × Ty)) (root : Bool) :
    List Entry → List (String × Val) → List (Option (Val × FieldList)) → List (String × Val) → Prop
  | [], acc, outs, cs => outs = [] ∧ cs = acc
  | en :: es, acc, outs, cs => match outs with
    | [] => False
    | some (x, f) :: outs' => R (⟨.seq, all, acc, en.name⟩ :: frames) en.scope en.ty x f ∧
        presentOkB E v n en x = true ∧ CompsDec E v n R frames all root es (acc ++ [(en.name, x)]) outs' cs
    | none :: outs' => en.presence.isMandatory = false ∧ absentOkB E n root en = true ∧
        CompsDec E v n R frames all root es acc outs' cs

/-- The preamble bits (19.2) for components `es` with outcomes `outs`. -/
def preOf (es : List Entry) (outs : List (Option FieldList)) : Bits :=
  (es.zip outs).filterMap fun (e, o) => if e.presence.isMandatory then none else some o.isSome

theorem compsR_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    (frames : List DFrame) (all : List (String × Scope × Ty)) (root : Bool) :
    ∀ (es : List Entry) (acc : List (String × Val)) (outs : List (Option (Val × FieldList))) (cs : List (String × Val)),
      CompsDec E v n R frames all root es acc outs cs → ∀ (p : Nat) (more : Bits),
      Reads (compsR E v n rec frames all root es (preOf es (outs.map (Option.map (·.2))) ++ more) acc) p
        (layout v.aligned p ((outs.map (Option.map (·.2))).flatMap (·.getD [])))
        (cs, outs.map (Option.map (·.2)))
  | [], acc, outs, cs, h, p, more => by
    obtain ⟨rfl, h2⟩ := h
    subst h2
    simpa [compsR] using Reads.pure (cs, ([] : List (Option FieldList))) p
  | en :: es, acc, outs, cs, h, p, more => by
    cases outs with
    | nil => exact h.elim
    | cons o outs' =>
      cases o with
      | some xf =>
        obtain ⟨x, f⟩ := xf
        obtain ⟨hR, hok, hd⟩ := h
        have ih := compsR_complete hrec frames all root es _ outs' cs hd
        simp only [List.map_cons, Option.map_some, List.flatMap_cons, Option.getD_some, layout_append]
        unfold compsR
        have hpre : (if en.presence.isMandatory = true then (true, preOf (en :: es) (some f :: outs'.map (Option.map (·.2))) ++ more)
            else ((preOf (en :: es) (some f :: outs'.map (Option.map (·.2))) ++ more).headD false,
              (preOf (en :: es) (some f :: outs'.map (Option.map (·.2))) ++ more).tail)) =
            (true, preOf es (outs'.map (Option.map (·.2))) ++ more) := by
          cases hm : en.presence.isMandatory <;> simp [preOf, hm]
        simp only [hpre, ↓reduceIte]
        refine Reads.bind (hrec _ _ _ _ _ hR p) ?_
        simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have := (ih (p + (layout v.aligned p f).length) more).map_pure (g := fun r => (r.1, some f :: r.2))
        simpa using this
      | none =>
        obtain ⟨hm, hok, hd⟩ := h
        have ih := compsR_complete hrec frames all root es acc outs' cs hd
        simp only [List.map_cons, Option.map_none, List.flatMap_cons, Option.getD_none, List.nil_append]
        unfold compsR
        have hpre : (if en.presence.isMandatory = true then (true, preOf (en :: es) (none :: outs'.map (Option.map (·.2))) ++ more)
            else ((preOf (en :: es) (none :: outs'.map (Option.map (·.2))) ++ more).headD false,
              (preOf (en :: es) (none :: outs'.map (Option.map (·.2))) ++ more).tail)) =
            (false, preOf es (outs'.map (Option.map (·.2))) ++ more) := by
          simp [preOf, hm]
        simp only [hpre, Bool.false_eq_true, ↓reduceIte, hok, Bool.not_true]
        have := (ih p more).map_pure (g := fun r => (r.1, none :: r.2))
        simpa using this

theorem compsDec_length {E : Env} {v : Variant} {n : Nat} {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    {frames : List DFrame} {all : List (String × Scope × Ty)} {root : Bool} :
    ∀ {es : List Entry} {acc : List (String × Val)} {outs : List (Option (Val × FieldList))} {cs : List (String × Val)},
      CompsDec E v n R frames all root es acc outs cs → outs.length = es.length
  | [], _, outs, _, h => by obtain ⟨rfl, _⟩ := h; rfl
  | _ :: es, _, outs, _, h => by
    cases outs with
    | nil => exact h.elim
    | cons o outs' =>
      cases o with
      | some xf => obtain ⟨x, f⟩ := xf; simp only [List.length_cons, compsDec_length h.2.2]
      | none => simp only [List.length_cons, compsDec_length h.2.2]

theorem preOf_length : ∀ (es : List Entry) (outs : List (Option FieldList)), outs.length = es.length →
    (preOf es outs).length = (es.filter fun e => !e.presence.isMandatory).length
  | [], [], _ => rfl
  | e :: es, o :: outs, h => by
    have ih := preOf_length es outs (by simpa using h)
    cases hm : e.presence.isMandatory <;> simp_all [preOf, List.filter_cons]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The preamble's fields (19.2, 19.3), as `seqRootFields` has them. -/
def preFields (v : Variant) (pre : Bits) : FieldList :=
  if pre = [] then []
  else if pre.length < K64 then [.unaligned pre]
  else lengthDet v (.constrained pre.length pre.length) (.field false (bitUnits pre))

theorem seqRootFields_eq (v : Variant) (es : List Entry) (outs : List (Option FieldList)) :
    seqRootFields v es outs = preFields v (preOf es outs) ++ outs.flatMap (·.getD []) := rfl

theorem preambleR_reads (v : Variant) (es : List Entry) (outs : List (Option FieldList))
    (hl : outs.length = es.length) (p : Nat) :
    Reads (preambleR v es) p (layout v.aligned p (preFields v (preOf es outs))) (preOf es outs) := by
  have hk := preOf_length es outs hl
  unfold preambleR preFields
  rw [← hk]
  by_cases h0 : preOf es outs = []
  · simp only [h0, List.length_nil, ↓reduceIte, layout_nil]; exact Reads.pure _ _
  · have h0' : (preOf es outs).length ≠ 0 := by simpa using h0
    simp only [h0, h0', ↓reduceIte]
    by_cases h1 : (preOf es outs).length < K64
    · simp only [h1, ↓reduceIte, layout_unaligned]; exact takeN_reads p _
    · simp only [h1, ↓reduceIte]
      obtain ⟨b1, b2, b3⟩ := bitUnits_spec (preOf es outs)
      have := (lenDetF_reads v fieldView (unitsR v 1) (bitUnits (preOf es outs))
        (fun al' ys hys p' => unitsR_reads v 1 al' p' ys (fun u hu => b1 u (hys u hu)))
        (.constrained (preOf es outs).length (preOf es outs).length) false
        (fun _ => by rw [b3]; omega) (by intro h; cases h) p).map_pure (g := List.flatten)
      rw [b2] at this
      simpa [fieldView, bind_assoc] using this

/-- The preamble and the components of a SEQUENCE, SET or addition group, read back, then `K`. -/
theorem seqRoot_reads {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {all : List (String × Scope × Ty)} {root : Bool} {es : List Entry}
    {acc : List (String × Val)} {outs : List (Option (Val × FieldList))} {cs : List (String × Val)}
    (hd : CompsDec E v n R frames all root es acc outs cs) (p : Nat) {β : Type}
    {K : List (String × Val) × List (Option FieldList) → PM β} {b2 : Bits} {res : β}
    (hK : Reads (K (cs, outs.map (Option.map (·.2))))
      (p + (layout v.aligned p (seqRootFields v es (outs.map (Option.map (·.2))))).length) b2 res) :
    Reads (preambleR v es >>= fun pre => compsR E v n rec frames all root es pre acc >>= K) p
      (layout v.aligned p (seqRootFields v es (outs.map (Option.map (·.2)))) ++ b2) res := by
  have hl : (outs.map (Option.map (·.2))).length = es.length := by simp [compsDec_length hd]
  rw [seqRootFields_eq, layout_append, List.append_assoc]
  refine Reads.bind (preambleR_reads v es _ hl p) ?_
  have hc := compsR_complete hrec frames all root es acc outs cs hd
    (p + (layout v.aligned p (preFields v (preOf es (outs.map (Option.map (·.2)))))).length) []
  rw [List.append_nil] at hc
  refine Reads.bind hc ?_
  simpa [seqRootFields_eq, layout_append, Nat.add_assoc] using hK

/-- What the decoder needs of the extension additions `adds` of a SEQUENCE or SET, read after the
components `cs`: for each, nothing (its components may be absent) or the field-list of its open
type field's contents (a single component, or a group as a sequence of its components). `csF` is
`cs` with the values read. -/
def AddsDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (all : List (String × Scope × Ty)) :
    List (List Entry × Bool) → List (String × Val) → List (Option FieldList) → List (String × Val) → Prop
  | [], cs, outs, csF => outs = [] ∧ csF = cs
  | (es, grp) :: rest, cs, outs, csF => match outs with
    | [] => False
    | none :: outs' => es.all (absentOkB E n false) = true ∧ AddsDec E v n R frames all rest cs outs' csF
    | some f :: outs' => (∃ cs',
        (if grp then ∃ gouts : List (Option (Val × FieldList)),
            CompsDec E v n R frames all false es cs gouts cs' ∧ (gouts.all Option.isNone) = false ∧
            ((es.zip (gouts.map (Option.map (·.2)))).all fun p => !p.1.presence.isMandatory || p.2.isSome) = true ∧
            f = seqRootFields v es (gouts.map (Option.map (·.2)))
          else ∃ e y, es = [e] ∧ R (⟨.seq, all, cs, e.name⟩ :: frames) e.scope e.ty y f ∧
            presentOkB E v n e y = true ∧ cs' = cs ++ [(e.name, y)]) ∧
        AddsDec E v n R frames all rest cs' outs' csF)

/-- The open type fields of the additions present. -/
def addsFields (v : Variant) (outs : List (Option FieldList)) : FieldList :=
  outs.flatMap fun o => match o with
    | some f => openField v f
    | none => []

theorem runInner_complete' {α : Type} {v : Variant} {m : PM (α × FieldList)} {a : α} {afl : FieldList}
    (h : Reads m 0 (layout v.aligned 0 afl) (a, afl)) :
    runInner m (octetsOf (complete v .other afl)).flatten = .ok (a, afl) := by
  obtain ⟨pad, he, h8⟩ := complete_other v afl
  obtain ⟨_, o2, _⟩ := octetsOf_spec _ _ (show (complete v .other afl).length = 8 * ((complete v .other afl).length / 8) by omega)
  rw [o2, he]
  unfold runInner
  rw [h pad]; rfl

theorem addStep_absent {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {frames : List DFrame} {all : List (String × Scope × Ty)} {cs : List (String × Val)} {oa : List (Option FieldList)}
    {es : List Entry} {grp : Bool} (hes : es.all (absentOkB E n false) = true) (p : Nat) :
    Reads (addStep E v n rec frames all (cs, oa) ((es, grp), false)) p [] (cs, oa ++ [none]) := by
  unfold addStep
  simp only [Bool.not_false, ↓reduceIte, hes, Bool.not_true, Bool.false_eq_true]
  exact Reads.pure _ _

theorem addStep_present {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {all : List (String × Scope × Ty)} {cs cs' : List (String × Val)} {oa : List (Option FieldList)}
    {es : List Entry} {grp : Bool} {f : FieldList}
    (h : if grp then ∃ gouts : List (Option (Val × FieldList)),
            CompsDec E v n R frames all false es cs gouts cs' ∧ (gouts.all Option.isNone) = false ∧
            ((es.zip (gouts.map (Option.map (·.2)))).all fun p => !p.1.presence.isMandatory || p.2.isSome) = true ∧
            f = seqRootFields v es (gouts.map (Option.map (·.2)))
          else ∃ e y, es = [e] ∧ R (⟨.seq, all, cs, e.name⟩ :: frames) e.scope e.ty y f ∧
            presentOkB E v n e y = true ∧ cs' = cs ++ [(e.name, y)]) (p : Nat) :
    Reads (addStep E v n rec frames all (cs, oa) ((es, grp), true)) p (layout v.aligned p (openField v f))
      (cs', oa ++ [some f]) := by
  unfold addStep
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Reads.bind' (b2 := []) (openR_reads v p f) ?_ (by simp)
  cases grp
  · obtain ⟨e, y, rfl, hR, hok, rfl⟩ := h
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runInner_complete' (a := cs ++ [(e.name, y)]) (afl := f) ?inner]
    · simp only [openCheck_false, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _
    · refine Reads.bind' (b2 := []) (hrec _ _ _ _ _ hR 0) ?_ (by simp)
      simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _
  · obtain ⟨gouts, hd, hne, hmand, rfl⟩ := h
    simp only [↓reduceIte]
    rw [runInner_complete' (a := cs') ?inner2]
    · simp only [openCheck_false, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _
    · rw [← List.append_nil (layout v.aligned 0 _)]
      refine seqRoot_reads hrec hd 0 ?_
      have hne' : ((gouts.map (Option.map (·.2))).all Option.isNone) = false := by
        simpa [List.all_map, Function.comp_def] using hne
      simp only [hne', hmand, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _

theorem addFold_reads {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    (frames : List DFrame) (all : List (String × Scope × Ty)) :
    ∀ (adds : List (List Entry × Bool)) (cs : List (String × Val)) (oa addOuts : List (Option FieldList))
      (csF : List (String × Val)), AddsDec E v n R frames all adds cs addOuts csF → ∀ p,
      Reads ((adds.zip (addOuts.map Option.isSome)).foldlM (addStep E v n rec frames all) (cs, oa)) p
        (layout v.aligned p (addsFields v addOuts)) (csF, oa ++ addOuts)
  | [], cs, oa, addOuts, csF, h, p => by
    obtain ⟨rfl, h2⟩ := h
    subst h2
    simpa [addsFields] using Reads.pure (csF, oa) p
  | (es, grp) :: rest, cs, oa, addOuts, csF, h, p => by
    cases addOuts with
    | nil => exact h.elim
    | cons o outs' =>
      cases o with
      | none =>
        obtain ⟨hes, hd⟩ := h
        simp only [List.map_cons, Option.isSome_none, List.zip_cons_cons, List.foldlM_cons]
        rw [show addsFields v (none :: outs') = [] ++ addsFields v outs' from rfl, layout_append]
        refine Reads.bind (addStep_absent hes p) ?_
        have := addFold_reads hrec frames all rest cs (oa ++ [none]) outs' csF hd (p + (layout v.aligned p []).length)
        simpa using this
      | some f =>
        obtain ⟨cs', hone, hd⟩ := h
        simp only [List.map_cons, Option.isSome_some, List.zip_cons_cons, List.foldlM_cons]
        rw [show addsFields v (some f :: outs') = openField v f ++ addsFields v outs' from rfl, layout_append]
        refine Reads.bind (addStep_present hrec hone p) ?_
        have := addFold_reads hrec frames all rest cs' (oa ++ [some f]) outs' csF hd
          (p + (layout v.aligned p (openField v f)).length)
        simpa using this

theorem addsDec_length {E : Env} {v : Variant} {n : Nat} {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    {frames : List DFrame} {all : List (String × Scope × Ty)} :
    ∀ {adds : List (List Entry × Bool)} {cs : List (String × Val)} {outs : List (Option FieldList)} {csF : List (String × Val)},
      AddsDec E v n R frames all adds cs outs csF → outs.length = adds.length
  | [], _, outs, _, h => by obtain ⟨rfl, _⟩ := h; rfl
  | (es, grp) :: rest, _, outs, _, h => by
    cases outs with
    | nil => exact h.elim
    | cons o outs' =>
      cases o with
      | none => simp only [List.length_cons, addsDec_length h.2]
      | some f => obtain ⟨_, _, hd⟩ := h; simp only [List.length_cons, addsDec_length hd]

/-- What the decoder needs of a SEQUENCE or SET value with root components `rootEs` (in the order
encoded) and additions `adds`: distinct component names, an addition that is not a group has one
component, the root components read back (`CompsDec`), and either no addition present, or
(extensible) some present and read back (`AddsDec`); the value lists the components read, in the
order read. -/
def SeqDec (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (isExt : Bool) (rootEs : List Entry) (adds : List (List Entry × Bool))
    (x : Val) (fl : FieldList) : Prop :=
  let allEs := rootEs ++ adds.flatMap (·.1)
  let all := frameComps allEs
  decide (allEs.map (·.name)).Nodup = true ∧ (adds.all fun a => a.2 || a.1.length == 1) = true ∧
  ∃ (rootOuts : List (Option (Val × FieldList))) (csR : List (String × Val)),
    CompsDec E v n R frames all true rootEs [] rootOuts csR ∧
    ((adds.all (fun a => a.1.all (absentOkB E n false)) = true ∧ x = .seq csR ∧
      fl = (if isExt then .unaligned [false] :: seqRootFields v rootEs (rootOuts.map (Option.map (·.2)))
        else seqRootFields v rootEs (rootOuts.map (Option.map (·.2))))) ∨
     (isExt = true ∧ ∃ (addOuts : List (Option FieldList)) (cs : List (String × Val)),
       AddsDec E v n R frames all adds csR addOuts cs ∧ addOuts.any Option.isSome = true ∧ x = .seq cs ∧
       fl = .unaligned [true] :: seqRootFields v rootEs (rootOuts.map (Option.map (·.2))) ++
         (lengthDet v .normallySmall (.field false (bitUnits (addOuts.map Option.isSome))) ++ addsFields v addOuts)))

theorem seqR_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {isExt : Bool} {rootEs : List Entry} {adds : List (List Entry × Bool)}
    {x : Val} {fl : FieldList} (h : SeqDec E v n R frames isExt rootEs adds x fl) (p : Nat) :
    Reads (seqR E v n rec frames isExt rootEs adds) p (layout v.aligned p fl) (x, fl) := by
  obtain ⟨hnd, hone, rootOuts, csR, hd, hcase⟩ := h
  have hmapIs : ∀ (bs : Bits), (bitUnits bs).map (fun u => u.headD false) = bs := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp only [bitUnits, List.map_cons, List.headD_cons] at ih ⊢; rw [ih]
  unfold seqR
  simp only [hnd, hone, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases hcase with ⟨habs, rfl, rfl⟩ | ⟨hext, addOuts, cs, had, hany, rfl, rfl⟩
  · cases hx : isExt
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      rw [← List.append_nil (layout v.aligned p _)]
      refine seqRoot_reads hrec hd p ?_
      simp only [Bool.not_false, ↓reduceIte, habs, Bool.not_true, Bool.false_eq_true]
      exact Reads.pure _ _
    · simp only [↓reduceIte]
      rw [layout_cons_unaligned, ← List.append_nil (layout v.aligned (p + [false].length) _)]
      refine Reads.bind (bitR_reads p false) ?_
      refine seqRoot_reads hrec hd _ ?_
      simp only [Bool.not_false, ↓reduceIte, habs, Bool.not_true, Bool.false_eq_true]
      exact Reads.pure _ _
  · simp only [hext, ↓reduceIte]
    rw [layout_append, layout_cons_unaligned, List.append_assoc]
    refine Reads.bind (bitR_reads p true) ?_
    refine seqRoot_reads hrec hd _ ?_
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hlen := addsDec_length had
    obtain ⟨b1, b2, b3⟩ := bitUnits_spec (addOuts.map Option.isSome)
    have hpos : 1 ≤ (bitUnits (addOuts.map Option.isSome)).length := by
      rw [b3, List.length_map]
      cases addOuts with
      | nil => simp at hany
      | cons _ _ => simp
    rw [layout_append]
    simp only [List.length_append, List.length_singleton, Nat.add_assoc]
    refine lenDetF_app v fieldView (unitsR v 1) (bitUnits (addOuts.map Option.isSome))
      (fun al' ys hys p' => unitsR_reads v 1 al' p' ys (fun u hu => b1 u (hys u hu))) .normallySmall false
      trivial (fun _ => hpos) _ ?_
    simp only [hmapIs, List.length_map, hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [← List.append_nil (layout v.aligned _ (addsFields v addOuts))]
    simp only [fieldView, Nat.add_assoc]
    refine Reads.bind (addFold_reads hrec _ _ adds csR [] addOuts cs had _) ?_
    have hany' : (addOuts.map Option.isSome).any id = true := by
      simpa [List.any_map, Function.comp_def] using hany
    simp only [List.nil_append, hany', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact Reads.pure _ _

/-! ## What the decoder needs, by fuel -/

/-- The root components of a SET in canonical tag order (21), as the decoder and `perB` sort them. -/
def setRootEs (E : Env) (n : Nat) (sc' : Scope) (r : List Comp) (e : Option (List ExtAdd)) (r2 : List Comp) :
    List Entry :=
  let tagged := entryTags E n sc' r e r2
  let auto := autoSeq sc'.mod.header.tagDefault r e r2
  let key (p : Entry × Option (List Tag)) : Option Tag :=
    if auto then p.2.bind List.head? else sortTag E n p.1.scope p.1.ty
  (sortByTag key (tagged.filter (·.1.addition.isNone))).map (·.1)

/-- What the decoder needs, beyond `perB`, to read back a value `x` of the built-in type `bt`
encoded as `fl`: for the leaf types, that the PER view is computed and the value is in the form the
decoder returns; for the composite types, the structure the decoder reads (`SeqDec`, `SeqOfDec`,
`ChoiceDec`, `OpenDec`), with `R` for the components. EMBEDDED PDV, EXTERNAL, CHARACTER STRING and
the time types are not decoded. -/
def PDecB (E : Env) (v : Variant) (n : Nat) (R : List DFrame → Scope → Ty → Val → FieldList → Prop)
    (frames : List DFrame) (hint : Option (Scope × Ty)) (sc : Scope) (t : Ty) (sc' : Scope) (bt : Ty)
    (x : Val) (fl : FieldList) : Prop :=
  match bt with
  | .boolean => True
  | .integer _ => (pIntC E n sc t).isSome = true
  | .enumerated root ext => ((enumNumbers root ext).map (·.2)).Nodup
  | .real => ∀ r, x = .real r → r.Wf
  | .bitString named => (pSizeC E n sc t).isSome = true ∧
      (named ≠ [] → ∀ bs, x = .bits bs → NamedBitsSent (pSize E n sc t) bs bs)
  | .octetString => (pSizeC E n sc t).isSome = true
  | .null => True
  | .sequence r e r2 =>
    SeqDec E v n R frames (e.isSome || sc'.mod.header.extImplied)
      (splitEntries (entries E n sc' r e r2) e).1 (splitEntries (entries E n sc' r e r2) e).2 x fl
  | .set r e r2 =>
    SeqDec E v n R frames (e.isSome || sc'.mod.header.extImplied) (setRootEs E n sc' r e r2)
      (splitEntries ((entryTags E n sc' r e r2).map (·.1)) e).2 x fl
  | .sequenceOf el => SeqOfDec E v n R frames sc t sc' false el x fl
  | .setOf el => SeqOfDec E v n R frames sc t sc' true el x fl
  | .choice root ext => ChoiceDec E v n R frames sc' root ext x fl
  | .objectIdentifier => ∀ arcs, x = .oid arcs → X690.OidWf arcs
  | .relativeOid => True
  | .oidIri => ∀ a, x = .iri a → X690.decIri false (X690.iriContents a) = some a
  | .relativeOidIri => ∀ a, x = .iri a → X690.decIri true (X690.relIriContents a) = some a
  | .restricted k => if k.knownMultiplier then (pStrC E n sc t).isSome = true else X690.StrBound k x
  | .generalizedTime | .utcTime | .objectDescriptor => True
  | .openType => OpenDec E v n R hint x fl
  | _ => False

/-- `PDec E v n frames sc t x fl`: the decoder, at fuel `n`, with enclosing values `frames`, can read
back the value `x` of `t` encoded as `fl`: `PDecB` at each type, the components needing `per` and
`PDec` at one less fuel. -/
def PDec (E : Env) (v : Variant) : Nat → List DFrame → Scope → Ty → Val → FieldList → Prop
  | 0, _, _, _, _, _ => False
  | n + 1, frames, sc, t, x, fl => match builtin E n sc t with
    | some (sc', bt) => PDecB E v n (fun fr sc t y afl => per E v n sc t y afl ∧ PDec E v n fr sc t y afl)
        (framesIn frames t) (hintOf E n frames sc t) sc t sc' bt x fl ∧
        contentsOkB E v n (pdec E v n) sc t x = true
    | none => False

theorem namedBitsSent_unique {S : PSet Nat} {bs s1 s2 : Bits} (h1 : NamedBitsSent S bs s1)
    (h2 : NamedBitsSent S bs s2) : s1 = s2 := by
  obtain ⟨k1, e1, l1, a1, m1⟩ := h1
  obtain ⟨k2, e2, l2, a2, m2⟩ := h2
  have : k1 = k2 := le_antisymm (m1 k2 l2 a2) (m2 k1 l1 a1)
  rw [e1, e2, this]

theorem pdecB_complete {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    {R : List DFrame → Scope → Ty → Val → FieldList → Prop}
    (hrec : ∀ fr sc t y afl, R fr sc t y afl → ∀ p, Reads (rec fr sc t) p (layout v.aligned p afl) (y, afl))
    {frames : List DFrame} {hint : Option (Scope × Ty)} {sc : Scope} {t : Ty} {sc' : Scope} {bt : Ty}
    {x : Val} {fl : FieldList}
    (hper : perB E v n (per E v n) sc t sc' bt x fl) (hd : PDecB E v n R frames hint sc t sc' bt x fl) (p : Nat) :
    Reads (pdecB E v n rec frames hint sc t sc' bt) p (layout v.aligned p fl) (x, fl) := by
  cases bt with
  | boolean =>
    cases x <;> simp only [perB] at hper
    subst hper; exact bool_complete _ p
  | integer z =>
    cases x <;> simp only [perB] at hper
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hd
    exact int_complete hC hper p
  | enumerated root ext =>
    cases x <;> simp only [perB] at hper
    exact enum_complete hper hd p
  | real =>
    cases x <;> simp only [perB] at hper
    obtain ⟨os, hos, rfl⟩ := hper
    exact real_complete hos (hd _ rfl) p
  | bitString named =>
    cases x <;> simp only [perB] at hper
    rename_i bs
    obtain ⟨hs, hn⟩ := hd
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨sent, hsent, hf⟩ := hper
    have hsb : sent = bs := by
      by_cases h0 : named = []
      · simpa [h0] using hsent
      · simp only [h0, ↓reduceIte] at hsent
        exact namedBitsSent_unique hsent (hn h0 bs rfl)
    subst hsb
    exact bits_complete hC hf (fun h0 => hn h0 _ rfl) p
  | octetString =>
    cases x <;> simp only [perB] at hper
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hd
    exact octets_complete hC hper p
  | null =>
    cases x <;> simp only [perB] at hper
    subst hper; exact null_complete p
  | sequence r e r2 =>
    unfold pdecB
    exact seqR_complete hrec hd p
  | set r e r2 =>
    unfold pdecB
    exact seqR_complete hrec hd p
  | sequenceOf el => exact seqOf_complete hrec hd p
  | setOf el => exact setOf_complete hrec hd p
  | choice root ext => exact choice_complete hrec hd p
  | objectIdentifier =>
    cases x <;> simp only [perB] at hper
    subst hper; exact oid_complete (hd _ rfl) p
  | relativeOid =>
    cases x <;> simp only [perB] at hper
    subst hper; exact relOid_complete _ p
  | oidIri =>
    cases x <;> simp only [perB] at hper
    subst hper; exact oidIri_complete (hd _ rfl) p
  | relativeOidIri =>
    cases x <;> simp only [perB] at hper
    subst hper; exact relOidIri_complete (hd _ rfl) p
  | restricted k =>
    simp only [perB] at hper
    simp only [PDecB] at hd
    cases hk : k.knownMultiplier
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hper hd
      exact otherString_complete hk hper hd p
    · simp only [hk, ↓reduceIte] at hper hd
      obtain ⟨cs, rfl, hkm⟩ := hper
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hd
      exact km_complete hk hP hkm p
  | generalizedTime => simp only [perB] at hper; exact genTime_complete hper p
  | utcTime => simp only [perB] at hper; exact utcTime_complete hper p
  | objectDescriptor => simp only [perB] at hper; exact objectDescriptor_complete hper p
  | openType => exact open_complete hrec hd p
  | _ => exact hd.elim

/-! ## Completeness -/

/-- **Completeness of the decoder**: every encoding `per` relates to a value the decoder can read
back (`PDec`), followed by anything, is read back by `pdec` as that value and that field-list. -/
theorem pdec_complete (E : Env) (v : Variant) : ∀ (n : Nat) (frames : List DFrame) (sc : Scope) (t : Ty)
    (x : Val) (fl : FieldList), per E v n sc t x fl → PDec E v n frames sc t x fl →
    ∀ p, Reads (pdec E v n frames sc t) p (layout v.aligned p fl) (x, fl)
  | 0, _, _, _, _, _, hper, _, _ => by simp [per] at hper
  | n + 1, frames, sc, t, x, fl, hper, hd, p => by
    unfold per at hper
    unfold PDec at hd
    unfold pdec
    cases hb : builtin E n sc t with
    | none => rw [hb] at hd; exact hd.elim
    | some sb =>
      obtain ⟨sc', bt⟩ := sb
      rw [hb] at hper hd
      simp only
      rw [← List.append_nil (layout v.aligned p fl)]
      refine Reads.bind (pdecB_complete (R := fun fr sc t y afl => per E v n sc t y afl ∧ PDec E v n fr sc t y afl)
        (fun fr sc t y afl h p => pdec_complete E v n fr sc t y afl h.1 h.2 p) hper hd.1 p) ?_
      simp only [hd.2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact Reads.pure _ _

/-- `decode` accepts the complete encoding (11.1) of every value it can read back that is a value
of the type as far as `valSemB` and `presentOkB` check, and returns that value. -/
theorem decode_complete {E : Env} {v : Variant} {fuel : Nat} {m : Module} {t : Ty} {x : Val} {fl : FieldList}
    (hper : per E v fuel (.ofModule m) t x fl) (hd : PDec E v fuel [] (.ofModule m) t x fl)
    (hs : valSemB E fuel (.ofModule m) t x = true) (hp : X690.presentOkB E fuel (.ofModule m) t x = true) :
    decode E v fuel m t (bitsToOctets (complete v .other fl)) = .ok x := by
  obtain ⟨pad, he, h8⟩ := complete_other v fl
  have hbits : bitsOf (bitsToOctets (complete v .other fl)) = complete v .other fl :=
    bitsOf_bitsToOctets _ h8
  have hrun := pdec_complete E v fuel [] (.ofModule m) t x fl hper hd 0 pad
  rw [← he] at hrun
  unfold decode
  simp only [hbits]
  rw [hrun]
  simp only [completeFast_eq]
  show (Except.ok ((x, fl), _) >>= _) = _
  simp [bind, Except.bind, hs, hp]
  rfl

/-- **Unambiguity** (X.691 8.4, for the values the decoder reads back): two values of `t` whose
encodings have the same complete encoding are the same value, with the same field-list. -/
theorem per_unambiguous {E : Env} {v : Variant} {n : Nat} {frames : List DFrame} {sc : Scope} {t : Ty}
    {x x' : Val} {fl fl' : FieldList}
    (h1 : per E v n sc t x fl) (d1 : PDec E v n frames sc t x fl)
    (h2 : per E v n sc t x' fl') (d2 : PDec E v n frames sc t x' fl')
    (he : complete v .other fl = complete v .other fl') : x = x' ∧ fl = fl' := by
  obtain ⟨pad1, e1, _⟩ := complete_other v fl
  obtain ⟨pad2, e2, _⟩ := complete_other v fl'
  have r1 := pdec_complete E v n frames sc t x fl h1 d1 0 pad1
  have r2 := pdec_complete E v n frames sc t x' fl' h2 d2 0 pad2
  rw [← e1, he, e2] at r1
  rw [r1] at r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at r2
  exact r2.1

end Asn1.X691

