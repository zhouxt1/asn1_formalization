import Asn1.X680.Checker
import Asn1.X680.Monotone

/-!
# The checker's value decisions agree with the spec's value sets

`valOkB`, `serialValsOkB` and `constraintKindsOkB` decide where a value is in or out of a type,
or where a constraint selects nothing. These lemmas connect them to `sem`, `cons` and `eset`:
more fuel resolves the same, a decision on an element set (`Dec`) is the spec's answer, and the
walks through tags, constraints and references follow `sem`.
-/

namespace Asn1.X680

/-! ## More fuel resolves the same -/

section Mono

variable {E : Env}

theorem resolveValTy_mono {n n' sc mn name args r} (h : resolveValTy E n sc mn name args = some r)
    (hn : n ≤ n') : resolveValTy E n' sc mn name args = some r := resolveIn_mono h hn

theorem classFields_mono : ∀ {n n' : Nat} {sc : Scope} {c : ClassRef} {r},
    classFields E n sc c = some r → n ≤ n' → classFields E n' sc c = some r
  | 0, _, _, _, _, h, _ => by simp [classFields] at h
  | n + 1, n' + 1, sc, c, r, h, hn => by
    cases c with
    | ref mn name args =>
      simp only [classFields] at h ⊢
      cases hr : resolveClass E n sc mn name args with
      | none => simp [hr] at h
      | some x =>
        rw [hr] at h; rw [resolveClass_mono hr (by omega)]
        exact classFields_mono h (by omega)
    | _ => simpa [classFields] using h
  | _ + 1, 0, _, _, _, _, hn => by omega

theorem fieldAt_mono : ∀ {n n' : Nat} {cf : Scope × List FieldSpec} {p : List String} {r},
    fieldAt E n cf p = some r → n ≤ n' → fieldAt E n' cf p = some r
  | 0, _, _, _, _, h, _ => by simp [fieldAt] at h
  | _ + 1, 0, _, _, _, _, hn => by omega
  | n + 1, n' + 1, (sc, fs), [], r, h, hn => by simp [fieldAt] at h
  | n + 1, n' + 1, (sc, fs), [f], r, h, hn => by simpa [fieldAt] using h
  | n + 1, n' + 1, (sc, fs), f :: g :: rest, r, h, hn => by
    simp only [fieldAt] at h ⊢
    split at h
    · rename_i nm c o hf
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨cf, h1, h2⟩ := h
      exact ⟨cf, classFields_mono h1 (by omega), fieldAt_mono h2 (by omega)⟩
    · rename_i nm c o hf
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨cf, h1, h2⟩ := h
      exact ⟨cf, classFields_mono h1 (by omega), fieldAt_mono h2 (by omega)⟩
    · simp at h

theorem objSetClass_mono {n n' : Nat} {sc : Scope} {os : ObjSet} {r}
    (h : objSetClass E n sc os = some r) (hn : n ≤ n') : objSetClass E n' sc os = some r := by
  unfold objSetClass at h ⊢
  split at h
  · rename_i mn name args
    split at h
    · rename_i x c y hr; rw [resolveObjSet_mono hr hn]; exact h
    · simp at h
  · rename_i mn name args
    split at h
    · rename_i x c y hr; rw [resolveObj_mono hr hn]; exact h
    · simp at h
  · simp at h

theorem bind_fields_mono {n n' : Nat} {sc : Scope} {cls : ClassRef} {path : List String} {r}
    (h : (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) = some r) (hn : n ≤ n') :
    (classFields E n' sc cls).bind (fun cf => fieldAt E n' cf path) = some r := by
  simp only [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨cf, h1, h2⟩ := h
  exact ⟨cf, classFields_mono h1 hn, fieldAt_mono h2 hn⟩

theorem builtin_mono : ∀ {n n' : Nat} {sc : Scope} {t : Ty} {r},
    builtin E n sc t = some r → n ≤ n' → builtin E n' sc t = some r
  | 0, _, _, _, _, h, _ => by simp [builtin] at h
  | _ + 1, 0, _, _, _, _, hn => by omega
  | n + 1, n' + 1, sc, t, r, h, hn => by
    cases t with
    | ref name =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtin_mono h2 (by omega)⟩
    | extRef mn name =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtin_mono h2 (by omega)⟩
    | paramRef mn name args =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtin_mono h2 (by omega)⟩
    | tagged tg k t => simp only [builtin] at h ⊢; exact builtin_mono h (by omega)
    | constrained t c => simp only [builtin] at h ⊢; exact builtin_mono h (by omega)
    | instanceOf cls => simp only [builtin] at h ⊢; exact builtin_mono h (by omega)
    | selection nm t =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i sc' root ext hb
        rw [builtin_mono hb (by omega)]; simp only
        split at h
        · rename_i a ha; exact builtin_mono h (by omega)
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i sc' nm t' u o hb; rw [bind_fields_mono hb (by omega)]; exact builtin_mono h (by omega)
      · rename_i sc' nm t' u hb; rw [bind_fields_mono hb (by omega)]; exact builtin_mono h (by omega)
      · rename_i x nm o hb; rw [bind_fields_mono hb (by omega)]; exact h
      · rename_i x nm o u hb; rw [bind_fields_mono hb (by omega)]; exact h
      · rename_i x nm o u hb; rw [bind_fields_mono hb (by omega)]; exact h
      · simp at h
    | fromObjects src path =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i csc cls hc
        rw [objSetClass_mono hc (by omega)]; simp only
        split at h
        · rename_i sc' nm t' u o hb; rw [bind_fields_mono hb (by omega)]; exact builtin_mono h (by omega)
        · rename_i sc' nm t' u hb; rw [bind_fields_mono hb (by omega)]; exact builtin_mono h (by omega)
        · simp at h
      · simp at h
    | _ => simpa [builtin] using h


theorem builtinV_mono : ∀ {n n' : Nat} {sc : Scope} {t : Ty} {r},
    builtinV E n sc t = some r → n ≤ n' → builtinV E n' sc t = some r
  | 0, _, _, _, _, h, _ => by simp [builtinV] at h
  | _ + 1, 0, _, _, _, _, hn => by omega
  | n + 1, n' + 1, sc, t, r, h, hn => by
    cases t with
    | ref name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtinV_mono h2 (by omega)⟩
    | extRef mn name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtinV_mono h2 (by omega)⟩
    | paramRef mn name args =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h
      exact ⟨x, resolveTy_mono h1 (by omega), builtinV_mono h2 (by omega)⟩
    | tagged tg k t => simp only [builtinV] at h ⊢; exact builtinV_mono h (by omega)
    | constrained t c => simp only [builtinV] at h ⊢; exact builtinV_mono h (by omega)
    | instanceOf cls => simp only [builtinV] at h ⊢; exact builtinV_mono h (by omega)
    | selection nm t =>
      simp only [builtinV] at h ⊢
      split at h
      · rename_i sc' root ext hb
        rw [builtin_mono hb (by omega)]; simp only
        split at h
        · exact builtinV_mono h (by omega)
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtinV] at h ⊢
      split at h
      · rename_i sc' nm t' u o hb; rw [bind_fields_mono hb (by omega)]; exact builtinV_mono h (by omega)
      · rename_i sc' nm t' u hb; rw [bind_fields_mono hb (by omega)]; exact builtinV_mono h (by omega)
      · simp at h
    | fromObjects src path => simp [builtinV] at h
    | _ => simpa [builtinV] using h

/-- What `builtinV` finds, `builtin` finds. -/
theorem builtin_of_builtinV : ∀ {n : Nat} {sc : Scope} {t : Ty} {r},
    builtinV E n sc t = some r → builtin E n sc t = some r
  | 0, _, _, _, h => by simp [builtinV] at h
  | n + 1, sc, t, r, h => by
    cases t with
    | ref name =>
      simp only [builtinV, builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h; exact ⟨x, h1, builtin_of_builtinV h2⟩
    | extRef mn name =>
      simp only [builtinV, builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h; exact ⟨x, h1, builtin_of_builtinV h2⟩
    | paramRef mn name args =>
      simp only [builtinV, builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, h1, h2⟩ := h; exact ⟨x, h1, builtin_of_builtinV h2⟩
    | tagged tg k t => simp only [builtinV, builtin] at h ⊢; exact builtin_of_builtinV h
    | constrained t c => simp only [builtinV, builtin] at h ⊢; exact builtin_of_builtinV h
    | instanceOf cls => simp only [builtinV, builtin] at h ⊢; exact builtin_of_builtinV h
    | selection nm t =>
      simp only [builtinV, builtin] at h ⊢
      split at h
      · rename_i sc' root ext hb
        rw [hb]; simp only
        split at h
        · rename_i a ha; rw [ha]; exact builtin_of_builtinV h
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtinV, builtin] at h ⊢
      split at h
      · rename_i sc' nm t' u o hb; rw [hb]; exact builtin_of_builtinV h
      · rename_i sc' nm t' u hb; rw [hb]; exact builtin_of_builtinV h
      · simp at h
    | fromObjects src path => simp [builtinV] at h
    | _ => simpa [builtinV, builtin] using h

/-- With `expandKnown`, more fuel lists the same components. -/
theorem expand_stable : ∀ {n n' : Nat} {sc : Scope} {l : List Comp},
    expandKnown E n sc l = true → n ≤ n' → expand E n' sc l = expand E n sc l
  | 0, _, _, _, h, _ => by simp [expandKnown] at h
  | _ + 1, 0, _, _, _, hn => by omega
  | n + 1, n' + 1, sc, [], _, _ => by simp [expand]
  | n + 1, n' + 1, sc, .mk nm t p :: rest, h, hn => by
    simp only [expandKnown] at h
    simp only [expand, expand_stable h (by omega : n ≤ n')]
  | n + 1, n' + 1, sc, .componentsOf t :: rest, h, hn => by
    simp only [expandKnown, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [expand, expand_stable h2 (by omega : n ≤ n')]
    congr 1
    split at h1
    · rename_i sc' r e r2 hb
      rw [builtin_mono hb (by omega), hb]; exact expand_stable h1 (by omega)
    · rename_i sc' r e r2 hb
      rw [builtin_mono hb (by omega), hb]; exact expand_stable h1 (by omega)
    · simp at h1

theorem entries_stable {n n' : Nat} {sc : Scope} {r r2 : List Comp} {e : Option (List ExtAdd)}
    (h : entriesKnown E n sc r e r2 = true) (hn : n ≤ n') : entries E n' sc r e r2 = entries E n sc r e r2 := by
  simp only [entriesKnown, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [entries, expand_stable h1 hn, expand_stable h3 hn]
  congr 2
  apply List.flatMap_congr
  intro ⟨a, i⟩ hm
  have := h2 a (List.fst_mem_of_mem_zipIdx hm)
  simp only [expand_stable this hn]

end Mono

/-! ## Value sets -/

section Sets

variable {E : Env} {H : ContentsHook}

theorem elem_sub_g : ∀ {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {el : Elem}
    {x : Val}, (elem E H M sc outer pt g el).r x ∨ (elem E H M sc outer pt g el).a x → g x
  | 0, _, _, _, _, _, _, h => by simp [elem, ESet.empty] at h
  | M + 1, sc, outer, pt, g, el, x, h => by
    cases el with
    | withComponents isPartial ncs =>
      simp only [elem] at h
      split at h
      · simp only [ESet.byComponents] at h; rcases h with h | h <;> exact h.1
      · simp only [ESet.byComponents] at h; rcases h with h | h <;> exact h.1
      · simp only [ESet.byAlternatives] at h; rcases h with h | h <;> exact h.1
      · exact elem_sub_g h
      · exact elem_sub_g h
      · exact elem_sub_g h
      · simp only [ESet.byReal] at h; rcases h with h | h <;> exact h.1
      · simp only [ESet.byDuration] at h; rcases h with h | h <;> exact h.1
      · simp only [ESet.byDuration] at h; rcases h with h | h <;> exact h.1
      · simp [ESet.empty] at h
    | withComponent c =>
      simp only [elem] at h
      split at h
      · simp only [ESet.byElems] at h; rcases h with h | h <;> exact h.1
      · simp only [ESet.byElems] at h; rcases h with h | h <;> exact h.1
      · simp [ESet.empty] at h
    | size c => simp only [elem, ESet.bySize] at h; rcases h with h | h <;> exact h.1
    | from_ c => simp only [elem, ESet.byAlphabet] at h; rcases h with h | h <;> exact h.1
    | _ => simp only [elem, ESet.fixed] at h; rcases h with h | h <;> exact h.1

theorem eset_sub_g : ∀ {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {es : ElemSet}
    {x : Val}, (eset E H M sc outer pt g es).r x ∨ (eset E H M sc outer pt g es).a x → g x
  | 0, _, _, _, _, _, _, h => by simp [eset, ESet.empty] at h
  | M + 1, sc, outer, pt, g, es, x, h => by
    cases es with
    | elem el => exact elem_sub_g h
    | union a b =>
      simp only [eset, ESet.union] at h
      rcases h with (h | h) | (h | h | h | h) <;> first | exact eset_sub_g (.inl h) | exact eset_sub_g (.inr h)
    | inter a b =>
      simp only [eset, ESet.inter] at h
      rcases h with h | (h | h) <;> first | exact eset_sub_g (.inl h.1) | exact eset_sub_g (.inr h.1)
    | except a b =>
      simp only [eset, ESet.except] at h
      rcases h with h | (h | h) <;> first | exact eset_sub_g (.inl h.1) | exact eset_sub_g (.inr h.1)
    | allExcept b => simp only [eset, ESet.allExcept] at h; rcases h with h | h <;> exact h.1

/-- A constraint's values are among its parent's root values. -/
theorem cons_sub_parent {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {parent : VSet}
    {c : Constraint} {x : Val}
    (h : (cons E H M sc outer pt parent c).root x ∨ (cons E H M sc outer pt parent c).all x) : parent.root x := by
  cases M with
  | zero => simp [cons, VSet.empty] at h
  | succ M =>
    cases c with
    | mk root ext adds =>
      simp only [cons, VSet.keepExt, VSet.ofSpecs] at h
      rcases h with h | (h | ⟨e, he, h⟩)
      · exact eset_sub_g (.inl h)
      · exact eset_sub_g (.inr h)
      · cases adds with
        | none => simp at he
        | some a => simp at he; subst he; exact eset_sub_g (.inr h)
    | table os refs =>
      simp only [cons] at h
      split at h
      · split at h
        · simp only [VSet.keepExt, VSet.plain] at h; rcases h with h | h <;> exact h.1
        · simp [VSet.empty] at h
      · split at h
        · simp only [VSet.keepExt, VSet.plain] at h; rcases h with h | h <;> exact h.1
        · simp [VSet.empty] at h
    | contents t enc => simp only [cons, VSet.keepExt, VSet.plain] at h; rcases h with h | h <;> exact h.1
    | userDefined =>
      simp only [cons, VSet.keepExt, VSet.ofSpecs, ESet.userDefined, ESet.fixed] at h
      rcases h with h | (h | ⟨e, he, h⟩)
      · exact h
      · exact h
      · simp at he


theorem valueOk_root_all {inner : Scope → Ty → Constraint → VSet}
    (hi : ∀ sc t c y, (inner sc t c).root y → (inner sc t c).all y) {sc : Scope} {t : Ty}
    {o : Option (Option Constraint × PresenceC)} {v : Option Val}
    (h : ValueOk inner true sc t o v) : ValueOk inner false sc t o v := by
  unfold ValueOk at h ⊢
  split
  · rename_i c p x
    simp only at h ⊢
    exact hi _ _ _ _ h
  · trivial

theorem byComponents_r_a {g : Val → Prop} {es : List Entry} {isPartial : Bool}
    {ncs : List (String × Option Constraint × PresenceC)} {inner : Scope → Ty → Constraint → VSet}
    {dflt : Entry → Val → Prop} (hi : ∀ sc t c y, (inner sc t c).root y → (inner sc t c).all y) {x : Val}
    (h : (ESet.byComponents g es isPartial ncs inner dflt).r x) :
    (ESet.byComponents g es isPartial ncs inner dflt).a x := by
  simp only [ESet.byComponents] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨hg, h⟩ := h
  cases x with
  | seq cs =>
    simp only at h ⊢
    intro en hen
    obtain ⟨h1, h2, h3⟩ := h en hen
    exact ⟨h1, valueOk_root_all hi h2, fun hl w hw => valueOk_root_all hi (h3 hl w hw)⟩
  | _ => simp at h

theorem byAlternatives_r_a {g : Val → Prop} {asc : Scope} {alts : List Alt} {isPartial : Bool}
    {ncs : List (String × Option Constraint × PresenceC)} {inner : Scope → Ty → Constraint → VSet}
    (hi : ∀ sc t c y, (inner sc t c).root y → (inner sc t c).all y) {x : Val}
    (h : (ESet.byAlternatives g asc alts isPartial ncs inner).r x) :
    (ESet.byAlternatives g asc alts isPartial ncs inner).a x := by
  simp only [ESet.byAlternatives] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨hg, h⟩ := h
  cases x with
  | choice a y =>
    simp only at h ⊢
    intro al hal
    obtain ⟨h1, h2⟩ := h al hal
    exact ⟨h1, valueOk_root_all hi h2⟩
  | _ => simp at h

mutual
theorem elem_r_a : ∀ {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {el : Elem}
    {x : Val}, (elem E H M sc outer pt g el).r x → (elem E H M sc outer pt g el).a x
  | 0, _, _, _, _, _, _, h => by simp [elem, ESet.empty] at h
  | M + 1, sc, outer, pt, g, el, x, h => by
    have hi : ∀ sc t c y, (cons E H M sc [] t (sem E H M sc [] t) c).root y →
        (cons E H M sc [] t (sem E H M sc [] t) c).all y := fun _ _ _ _ h => cons_root_all h
    cases el with
    | withComponents isPartial ncs =>
      simp only [elem] at h ⊢
      split at h
      · exact byComponents_r_a hi h
      · exact byComponents_r_a hi h
      · exact byAlternatives_r_a hi h
      · exact elem_r_a h
      · exact elem_r_a h
      · exact elem_r_a h
      · simp only [ESet.byReal] at h ⊢
        obtain ⟨hg, r, hr, y, hd, hy⟩ := h
        exact ⟨hg, r, hr, y, hd, elem_r_a hy⟩
      · simp only [ESet.byDuration] at h ⊢
        obtain ⟨hg, d, hd, hy⟩ := h
        exact ⟨hg, d, hd, byComponents_r_a hi hy⟩
      · simp only [ESet.byDuration] at h ⊢
        obtain ⟨hg, d, hd, hy⟩ := h
        exact ⟨hg, d, hd, byComponents_r_a hi hy⟩
      · simp [ESet.empty] at h
    | withComponent c =>
      simp only [elem] at h ⊢
      split at h
      · simp only [ESet.byElems] at h ⊢
        exact ⟨h.1, fun y hy => cons_root_all (h.2 y hy)⟩
      · simp only [ESet.byElems] at h ⊢
        exact ⟨h.1, fun y hy => cons_root_all (h.2 y hy)⟩
      · simp [ESet.empty] at h
    | size c =>
      simp only [elem, ESet.bySize] at h ⊢
      obtain ⟨hg, k, hk, hr⟩ := h
      exact ⟨hg, k, hk, cons_root_all hr⟩
    | from_ c =>
      simp only [elem, ESet.byAlphabet] at h ⊢
      obtain ⟨hg, h1, h2⟩ := h
      refine ⟨hg, fun ch hch => ?_, fun ch hch => ?_⟩
      · obtain ⟨s, hs, hc⟩ := h1 ch hch; exact ⟨s, cons_root_all hs, hc⟩
      · obtain ⟨s, hs, hc⟩ := h2 ch hch; exact ⟨s, cons_root_all hs, hc⟩
    | _ => simpa [elem, ESet.fixed] using h

theorem eset_r_a : ∀ {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {es : ElemSet}
    {x : Val}, (eset E H M sc outer pt g es).r x → (eset E H M sc outer pt g es).a x
  | 0, _, _, _, _, _, _, h => by simp [eset, ESet.empty] at h
  | M + 1, sc, outer, pt, g, es, x, h => by
    cases es with
    | elem el => exact elem_r_a h
    | union a b =>
      simp only [eset, ESet.union] at h ⊢
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h)
    | inter a b => simp only [eset, ESet.inter] at h ⊢; exact .inl h
    | except a b => simp only [eset, ESet.except] at h ⊢; exact .inl h
    | allExcept b => simpa [eset, ESet.allExcept] using h

theorem cons_root_all : ∀ {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {parent : VSet}
    {c : Constraint} {x : Val}, (cons E H M sc outer pt parent c).root x → (cons E H M sc outer pt parent c).all x
  | 0, _, _, _, _, _, _, h => by simp [cons, VSet.empty] at h
  | M + 1, sc, outer, pt, parent, c, x, h => by
    cases c with
    | mk root ext adds =>
      simp only [cons, VSet.keepExt, VSet.ofSpecs] at h ⊢
      exact .inl (eset_r_a h)
    | table os refs =>
      simp only [cons] at h ⊢
      split at h
      · split at h
        · simpa [VSet.keepExt, VSet.plain] using h
        · simp [VSet.empty] at h
      · split at h
        · simpa [VSet.keepExt, VSet.plain] using h
        · simp [VSet.empty] at h
    | contents t enc => simpa [cons, VSet.keepExt, VSet.plain] using h
    | userDefined =>
      simp only [cons, VSet.keepExt, VSet.ofSpecs, ESet.userDefined, ESet.fixed] at h ⊢
      exact .inl h
end

end Sets


/-! ## Decisions -/

/-- `o` decides `P`: when it says, it is right. -/
def Decides (o : Option Bool) (P : Prop) : Prop := ∀ b, o = some b → (P ↔ b = true)

theorem Decides.none' {P : Prop} : Decides none P := by intro b h; simp at h

theorem Decides.congr {o : Option Bool} {P Q : Prop} (h : Decides o P) (hpq : P ↔ Q) : Decides o Q :=
  fun b hb => hpq.symm.trans (h b hb)

theorem Decides.orB {x y : Option Bool} {P Q : Prop} (hx : Decides x P) (hy : Decides y Q) :
    Decides (orB x y) (P ∨ Q) := by
  intro b hb
  rcases x with _ | ⟨_ | _⟩ <;> rcases y with _ | ⟨_ | _⟩ <;> simp only [Asn1.X680.orB, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    simp_all [Decides]

theorem Decides.andB {x y : Option Bool} {P Q : Prop} (hx : Decides x P) (hy : Decides y Q) :
    Decides (andB x y) (P ∧ Q) := by
  intro b hb
  rcases x with _ | ⟨_ | _⟩ <;> rcases y with _ | ⟨_ | _⟩ <;> simp only [Asn1.X680.andB, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    simp_all [Decides]

theorem Decides.not {x : Option Bool} {P : Prop} (hx : Decides x P) : Decides (x.map (!·)) (¬ P) := by
  intro b hb
  rcases x with _ | ⟨_ | _⟩ <;> simp at hb <;> subst hb <;> simp_all [Decides]

theorem Decides.some_false {o : Option Bool} {P : Prop} (h : Decides o P) (ho : o = some false) : ¬ P :=
  fun hp => by simpa using (h false ho).mp hp

theorem Decides.some_true {o : Option Bool} {P : Prop} (h : Decides o P) (ho : o = some true) : P :=
  (h true ho).mpr rfl

/-- A decision on an element set: on its root, and on its values with additions. -/
def DecidesES (d : Dec) (S : ESet) (x : Val) : Prop := Decides d.1 (S.r x) ∧ Decides d.2 (S.a x)

/-- A decision on a constrained type's values: its root, and all its values. -/
def DecidesV (d : Dec) (S : VSet) (x : Val) : Prop := Decides d.1 (S.root x) ∧ Decides d.2 (S.all x)

theorem DecidesES.fixed {o : Option Bool} {s : Val → Prop} {x : Val} (h : Decides o (s x)) :
    DecidesES (o, o) (ESet.fixed s) x := ⟨h, h⟩

theorem DecidesES.union {d1 d2 : Dec} {A B : ESet} {x : Val} (h1 : DecidesES d1 A x) (h2 : DecidesES d2 B x) :
    DecidesES (d1.union d2) (A.union B) x :=
  ⟨h1.1.orB h2.1, ((h1.1.orB h2.1).orB (h1.2.orB h2.2)).congr (by simp only [ESet.union]; tauto)⟩

theorem DecidesES.inter {d1 d2 : Dec} {A B : ESet} {x : Val} (h1 : DecidesES d1 A x) (h2 : DecidesES d2 B x) :
    DecidesES (d1.inter d2) (A.inter B) x :=
  ⟨h1.1.andB h2.1, ((h1.1.andB h2.1).orB (h1.2.andB h2.2)).congr (by simp only [ESet.inter])⟩

theorem DecidesES.except {d1 d2 : Dec} {A B : ESet} {x : Val} (h1 : DecidesES d1 A x) (h2 : DecidesES d2 B x) :
    DecidesES (d1.except d2) (A.except B) x :=
  ⟨h1.1.andB h2.1.not, ((h1.1.andB h2.1.not).orB (h1.2.andB h2.2.not)).congr (by simp only [ESet.except])⟩

theorem DecidesES.allExcept {d : Dec} {B : ESet} {g : Val → Prop} {x : Val} (hg : g x) (h : DecidesES d B x) :
    DecidesES d.allExcept (ESet.allExcept g B) x :=
  ⟨h.1.not.congr (by simp [ESet.allExcept, hg]), h.1.not.congr (by simp [ESet.allExcept, hg])⟩

variable {E : Env} {H : ContentsHook}

/-- `decES` decides an element set when its element decisions decide the elements, at every fuel
from `M0` and their size on. -/
theorem decES_decides {el : Elem → Dec} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {x : Val} {M0 : Nat} (hg : g x)
    (hel : ∀ e M, M0 + sizeOf e ≤ M → DecidesES (el e) (elem E H M sc outer pt g e) x) :
    ∀ (es : ElemSet) (M : Nat), M0 + sizeOf es ≤ M → DecidesES (decES el es) (eset E H M sc outer pt g es) x
  | .elem e, M + 1, hM => by
    simp only [decES, eset]; exact hel e M (by simp at hM; omega)
  | .union a b, M + 1, hM => by
    simp only [decES, eset]
    exact (decES_decides hg hel a M (by simp at hM; omega)).union (decES_decides hg hel b M (by simp at hM; omega))
  | .inter a b, M + 1, hM => by
    simp only [decES, eset]
    exact (decES_decides hg hel a M (by simp at hM; omega)).inter (decES_decides hg hel b M (by simp at hM; omega))
  | .except a b, M + 1, hM => by
    simp only [decES, eset]
    exact (decES_decides hg hel a M (by simp at hM; omega)).except (decES_decides hg hel b M (by simp at hM; omega))
  | .allExcept b, M + 1, hM => by
    simp only [decES, eset]
    exact (decES_decides hg hel b M (by simp at hM; omega)).allExcept hg
  | es, 0, hM => by cases es <;> simp at hM

/-- `decCons` decides a constraint when its element set decisions decide them. -/
theorem decCons_decides {es : ElemSet → Dec} {sc : Scope} {outer : List Frame} {pt : Ty} {parent : VSet}
    {x : Val} {M : Nat} {r : ElemSet} {ext : Bool} {a : Option ElemSet}
    (hr : DecidesES (es r) (eset E H M sc outer pt parent.root r) x)
    (ha : ∀ a', a = some a' → DecidesES (es a') (eset E H M sc outer pt parent.root a') x) :
    DecidesV (decCons es (.mk r ext a)) (cons E H (M + 1) sc outer pt parent (.mk r ext a)) x := by
  simp only [decCons, Dec.ofSpecs, cons, DecidesV, VSet.keepExt, VSet.ofSpecs]
  refine ⟨hr.1, ?_⟩
  cases a with
  | none => simpa using hr.2
  | some a' => simpa using hr.2.orB (ha a' rfl).2


/-! ## Equality and evaluation -/

/-- Built-in types whose values are one abstract value only when equal. -/
def EqBase : Ty → Prop
  | .integer _ | .restricted _ => True
  | _ => False

theorem eqv_eq_of_builtin : ∀ {n : Nat} {sc : Scope} {t : Ty} {sc' : Scope} {b : Ty},
    builtin E n sc t = some (sc', b) → EqBase b → ∀ N, n + 1 ≤ N → ∀ x y, eqv E N sc t x y ↔ x = y
  | 0, _, _, _, _, h, _, _, _, _, _ => by simp [builtin] at h
  | _, _, _, _, _, _, _, 0, hN, _, _ => by omega
  | n + 1, sc, t, sc', b, h, hb, N + 1, hN, x, y => by
    cases t with
    | ref name =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      simp only [eqv, resolveTy_mono h1 (by omega : n ≤ N)]
      exact eqv_eq_of_builtin h2 hb N (by omega) x y
    | extRef mn name =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      simp only [eqv, resolveTy_mono h1 (by omega : n ≤ N)]
      exact eqv_eq_of_builtin h2 hb N (by omega) x y
    | paramRef mn name args =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      simp only [eqv, resolveTy_mono h1 (by omega : n ≤ N)]
      exact eqv_eq_of_builtin h2 hb N (by omega) x y
    | tagged tg k u => simp only [builtin] at h; simp only [eqv]; exact eqv_eq_of_builtin h hb N (by omega) x y
    | constrained u c => simp only [builtin] at h; simp only [eqv]; exact eqv_eq_of_builtin h hb N (by omega) x y
    | selection nm u =>
      simp only [builtin] at h
      split at h
      · rename_i s root ext hu
        split at h
        · rename_i a ha
          simp only [eqv, builtin_mono hu (by omega : n ≤ N), ha]
          exact eqv_eq_of_builtin h hb N (by omega) x y
        · simp at h
      · simp at h
    | classField cls path =>
      have hc := builtin_mono h (by omega : n + 1 ≤ N)
      simp only [eqv, hc]
      cases N with
      | zero => omega
      | succ N =>
        cases b <;> simp only [EqBase] at hb <;> simp [eqv]
    | instanceOf cls =>
      simp only [builtin] at h
      cases n with
      | zero => simp [builtin] at h
      | succ n => simp [builtin, instanceOfTy] at h; obtain ⟨-, rfl⟩ := h; simp [EqBase] at hb
    | fromObjects src path => simp [eqv]
    | integer nb => simp [eqv]
    | restricted k => simp [eqv]
    | _ => simp [builtin] at h; obtain ⟨-, rfl⟩ := h; simp [EqBase] at hb

theorem evalVal_of_intOfV {n : Nat} : ∀ {k : Nat} {sc : Scope} {v : Val} {i : Int},
    intOfV E n sc k v = some i → ∀ M, n + k + 1 ≤ M → ∀ w, evalVal E M sc v w ↔ w = .int i
  | k, sc, .int j, i, h, M + 1, hM, w => by simp [intOfV] at h; subst h; simp [evalVal]
  | k + 1, sc, .ref mn nm args, i, h, M + 1, hM, w => by
    simp only [intOfV] at h
    split at h
    · rename_i s v' hr
      simp only [evalVal, resolveVal_mono hr (by omega : n ≤ M)]
      exact evalVal_of_intOfV h M (by omega) w
    · simp at h
  | 0, sc, .ref .., i, h, _, _, _ => by simp [intOfV] at h
  | _, _, .bool _, _, h, _, _, _ | _, _, .enum _, _, h, _, _, _ | _, _, .real _, _, h, _, _, _
  | _, _, .bits _, _, h, _, _, _ | _, _, .octets _, _, h, _, _, _ | _, _, .null, _, h, _, _, _
  | _, _, .seq _, _, h, _, _, _ | _, _, .seqOf _, _, h, _, _, _ | _, _, .setOf _, _, h, _, _, _
  | _, _, .choice .., _, h, _, _, _ | _, _, .oid _, _, h, _, _, _ | _, _, .iri _, _, h, _, _, _
  | _, _, .chars _, _, h, _, _, _ | _, _, .regChars _, _, h, _, _, _ | _, _, .time _, _, h, _, _, _
  | _, _, .open_ .., _, h, _, _, _ | _, _, .fromObject .., _, h, _, _, _ | _, _, .raw _, _, h, _, _, _ => by
    simp [intOfV] at h
  | _, _, .int _, _, _, 0, hM, _ => by omega

theorem evalVal_of_charsOfV {n : Nat} : ∀ {k : Nat} {sc : Scope} {v : Val} {cs : List Nat},
    charsOfV E n sc k v = some cs → ∀ M, n + k + 1 ≤ M → ∀ w, evalVal E M sc v w ↔ w = .chars cs
  | k, sc, .chars j, i, h, M + 1, hM, w => by simp [charsOfV] at h; subst h; simp [evalVal]
  | k + 1, sc, .ref mn nm args, i, h, M + 1, hM, w => by
    simp only [charsOfV] at h
    split at h
    · rename_i s v' hr
      simp only [evalVal, resolveVal_mono hr (by omega : n ≤ M)]
      exact evalVal_of_charsOfV h M (by omega) w
    · simp at h
  | 0, sc, .ref .., i, h, _, _, _ => by simp [charsOfV] at h
  | _, _, .bool _, _, h, _, _, _ | _, _, .enum _, _, h, _, _, _ | _, _, .real _, _, h, _, _, _
  | _, _, .bits _, _, h, _, _, _ | _, _, .octets _, _, h, _, _, _ | _, _, .null, _, h, _, _, _
  | _, _, .seq _, _, h, _, _, _ | _, _, .seqOf _, _, h, _, _, _ | _, _, .setOf _, _, h, _, _, _
  | _, _, .choice .., _, h, _, _, _ | _, _, .oid _, _, h, _, _, _ | _, _, .iri _, _, h, _, _, _
  | _, _, .int _, _, h, _, _, _ | _, _, .regChars _, _, h, _, _, _ | _, _, .time _, _, h, _, _, _
  | _, _, .open_ .., _, h, _, _, _ | _, _, .fromObject .., _, h, _, _, _ | _, _, .raw _, _, h, _, _, _ => by
    simp [charsOfV] at h
  | _, _, .chars _, _, _, 0, hM, _ => by omega


/-! ## INTEGER element sets -/

theorem intLo_decides {n : Nat} {sc : Scope} {i : Int} {lo : Bound} {loOpen : Bool} {M : Nat}
    (hM : n + 10 ≤ M) :
    Decides (match lo with
      | .min => some true
      | .max => none
      | .val v => (intOfV E n sc 8 v).map fun l => if loOpen then decide (l < i) else decide (l ≤ i))
      (∃ l, EvalBound E M sc lo l ∧ match l with
        | .min => True
        | .max => False
        | .val v => if loOpen then v.lt (.int i) else v.le (.int i)) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  cases lo with
  | min => intro b hb; simp at hb; subst hb; simp [EvalBound]
  | max => exact Decides.none'
  | val v =>
    intro b hb
    cases hv : intOfV E n sc 8 v with
    | none => simp [hv] at hb
    | some l =>
      simp only [hv, Option.map_some, Option.some.injEq] at hb; subst hb
      have he := evalVal_of_intOfV hv M (by omega)
      simp only [EvalBound]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
        rw [(he w).mp hw] at h
        cases loOpen <;> simp_all [Val.lt, Val.le]
      · intro h
        refine ⟨_, ⟨.int l, (he _).mpr rfl, rfl⟩, ?_⟩
        cases loOpen <;> simp_all [Val.lt, Val.le]; omega

theorem intHi_decides {n : Nat} {sc : Scope} {i : Int} {hi : Bound} {hiOpen : Bool} {M : Nat}
    (hM : n + 10 ≤ M) :
    Decides (match hi with
      | .max => some true
      | .min => none
      | .val v => (intOfV E n sc 8 v).map fun h => if hiOpen then decide (i < h) else decide (i ≤ h))
      (∃ h, EvalBound E M sc hi h ∧ match h with
        | .max => True
        | .min => False
        | .val v => if hiOpen then (Val.int i).lt v else (Val.int i).le v) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  cases hi with
  | max => intro b hb; simp at hb; subst hb; simp [EvalBound]
  | min => exact Decides.none'
  | val v =>
    intro b hb
    cases hv : intOfV E n sc 8 v with
    | none => simp [hv] at hb
    | some l =>
      simp only [hv, Option.map_some, Option.some.injEq] at hb; subst hb
      have he := evalVal_of_intOfV hv M (by omega)
      simp only [EvalBound]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
        rw [(he w).mp hw] at h
        cases hiOpen <;> simp_all [Val.lt, Val.le]
      · intro h
        refine ⟨_, ⟨.int l, (he _).mpr rfl, rfl⟩, ?_⟩
        cases hiOpen <;> simp_all [Val.lt, Val.le]; omega

theorem intInElem_decides {n : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {i : Int} (hg : g (.int i)) (hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc pt x y ↔ x = y)
    (e : Elem) (M : Nat) (hM : n + 11 ≤ M) :
    DecidesES (let d := intInElem E n sc i e; (d, d)) (elem E H M sc outer pt g e) (.int i) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  cases e with
  | single v =>
    simp only [intInElem, elem]
    apply DecidesES.fixed
    intro b hb
    cases hv : intOfV E n sc 8 v with
    | none => simp [hv] at hb
    | some j =>
      simp only [hv, Option.map_some, Option.some.injEq] at hb; subst hb
      have he := evalVal_of_intOfV hv M (by omega)
      constructor
      · rintro ⟨-, w, hw, hq⟩
        rw [(he w).mp hw, hpt M (by omega)] at hq
        simp at hq; simp [hq]
      · intro h
        simp at h
        exact ⟨hg, .int j, (he _).mpr rfl, (hpt M (by omega) _ _).mpr (by simp [h])⟩
  | range lo loOpen hi hiOpen =>
    simp only [intInElem, elem]
    apply DecidesES.fixed
    refine ((intLo_decides (lo := lo) (loOpen := loOpen) (i := i) (sc := sc) (by omega : n + 10 ≤ M)).andB
      (intHi_decides (hi := hi) (hiOpen := hiOpen) (i := i) (sc := sc) (by omega : n + 10 ≤ M))).congr ?_
    simp only [RangeHas, InRange]
    constructor
    · rintro ⟨⟨l, hl, hl'⟩, ⟨h, hh, hh'⟩⟩
      refine ⟨hg, l, h, hl, hh, ?_, ?_⟩
      · cases l <;> simp_all
      · cases h <;> simp_all
    · rintro ⟨-, l, h, hl, hh, hl', hh'⟩
      refine ⟨⟨l, hl, ?_⟩, ⟨h, hh, ?_⟩⟩
      · cases l <;> simp_all
      · cases h <;> simp_all
  | _ => simp only [intInElem]; exact ⟨Decides.none', Decides.none'⟩

/-- The checker's decision on an INTEGER element set is the spec's, for a value of the governor, on
a parent whose equal values are equal. -/
theorem intInES_decides {n : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {i : Int} (hg : g (.int i)) (hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc pt x y ↔ x = y)
    (es : ElemSet) (M : Nat) (hM : n + 11 + sizeOf es ≤ M) :
    DecidesES (intInES E n sc i es) (eset E H M sc outer pt g es) (.int i) :=
  decES_decides hg (fun e M hM => intInElem_decides hg hpt e M (by omega)) es M hM


theorem eqv_integer {sc : Scope} {nb : List (String × Int)} : ∀ M, 1 ≤ M → ∀ x y, eqv E M sc (.integer nb) x y ↔ x = y
  | M + 1, _, x, y => by simp [eqv]

/-! ## SIZE -/

theorem sizeCons_decides {n : Nat} {sc : Scope} {outer : List Frame} {len : Nat} (c : Constraint) (M : Nat)
    (hM : n + 12 + sizeOf c ≤ M) :
    DecidesV (decCons (intInES E n sc len) c) (cons E H M sc outer (.integer []) sizeParent c) (.int len) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hg : sizeParent.root (.int len) := ⟨len, rfl⟩
  have hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc (.integer []) x y ↔ x = y :=
    fun M hM => eqv_integer M (by omega)
  cases c with
  | mk r ext a =>
    apply decCons_decides
    · exact intInES_decides hg hpt r M (by simp at hM; omega)
    · intro a' ha; subst ha; exact intInES_decides hg hpt a' M (by simp at hM; omega)
  | _ => exact ⟨Decides.none', Decides.none'⟩

theorem bySize_decides {g : Val → Prop} {S : VSet} {x : Val} {len : Nat} {d : Dec} (hg : g x)
    (hx : x.size? = some len) (h : DecidesV d S (.int len)) : DecidesES d (ESet.bySize g S) x :=
  ⟨h.1.congr (by simp [ESet.bySize, hg, hx]), h.2.congr (by simp [ESet.bySize, hg, hx])⟩

theorem sizeInES_decides {n : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {x : Val} {len : Nat} (hg : g x) (hx : x.size? = some len)
    (es : ElemSet) (M : Nat) (hM : n + 13 + sizeOf es ≤ M) :
    DecidesES (sizeInES E n sc len es) (eset E H M sc outer pt g es) x := by
  refine decES_decides (M0 := n + 13) hg (fun e M hM => ?_) es M hM
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  cases e with
  | size c =>
    simp only [elem]
    exact bySize_decides hg hx (sizeCons_decides c M (by simp at hM; omega))
  | _ => exact ⟨Decides.none', Decides.none'⟩


/-! ## Character strings -/

theorem forall₂_mem_left {α β} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | [], [], _, a, ha => by simp at ha
  | x :: xs, y :: ys, .cons hxy hr, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, by simp, hxy⟩
    · obtain ⟨b, hb, h⟩ := forall₂_mem_left hr a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-! ## PATTERN: `patEnds` lists the ends of the matches -/

theorem mapM_some {α β} {f : α → Option β} : ∀ {ps : List α} {qs : List β}, ps.mapM f = some qs →
    List.Forall₂ (fun p q => f p = some q) ps qs
  | [], qs, h => by simp at h; subst h; exact .nil
  | p :: ps, qs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨q, hq, qs', hqs, rfl⟩ := h
    exact .cons hq (mapM_some hqs)

theorem forall₂_mem_right {α β} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], _, b, hb => by simp at hb
  | x :: xs, y :: ys, .cons hxy hr, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, by simp, hxy⟩
    · obtain ⟨a, ha, h⟩ := forall₂_mem_right hr b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem mem_flatten_mapM {α} {f : α → Option (List Nat)} {ps : List α} {qs : List (List Nat)}
    (h : ps.mapM f = some qs) {j : Nat} : j ∈ qs.flatten ↔ ∃ p ∈ ps, ∃ q, f p = some q ∧ j ∈ q := by
  have h2 := mapM_some h
  rw [List.mem_flatten]
  constructor
  · rintro ⟨q, hq, hj⟩
    obtain ⟨p, hp, hpq⟩ := forall₂_mem_right h2 q hq
    exact ⟨p, hp, q, hpq, hj⟩
  · rintro ⟨p, hp, q, hpq, hj⟩
    obtain ⟨q', hq', hpq'⟩ := forall₂_mem_left h2 p hp
    rw [hpq] at hpq'; cases hpq'
    exact ⟨q, hq', hj⟩

theorem Times.zero_iff {a : Regex} {w : List Nat} {i j : Nat} : Times a 0 w i j ↔ i = j := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .zero

theorem Times.succ_iff {a : Regex} {w : List Nat} {k i j : Nat} :
    Times a (k + 1) w i j ↔ ∃ m, Matches a w i m ∧ Times a k w m j := by
  constructor
  · intro h; cases h with | succ h1 h2 => exact ⟨_, h1, h2⟩
  · rintro ⟨m, h1, h2⟩; exact .succ h1 h2

theorem Times.add {a : Regex} {w : List Nat} : ∀ {k l i j : Nat},
    Times a (k + l) w i j ↔ ∃ p, Times a k w i p ∧ Times a l w p j
  | 0, l, i, j => by simp [Times.zero_iff]
  | k + 1, l, i, j => by
    rw [show k + 1 + l = (k + l) + 1 by omega, Times.succ_iff]
    constructor
    · rintro ⟨m, h1, h2⟩
      obtain ⟨p, h3, h4⟩ := (Times.add (k := k) (l := l)).mp h2
      exact ⟨p, Times.succ_iff.mpr ⟨m, h1, h3⟩, h4⟩
    · rintro ⟨p, h1, h2⟩
      obtain ⟨m, h3, h4⟩ := Times.succ_iff.mp h1
      exact ⟨m, h3, (Times.add (k := k) (l := l)).mpr ⟨p, h4, h2⟩⟩

theorem Times.snoc {a : Regex} {w : List Nat} {k i j : Nat} :
    Times a (k + 1) w i j ↔ ∃ p, Times a k w i p ∧ Matches a w p j := by
  rw [Times.add]
  simp only [Times.succ_iff, Times.zero_iff]
  constructor
  · rintro ⟨p, h1, m, h2, rfl⟩; exact ⟨p, h1, h2⟩
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h1, _, h2, rfl⟩

/-- The step of a repetition: the ends of one more match from each position. -/
theorem step_mem {w : List Nat} {a : Regex}
    (ih : ∀ i js, patEnds w a i = some js → ∀ j, j ∈ js ↔ Matches a w i j)
    {ps qs : List Nat} (h : ((ps.mapM (patEnds w a)).map (·.flatten.eraseDups)) = some qs) (j : Nat) :
    j ∈ qs ↔ ∃ p ∈ ps, Matches a w p j := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨xs, hxs, rfl⟩ := h
  rw [List.mem_eraseDups, mem_flatten_mapM hxs]
  constructor
  · rintro ⟨p, hp, q, hq, hj⟩; exact ⟨p, hp, (ih p q hq j).mp hj⟩
  · rintro ⟨p, hp, hm⟩
    obtain ⟨q, hq⟩ : ∃ q, patEnds w a p = some q := by
      obtain ⟨q, _, hq⟩ := forall₂_mem_left (mapM_some hxs) p hp; exact ⟨q, hq⟩
    exact ⟨p, hp, q, hq, (ih p q hq j).mpr hm⟩

theorem iterOpt_mem {w : List Nat} {a : Regex} {step : List Nat → Option (List Nat)}
    (hs : ∀ ps qs, step ps = some qs → ∀ j, j ∈ qs ↔ ∃ p ∈ ps, Matches a w p j) :
    ∀ (k : Nat) (ps f : List Nat), iterOpt step k ps = some f → ∀ j, j ∈ f ↔ ∃ p ∈ ps, Times a k w p j
  | 0, ps, f, h, j => by
    simp only [iterOpt, Option.some.injEq] at h; subst h
    simp [Times.zero_iff]
  | k + 1, ps, f, h, j => by
    simp only [iterOpt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ps', hps', hf⟩ := h
    rw [iterOpt_mem hs k ps' f hf j]
    simp only [hs ps ps' hps', Times.succ_iff]
    constructor
    · rintro ⟨p', ⟨p, hp, hm⟩, ht⟩; exact ⟨p, hp, p', hm, ht⟩
    · rintro ⟨p, hp, p', hm, ht⟩; exact ⟨p', ⟨p, hp, hm⟩, ht⟩

theorem upToOpt_mem {w : List Nat} {a : Regex} {step : List Nat → Option (List Nat)} {i : Nat}
    (hs : ∀ ps qs, step ps = some qs → ∀ j, j ∈ qs ↔ ∃ p ∈ ps, Matches a w p j) :
    ∀ (k c : Nat) (f acc res : List Nat), (∀ x, x ∈ f ↔ Times a c w i x) → upToOpt step k f acc = some res →
      ∀ j, j ∈ res ↔ j ∈ acc ∨ ∃ t, 1 ≤ t ∧ t ≤ k ∧ Times a (c + t) w i j
  | 0, c, f, acc, res, _, h, j => by
    simp only [upToOpt, Option.some.injEq] at h; subst h
    constructor
    · exact .inl
    · rintro (h | ⟨t, h1, h2, -⟩)
      · exact h
      · omega
  | k + 1, c, f, acc, res, hf, h, j => by
    simp only [upToOpt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f', hf', hres⟩ := h
    have hf'' : ∀ x, x ∈ f' ↔ Times a (c + 1) w i x := by
      intro x
      rw [hs f f' hf' x, Times.snoc]
      constructor
      · rintro ⟨p, hp, hm⟩; exact ⟨p, (hf p).mp hp, hm⟩
      · rintro ⟨p, hp, hm⟩; exact ⟨p, (hf p).mpr hp, hm⟩
    rw [upToOpt_mem hs k (c + 1) f' _ res hf'' hres j, List.mem_eraseDups, List.mem_append, hf'' j]
    constructor
    · rintro ((h | h) | ⟨t, h1, h2, h3⟩)
      · exact .inl h
      · exact .inr ⟨1, le_refl _, by omega, h⟩
      · exact .inr ⟨t + 1, by omega, by omega, by rw [show c + (t + 1) = c + 1 + t by omega]; exact h3⟩
    · rintro (h | ⟨t, h1, h2, h3⟩)
      · exact .inl (.inl h)
      · rcases Nat.lt_or_ge t 2 with ht | ht
        · obtain rfl : t = 1 := by omega
          exact .inl (.inr h3)
        · exact .inr ⟨t - 1, by omega, by omega, by rw [show c + 1 + (t - 1) = c + t by omega]; exact h3⟩

/-- What `closureOpt` returns holds what it started with, is closed under one more match, and is
reached from what it started with. -/
theorem closureOpt_mem {w : List Nat} {a : Regex} {step : List Nat → Option (List Nat)}
    (hs : ∀ ps qs, step ps = some qs → ∀ j, j ∈ qs ↔ ∃ p ∈ ps, Matches a w p j) :
    ∀ (k : Nat) (acc res : List Nat), closureOpt step k acc = some res →
      (∀ x ∈ acc, x ∈ res) ∧ (∀ p ∈ res, ∀ j, Matches a w p j → j ∈ res) ∧
      (∀ x ∈ res, ∃ p ∈ acc, ∃ m, Times a m w p x)
  | 0, acc, res, h => by simp [closureOpt] at h
  | k + 1, acc, res, h => by
    simp only [closureOpt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s, hstep, h⟩ := h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h; subst h
      refine ⟨fun x hx => hx, fun p hp j hm => ?_, fun x hx => ⟨x, hx, 0, .zero⟩⟩
      have := (hs _ s hstep j).mpr ⟨p, hp, hm⟩
      simp only [List.all_eq_true, List.contains_iff_mem] at hall
      exact hall j this
    · obtain ⟨h1, h2, h3⟩ := closureOpt_mem hs k _ res h
      refine ⟨fun x hx => h1 x (by simp [List.mem_eraseDups, hx]), h2, fun x hx => ?_⟩
      obtain ⟨p, hp, m, ht⟩ := h3 x hx
      rw [List.mem_eraseDups, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ⟨p, hp, m, ht⟩
      · obtain ⟨q, hq, hqm⟩ := (hs _ s hstep p).mp hp
        exact ⟨q, hq, m + 1, .succ hqm ht⟩

theorem closed_times {w : List Nat} {a : Regex} {res : List Nat}
    (hc : ∀ p ∈ res, ∀ j, Matches a w p j → j ∈ res) : ∀ (m : Nat) (p j : Nat), p ∈ res → Times a m w p j → j ∈ res
  | 0, p, j, hp, ht => by rw [Times.zero_iff] at ht; subst ht; exact hp
  | m + 1, p, j, hp, ht => by
    rw [Times.succ_iff] at ht
    obtain ⟨q, hq, ht⟩ := ht
    exact closed_times hc m q j (hc p hp q hq) ht

theorem patEnds_mem (w : List Nat) : ∀ (re : Regex) (i : Nat) (js : List Nat), patEnds w re i = some js →
    ∀ j, j ∈ js ↔ Matches re w i j
  | .cls neg rs, i, js, h, j => by
    simp only [patEnds, Option.some.injEq] at h; subst h
    constructor
    · intro hj
      split at hj
      · rename_i c hc
        split at hj
        · rename_i hm; simp at hj; subst hj; exact .cls hc hm
        · simp at hj
      · simp at hj
    · intro hm
      cases hm with
      | cls hc hm => rw [hc]; simp [hm]
  | .boundary, i, js, h, j => by
    simp only [patEnds, Option.some.injEq] at h; subst h
    constructor
    · intro hj
      split at hj
      · rename_i hb; simp at hj; subst hj; exact .boundary (of_decide_eq_true hb)
      · simp at hj
    · intro hm
      cases hm with
      | boundary hb => simp only [decide_eq_true hb, ↓reduceIte, List.mem_singleton]
  | .cat a b, i, js, h, j => by
    simp only [patEnds, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ks, hks, xs, hxs, rfl⟩ := h
    rw [List.mem_eraseDups, mem_flatten_mapM hxs]
    constructor
    · rintro ⟨k, hk, q, hq, hj⟩
      exact .cat ((patEnds_mem w a i ks hks k).mp hk) ((patEnds_mem w b k q hq j).mp hj)
    · intro hm
      cases hm with
      | cat h1 h2 =>
        rename_i k
        have hk := (patEnds_mem w a i ks hks k).mpr h1
        obtain ⟨q, _, hq⟩ := forall₂_mem_left (mapM_some hxs) k hk
        exact ⟨k, hk, q, hq, (patEnds_mem w b k q hq j).mpr h2⟩
  | .alt a b, i, js, h, j => by
    simp only [patEnds, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨xs, hxs, ys, hys, rfl⟩ := h
    rw [List.mem_eraseDups, List.mem_append, patEnds_mem w a i xs hxs j, patEnds_mem w b i ys hys j]
    constructor
    · rintro (h | h)
      · exact .altL h
      · exact .altR h
    · intro hm
      cases hm with
      | altL h => exact .inl h
      | altR h => exact .inr h
  | .rep a lo hi, i, js, h, j => by
    have hs : ∀ ps qs, (fun ps : List Nat => (ps.mapM (patEnds w a)).map (·.flatten.eraseDups)) ps = some qs →
        ∀ j, j ∈ qs ↔ ∃ p ∈ ps, Matches a w p j :=
      fun ps qs h j => step_mem (fun i js h => patEnds_mem w a i js h) h j
    simp only [patEnds] at h
    split at h
    · simp at h
    · rename_i hlo
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f, hf, h⟩ := h
      have hf' := iterOpt_mem hs lo [i] f hf
      simp only [List.mem_singleton, exists_eq_left] at hf'
      have hrep : Matches (.rep a lo hi) w i j ↔ ∃ n, lo ≤ n ∧ (∀ m, hi = some m → n ≤ m) ∧ Times a n w i j := by
        constructor
        · intro hm; cases hm with | rep h1 h2 h3 => exact ⟨_, h1, h2, h3⟩
        · rintro ⟨n, h1, h2, h3⟩; exact .rep h1 h2 h3
      rw [hrep]
      cases hi with
      | none =>
        obtain ⟨h1, h2, h3⟩ := closureOpt_mem hs _ f js h
        constructor
        · intro hj
          obtain ⟨p, hp, m, ht⟩ := h3 j hj
          refine ⟨lo + m, by omega, by simp, Times.add.mpr ⟨p, (hf' p).mp hp, ht⟩⟩
        · rintro ⟨n, hn, -, ht⟩
          obtain ⟨p, hp, ht'⟩ := (show Times a (lo + (n - lo)) w i j by rw [show lo + (n - lo) = n by omega]; exact ht)
            |> Times.add.mp
          exact closed_times h2 _ p j (h1 p ((hf' p).mpr hp)) ht'
      | some m =>
        simp only at h
        split at h
        · simp at h
        · have hu := upToOpt_mem (i := i) hs (m - lo) lo f _ js hf' h j
          rw [hu]
          constructor
          · rintro (hj | ⟨t, h1, h2, h3⟩)
            · split at hj
              · exact ⟨lo, le_refl _, fun m' hm' => by simp at hm'; omega, (hf' j).mp hj⟩
              · simp at hj
            · exact ⟨lo + t, by omega, fun m' hm' => by simp at hm'; omega, h3⟩
          · rintro ⟨n, hn, hnm, ht⟩
            have hnm := hnm m rfl
            rcases Nat.eq_or_lt_of_le hn with rfl | hlt
            · left; simp only [hnm, ↓reduceIte]; exact (hf' j).mpr ht
            · right; exact ⟨n - lo, by omega, by omega, by rw [show lo + (n - lo) = n by omega]; exact ht⟩

theorem patAccepts_decides (re : Regex) (cs : List Nat) : Decides (patAccepts re cs) (re.Accepts cs) := by
  intro b hb
  simp only [patAccepts, Option.map_eq_some_iff] at hb
  obtain ⟨js, hjs, rfl⟩ := hb
  rw [Regex.Accepts, ← patEnds_mem cs re 0 js hjs cs.length]
  simp

theorem charList_mem {s : Val} {ch : Nat} (h : ch ∈ s.charList) : ∃ cs, s = .chars cs ∧ ch ∈ cs := by
  cases s <;> simp [Val.charList] at h ⊢; exact h

/-- `alphaNo`: no string of the element set has the character. -/
theorem alphaNo_sound {n : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {ch : Nat}
    (hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc pt x y ↔ x = y) :
    ∀ (es : ElemSet) (M : Nat), n + 12 + sizeOf es ≤ M → alphaNo E n sc ch es = true →
      ∀ s, (eset E H M sc outer pt g es).r s ∨ (eset E H M sc outer pt g es).a s → ch ∉ s.charList
  | .elem (.single v), M + 2, hM, h, s, hs => by
    intro hch
    obtain ⟨cs', rfl, hch⟩ := charList_mem hch
    simp only [alphaNo] at h
    split at h
    · rename_i cs hv
      simp only [eset, elem, ESet.fixed, or_self] at hs
      obtain ⟨-, w, hw, hq⟩ := hs
      rw [(evalVal_of_charsOfV hv M (by simp at hM; omega) w).mp hw, hpt M (by simp at hM; omega)] at hq
      simp only [Val.chars.injEq] at hq; subst hq
      simp at h; exact h hch
    · simp at h
  | .elem (.range lo loOpen hi hiOpen), M + 2, hM, h, s, hs => by
    intro hch
    obtain ⟨cs', rfl, hch⟩ := charList_mem hch
    simp only [eset, elem, ESet.fixed, or_self, RangeHas, InRange] at hs
    obtain ⟨-, l, hb, hl, hh, hlo, hhi⟩ := hs
    simp only [alphaNo] at h
    split at h
    · rename_i lx hx hlx hhx
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by simp at hM; omega⟩
      have key : ∀ (b : Bound) (o : Option Nat) (bv : Bound),
          charBound E n sc b = some o → EvalBound E (M' + 1) sc b bv →
          (b = .min ∧ bv = .min ∧ o = none) ∨ (b = .max ∧ bv = .max) ∨
            ∃ x, o = some x ∧ bv = .val (.chars [x]) := by
        intro b o bv hb hev
        cases b with
        | min => simp [charBound] at hb; simp [EvalBound] at hev; exact .inl ⟨rfl, hev, hb.symm⟩
        | max => simp [charBound] at hb; simp [EvalBound] at hev; exact .inr (.inl ⟨rfl, hev⟩)
        | val v =>
          simp only [charBound] at hb
          split at hb
          · rename_i x hv
            simp at hb; subst hb
            simp only [EvalBound] at hev
            obtain ⟨w, hw, rfl⟩ := hev
            rw [(evalVal_of_charsOfV hv M' (by simp at hM; omega) w).mp hw]
            exact .inr (.inr ⟨x, rfl, rfl⟩)
          · simp at hb
      have lo_ok : lx = none ∨ ∃ x y, lx = some x ∧ cs' = [y] ∧ (if loOpen then x < y else x ≤ y) := by
        rcases key lo lx l hlx hl with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
        · exact .inl rfl
        · simp at hlo
        · right
          rcases cs' with _ | ⟨y, _ | _⟩ <;> cases loOpen <;> simp [Val.lt, Val.le] at hlo
          · exact ⟨x, y, rfl, rfl, by simpa using hlo⟩
          · exact ⟨x, y, rfl, rfl, by simp; omega⟩
      have hi_ok : hx = none ∨ ∃ z y, hx = some z ∧ cs' = [y] ∧ (if hiOpen then y < z else y ≤ z) := by
        rcases key hi hx hb hhx hh with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨z, rfl, rfl⟩
        · simp at hhi
        · simp [charBound] at hhx; exact .inl hhx.symm
        · right
          rcases cs' with _ | ⟨y, _ | _⟩ <;> cases hiOpen <;> simp [Val.lt, Val.le] at hhi
          · exact ⟨z, y, rfl, rfl, by simpa using hhi⟩
          · exact ⟨z, y, rfl, rfl, by simp; omega⟩
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at h
      rcases h with h | h
      · rcases lo_ok with rfl | ⟨x, y, rfl, rfl, hxy⟩
        · simp [Option.all] at h
        · simp [Val.charList] at hch; subst hch
          cases loOpen <;> simp [Option.all] at h hxy <;> omega
      · rcases hi_ok with rfl | ⟨z, y, rfl, rfl, hyz⟩
        · simp [Option.all] at h
        · simp [Val.charList] at hch; subst hch
          cases hiOpen <;> simp [Option.all] at h hyz <;> omega
    · simp at h
  | .elem (.contained ..), M, _, h, _, _ | .elem (.size _), M, _, h, _, _ | .elem (.typeC _), M, _, h, _, _
  | .elem (.from_ _), M, _, h, _, _ | .elem (.withComponent _), M, _, h, _, _
  | .elem (.withComponents ..), M, _, h, _, _ | .elem (.pattern _), M, _, h, _, _
  | .elem (.settings _), M, _, h, _, _ | .allExcept _, M, _, h, _, _ => by simp [alphaNo] at h
  | .union a b, M + 1, hM, h, s, hs => by
    simp only [alphaNo, Bool.and_eq_true] at h
    simp only [eset, ESet.union] at hs
    rcases hs with (hs | hs) | (hs | hs | hs | hs)
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h.1 s (.inl hs)
    · exact alphaNo_sound hpt b M (by simp at hM; omega) h.2 s (.inl hs)
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h.1 s (.inl hs)
    · exact alphaNo_sound hpt b M (by simp at hM; omega) h.2 s (.inl hs)
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h.1 s (.inr hs)
    · exact alphaNo_sound hpt b M (by simp at hM; omega) h.2 s (.inr hs)
  | .inter a b, M + 1, hM, h, s, hs => by
    simp only [alphaNo, Bool.or_eq_true] at h
    simp only [eset, ESet.inter] at hs
    rcases h with h | h
    · rcases hs with hs | hs | hs
      · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inl hs.1)
      · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inl hs.1)
      · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inr hs.1)
    · rcases hs with hs | hs | hs
      · exact alphaNo_sound hpt b M (by simp at hM; omega) h s (.inl hs.2)
      · exact alphaNo_sound hpt b M (by simp at hM; omega) h s (.inl hs.2)
      · exact alphaNo_sound hpt b M (by simp at hM; omega) h s (.inr hs.2)
  | .except a b, M + 1, hM, h, s, hs => by
    simp only [alphaNo] at h
    simp only [eset, ESet.except] at hs
    rcases hs with hs | hs | hs
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inl hs.1)
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inl hs.1)
    · exact alphaNo_sound hpt a M (by simp at hM; omega) h s (.inr hs.1)
  | .elem _, 0, hM, _, _, _ | .elem _, 1, hM, _, _, _ | .union .., 0, hM, _, _, _
  | .inter .., 0, hM, _, _, _ | .except .., 0, hM, _, _, _ => by simp at hM <;> omega


theorem charsInES_decides {n : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {cs : List Nat} (hg : g (.chars cs)) (hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc pt x y ↔ x = y)
    (es : ElemSet) (M : Nat) (hM : n + 14 + sizeOf es ≤ M) :
    DecidesES (charsInES E n sc cs es) (eset E H M sc outer pt g es) (.chars cs) := by
  refine decES_decides (M0 := n + 14) hg (fun e M hM => ?_) es M hM
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  cases e with
  | single v =>
    simp only [elem]
    apply DecidesES.fixed
    intro b hb
    cases hv : charsOfV E n sc 8 v with
    | none => simp [hv] at hb
    | some j =>
      simp only [hv, Option.map_some, Option.some.injEq] at hb; subst hb
      have he := evalVal_of_charsOfV hv M (by omega)
      constructor
      · rintro ⟨-, w, hw, hq⟩
        rw [(he w).mp hw, hpt M (by omega)] at hq
        simp at hq; simp [hq]
      · intro h
        simp at h
        exact ⟨hg, .chars j, (he _).mpr rfl, (hpt M (by omega) _ _).mpr (by simp [h])⟩
  | pattern re =>
    simp only [elem]
    apply DecidesES.fixed
    exact (patAccepts_decides re cs).congr (by simp [hg, Val.patternChars])
  | size c =>
    simp only [elem]
    exact bySize_decides hg (by simp [Val.size?]) (sizeCons_decides c M (by simp at hM; omega))
  | from_ c =>
    simp only [elem]
    cases c with
    | mk r ext a =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by simp at hM; omega⟩
      simp only [cons, ESet.byAlphabet, VSet.keepExt, VSet.ofSpecs, DecidesES]
      constructor
      · intro b hb
        split at hb
        · rename_i hany
          simp at hb; subst hb
          simp only [List.any_eq_true] at hany
          obtain ⟨ch, hch, hno⟩ := hany
          simp only [Bool.false_eq_true, iff_false, not_and]
          intro _ hall _
          obtain ⟨s, hs, hcs⟩ := hall ch (by simpa [Val.charList] using hch)
          exact alphaNo_sound hpt r M (by simp at hM; omega) hno s (.inl hs) hcs
        · simp at hb
      · intro b hb
        split at hb
        · rename_i hany
          simp at hb; subst hb
          simp only [List.any_eq_true, Bool.and_eq_true] at hany
          obtain ⟨ch, hch, hno, hnoa⟩ := hany
          simp only [Bool.false_eq_true, iff_false, not_and]
          intro _ hall _
          obtain ⟨s, hs, hcs⟩ := hall ch (by simpa [Val.charList] using hch)
          rcases hs with hs | ⟨e, he, hs⟩
          · exact alphaNo_sound hpt r M (by simp at hM; omega) hno s (.inr hs) hcs
          · cases a with
            | none => simp at he
            | some a' =>
              simp at he; subst he
              simp at hnoa
              exact alphaNo_sound hpt a' M (by simp at hM; omega) hnoa s (.inr hs) hcs
        · simp at hb
    | _ => exact ⟨Decides.none', Decides.none'⟩
  | _ => exact ⟨Decides.none', Decides.none'⟩


/-! ## The walk through tags, constraints and references -/

/-- All the values of a type if `w`, its root if not. -/
def VSet.at (S : VSet) (w : Bool) (x : Val) : Prop := if w then S.all x else S.root x

theorem cons_at_parent {M : Nat} {sc : Scope} {outer : List Frame} {pt : Ty} {parent : VSet}
    {c : Constraint} {w : Bool} {x : Val} (h : (cons E H M sc outer pt parent c).at w x) : parent.root x := by
  unfold VSet.at at h; cases w <;> simp at h
  · exact cons_sub_parent (.inl h)
  · exact cons_sub_parent (.inr h)

/-- `notInTy` decides only what the spec says: when each decision on its way is the spec's on the
values with `X`, no value with `X` is (eventually) a value of `t` where it says `true`. -/
theorem notInTy_sound {n : Nat} {dec : Scope → Bool → Constraint → Option Bool} {X : Val → Prop}
    {P : Scope → Ty → Prop}
    (hPc : ∀ sc t c, P sc (.constrained t c) → P sc t)
    (hPt : ∀ sc tg k t, P sc (.tagged tg k t) → P sc t)
    (hPr : ∀ sc nm sc' t, P sc (.ref nm) → resolveTy E n sc none nm [] = some (sc', t) → P sc' t)
    (hPe : ∀ sc mn nm sc' t, P sc (.extRef mn nm) → resolveTy E n sc (some mn) nm [] = some (sc', t) → P sc' t)
    (hdec : ∀ sc t c w, P sc (.constrained t c) → dec sc w c = some false →
      ∃ M0, ∀ M, M0 ≤ M → ∀ outer x, X x → ¬ (cons E H M sc outer t (sem E H M sc outer t) c).at w x) :
    ∀ (k : Nat) (sc : Scope) (t : Ty) (w : Bool), P sc t → notInTy E n dec k sc t w = true →
      ¬ ∀ N, ∃ M, N ≤ M ∧ ∃ outer x, X x ∧ (sem E H M sc outer t).at w x
  | 0, _, _, _, _, h, _ => by simp [notInTy] at h
  | k + 1, sc, .constrained t c, w, hP, h, hN => by
    simp only [notInTy, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · obtain ⟨M0, hM0⟩ := hdec sc t c w hP h
      obtain ⟨M, hM, outer, x, hx, hm⟩ := hN (M0 + 1)
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simp only [sem] at hm
      exact hM0 M (by omega) outer x hx hm
    · refine notInTy_sound hPc hPt hPr hPe hdec k sc t false (hPc _ _ _ hP) h fun N => ?_
      obtain ⟨M, hM, outer, x, hx, hm⟩ := hN (N + 1)
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simp only [sem] at hm
      exact ⟨M, by omega, outer, x, hx, by simpa [VSet.at] using cons_at_parent hm⟩
  | k + 1, sc, .tagged tg kk t, w, hP, h, hN => by
    simp only [notInTy] at h
    refine notInTy_sound hPc hPt hPr hPe hdec k sc t w (hPt _ _ _ _ hP) h fun N => ?_
    obtain ⟨M, hM, outer, x, hx, hm⟩ := hN (N + 1)
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    simp only [sem] at hm
    exact ⟨M, by omega, outer, x, hx, hm⟩
  | k + 1, sc, .ref nm, w, hP, h, hN => by
    simp only [notInTy] at h
    split at h
    · rename_i sc' t' hr
      refine notInTy_sound hPc hPt hPr hPe hdec k sc' t' w (hPr _ _ _ _ hP hr) h fun N => ?_
      obtain ⟨M, hM, outer, x, hx, hm⟩ := hN (max N n + 1)
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simp only [sem, resolveTy_mono hr (by omega : n ≤ M)] at hm
      exact ⟨M, by omega, [], x, hx, hm⟩
    · simp at h
  | k + 1, sc, .extRef mn nm, w, hP, h, hN => by
    simp only [notInTy] at h
    split at h
    · rename_i sc' t' hr
      refine notInTy_sound hPc hPt hPr hPe hdec k sc' t' w (hPe _ _ _ _ _ hP hr) h fun N => ?_
      obtain ⟨M, hM, outer, x, hx, hm⟩ := hN (max N n + 1)
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simp only [sem, resolveTy_mono hr (by omega : n ≤ M)] at hm
      exact ⟨M, by omega, [], x, hx, hm⟩
    · simp at h
  | k + 1, sc, .boolean, w, _, h, _ | k + 1, sc, .integer _, w, _, h, _
  | k + 1, sc, .enumerated .., w, _, h, _ | k + 1, sc, .real, w, _, h, _
  | k + 1, sc, .bitString _, w, _, h, _ | k + 1, sc, .octetString, w, _, h, _
  | k + 1, sc, .null, w, _, h, _ | k + 1, sc, .sequence .., w, _, h, _
  | k + 1, sc, .set .., w, _, h, _ | k + 1, sc, .sequenceOf _, w, _, h, _
  | k + 1, sc, .setOf _, w, _, h, _ | k + 1, sc, .choice .., w, _, h, _
  | k + 1, sc, .selection .., w, _, h, _ | k + 1, sc, .objectIdentifier, w, _, h, _
  | k + 1, sc, .relativeOid, w, _, h, _ | k + 1, sc, .oidIri, w, _, h, _
  | k + 1, sc, .relativeOidIri, w, _, h, _ | k + 1, sc, .embeddedPdv, w, _, h, _
  | k + 1, sc, .external, w, _, h, _ | k + 1, sc, .characterString, w, _, h, _
  | k + 1, sc, .restricted _, w, _, h, _ | k + 1, sc, .time, w, _, h, _
  | k + 1, sc, .date, w, _, h, _ | k + 1, sc, .timeOfDay, w, _, h, _
  | k + 1, sc, .dateTime, w, _, h, _ | k + 1, sc, .duration, w, _, h, _
  | k + 1, sc, .generalizedTime, w, _, h, _ | k + 1, sc, .utcTime, w, _, h, _
  | k + 1, sc, .objectDescriptor, w, _, h, _ | k + 1, sc, .paramRef .., w, _, h, _
  | k + 1, sc, .openType, w, _, h, _ | k + 1, sc, .classField .., w, _, h, _
  | k + 1, sc, .fromObjects .., w, _, h, _ | k + 1, sc, .instanceOf _, w, _, h, _ => by
    simp [notInTy] at h


/-- `t` is (through references, tags and constraints) a type whose equal values are equal. -/
def EqTy (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Prop :=
  ∃ sc' b, builtin E n sc t = some (sc', b) ∧ EqBase b

theorem EqTy.constrained {n : Nat} {sc : Scope} {t : Ty} {c : Constraint} (h : EqTy E n sc (.constrained t c)) :
    EqTy E n sc t := by
  obtain ⟨sc', b, hb, he⟩ := h
  cases n with
  | zero => simp [builtin] at hb
  | succ n => simp only [builtin] at hb; exact ⟨sc', b, builtin_mono hb (by omega), he⟩

theorem EqTy.tagged {n : Nat} {sc : Scope} {tg : Tag} {k : TagKind} {t : Ty} (h : EqTy E n sc (.tagged tg k t)) :
    EqTy E n sc t := by
  obtain ⟨sc', b, hb, he⟩ := h
  cases n with
  | zero => simp [builtin] at hb
  | succ n => simp only [builtin] at hb; exact ⟨sc', b, builtin_mono hb (by omega), he⟩

theorem EqTy.ref {n : Nat} {sc : Scope} {nm : String} {sc' : Scope} {t' : Ty}
    (h : EqTy E n sc (.ref nm)) (hr : resolveTy E n sc none nm [] = some (sc', t')) : EqTy E n sc' t' := by
  obtain ⟨s, b, hb, he⟩ := h
  cases n with
  | zero => simp [builtin] at hb
  | succ n =>
    simp only [builtin, Option.bind_eq_some_iff] at hb
    obtain ⟨⟨s2, u⟩, h1, h2⟩ := hb
    rw [resolveTy_mono h1 (by omega)] at hr; cases hr
    exact ⟨s, b, builtin_mono h2 (by omega), he⟩

theorem EqTy.extRef {n : Nat} {sc : Scope} {mn nm : String} {sc' : Scope} {t' : Ty}
    (h : EqTy E n sc (.extRef mn nm)) (hr : resolveTy E n sc (some mn) nm [] = some (sc', t')) :
    EqTy E n sc' t' := by
  obtain ⟨s, b, hb, he⟩ := h
  cases n with
  | zero => simp [builtin] at hb
  | succ n =>
    simp only [builtin, Option.bind_eq_some_iff] at hb
    obtain ⟨⟨s2, u⟩, h1, h2⟩ := hb
    rw [resolveTy_mono h1 (by omega)] at hr; cases hr
    exact ⟨s, b, builtin_mono h2 (by omega), he⟩

theorem EqTy.eqv {n : Nat} {sc : Scope} {t : Ty} (h : EqTy E n sc t) :
    ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc t x y ↔ x = y := by
  obtain ⟨s, b, hb, he⟩ := h
  exact eqv_eq_of_builtin hb he

theorem intNotInTy_sound {n : Nat} {sc : Scope} {t : Ty} {i : Int} {w : Bool} (hP : EqTy E n sc t)
    (h : intNotInTy E n 16 sc t i w = true) :
    ¬ ∀ N, ∃ M, N ≤ M ∧ ∃ outer, (sem E H M sc outer t).at w (.int i) := by
  intro hN
  refine notInTy_sound (H := H) (X := (· = .int i)) (P := EqTy E n) (fun _ _ _ h => h.constrained)
    (fun _ _ _ _ h => h.tagged) (fun _ _ _ _ h hr => h.ref hr) (fun _ _ _ _ _ h hr => h.extRef hr) ?_
    16 sc t w hP h fun N => ?_
  · intro sc t c w hP hd
    refine ⟨n + 13 + sizeOf c, fun M hM outer x hx hm => ?_⟩
    subst hx
    have hg := cons_at_parent hm
    have hpt := hP.constrained.eqv
    cases c with
    | mk r ext a =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have hD := decCons_decides (es := intInES E n sc i) (ext := ext) (a := a) (H := H) (outer := outer)
        (intInES_decides hg hpt r M (by simp at hM; omega))
        (fun a' ha => by subst ha; exact intInES_decides hg hpt a' M (by simp at hM; omega))
      simp only [intInCons] at hd
      unfold VSet.at at hm
      cases w
      · exact hD.1.some_false hd hm
      · exact hD.2.some_false hd hm
    | _ => cases w <;> simp [intInCons, decCons] at hd
  · obtain ⟨M, hM, outer, hm⟩ := hN N
    exact ⟨M, hM, outer, _, rfl, hm⟩

theorem sizeNotInTy_sound {n : Nat} {sc : Scope} {t : Ty} {len : Nat} {w : Bool}
    (h : sizeNotInTy E n 16 sc t len w = true) :
    ¬ ∀ N, ∃ M, N ≤ M ∧ ∃ outer x, x.size? = some len ∧ (sem E H M sc outer t).at w x := by
  intro hN
  refine notInTy_sound (H := H) (X := (·.size? = some len)) (P := fun _ _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_
    16 sc t w trivial h hN
  intro sc t c w _ hd
  refine ⟨n + 14 + sizeOf c, fun M hM outer x hx hm => ?_⟩
  have hg := cons_at_parent hm
  cases c with
  | mk r ext a =>
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have hD := decCons_decides (es := sizeInES E n sc len) (ext := ext) (a := a) (H := H) (outer := outer) (pt := t)
      (sizeInES_decides hg hx r M (by simp at hM; omega))
      (fun a' ha => by subst ha; exact sizeInES_decides hg hx a' M (by simp at hM; omega))
    simp only [sizeInCons] at hd
    unfold VSet.at at hm
    cases w
    · exact hD.1.some_false hd hm
    · exact hD.2.some_false hd hm
  | _ => cases w <;> simp [sizeInCons, decCons] at hd

theorem charsNotInTy_sound {n : Nat} {sc : Scope} {t : Ty} {cs : List Nat} {w : Bool} (hP : EqTy E n sc t)
    (h : charsNotInTy E n 16 sc t cs w = true) :
    ¬ ∀ N, ∃ M, N ≤ M ∧ ∃ outer, (sem E H M sc outer t).at w (.chars cs) := by
  intro hN
  refine notInTy_sound (H := H) (X := (· = .chars cs)) (P := EqTy E n) (fun _ _ _ h => h.constrained)
    (fun _ _ _ _ h => h.tagged) (fun _ _ _ _ h hr => h.ref hr) (fun _ _ _ _ _ h hr => h.extRef hr) ?_
    16 sc t w hP h fun N => ?_
  · intro sc t c w hP hd
    refine ⟨n + 15 + sizeOf c, fun M hM outer x hx hm => ?_⟩
    subst hx
    have hg := cons_at_parent hm
    have hpt := hP.constrained.eqv
    cases c with
    | mk r ext a =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have hD := decCons_decides (es := charsInES E n sc cs) (ext := ext) (a := a) (H := H) (outer := outer)
        (charsInES_decides hg hpt r M (by simp at hM; omega))
        (fun a' ha => by subst ha; exact charsInES_decides hg hpt a' M (by simp at hM; omega))
      simp only [charsInCons] at hd
      unfold VSet.at at hm
      cases w
      · exact hD.1.some_false hd hm
      · exact hD.2.some_false hd hm
    | _ => cases w <;> simp [charsInCons, decCons] at hd
  · obtain ⟨M, hM, outer, hm⟩ := hN N
    exact ⟨M, hM, outer, _, rfl, hm⟩

section Walk

variable {E : Env} {H : ContentsHook}

/-- `sem` follows `builtinV`: a value of `t` is a value (or root value) of its built-in type. -/
theorem sem_builtinV : ∀ {n : Nat} {sc : Scope} {t : Ty} {sc' : Scope} {b : Ty},
    builtinV E n sc t = some (sc', b) → ∃ d, ∀ M, n ≤ M → ∀ outer x w,
      (sem E H (M + d) sc outer t).at w x → ∃ outer' w', (sem E H M sc' outer' b).at w' x
  | 0, _, _, _, _, h => by simp [builtinV] at h
  | n + 1, sc, t, sc', b, h => by
    cases t with
    | ref name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨d, hd⟩ := sem_builtinV h2
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem, resolveTy_mono h1 (by omega : n ≤ M + d)] at hm
      exact hd M (by omega) _ x w hm
    | extRef mn name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨d, hd⟩ := sem_builtinV h2
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem, resolveTy_mono h1 (by omega : n ≤ M + d)] at hm
      exact hd M (by omega) _ x w hm
    | paramRef mn name args =>
      simp only [builtinV, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨d, hd⟩ := sem_builtinV h2
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem, resolveTy_mono h1 (by omega : n ≤ M + d)] at hm
      exact hd M (by omega) _ x w hm
    | tagged tg k u =>
      simp only [builtinV] at h
      obtain ⟨d, hd⟩ := sem_builtinV h
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem] at hm
      exact hd M (by omega) _ x w hm
    | constrained u c =>
      simp only [builtinV] at h
      obtain ⟨d, hd⟩ := sem_builtinV h
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem] at hm
      exact hd M (by omega) outer x false (by simpa [VSet.at] using cons_at_parent hm)
    | instanceOf cls =>
      simp only [builtinV] at h
      obtain ⟨d, hd⟩ := sem_builtinV h
      refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
      rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
      simp only [sem] at hm
      exact hd M (by omega) outer x w (by simpa [VSet.at, VSet.noExt] using hm)
    | selection nm u =>
      simp only [builtinV] at h
      split at h
      · rename_i s root ext hu
        split at h
        · rename_i a ha
          obtain ⟨d, hd⟩ := sem_builtinV h
          refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
          rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
          simp only [sem, builtin_mono hu (by omega : n ≤ M + d), ha] at hm
          exact hd M (by omega) _ x w hm
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtinV] at h
      split at h
      · rename_i s nm u un o hf
        obtain ⟨d, hd⟩ := sem_builtinV h
        refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
        rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
        simp only [sem, bind_fields_mono hf (by omega : n ≤ M + d)] at hm
        exact hd M (by omega) _ x w hm
      · rename_i s nm u o hf
        obtain ⟨d, hd⟩ := sem_builtinV h
        refine ⟨d + 1, fun M hM outer x w hm => ?_⟩
        rw [show M + (d + 1) = (M + d) + 1 by omega] at hm
        simp only [sem, bind_fields_mono hf (by omega : n ≤ M + d)] at hm
        exact hd M (by omega) _ x w hm
      · simp at h
    | fromObjects src path => simp [builtinV] at h
    | _ =>
      simp only [builtinV, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, fun M _ outer x w hm => ⟨outer, w, hm⟩⟩

/-- Pigeonhole: what holds at arbitrarily large fuel for some element of a list, holds at
arbitrarily large fuel for one of them. -/
theorem frequently_mem {α : Type} {l : List α} {Q : α → Nat → Prop}
    (h : ∀ N, ∃ M, N ≤ M ∧ ∃ a ∈ l, Q a M) : ∃ a ∈ l, ∀ N, ∃ M, N ≤ M ∧ Q a M := by
  induction l with
  | nil => obtain ⟨M, _, a, ha, _⟩ := h 0; simp at ha
  | cons x l ih =>
    by_cases hx : ∀ N, ∃ M, N ≤ M ∧ Q x M
    · exact ⟨x, by simp, hx⟩
    · push Not at hx
      obtain ⟨N0, hN0⟩ := hx
      obtain ⟨a, ha, hq⟩ := ih fun N => by
        obtain ⟨M, hM, a, ha, hq⟩ := h (max N N0)
        rcases List.mem_cons.mp ha with rfl | ha
        · exact absurd hq (hN0 M (by omega))
        · exact ⟨M, by omega, a, ha, hq⟩
      exact ⟨a, List.mem_cons_of_mem _ ha, hq⟩


/-! ## Values -/

/-- `v`, written in `vsc`, evaluates at arbitrarily large fuel to a value of `t`, read in `sc`
(evaluated with at least the type's fuel). -/
def ValIn (E : Env) (H : ContentsHook) (vsc : Scope) (v : Val) (sc : Scope) (t : Ty) : Prop :=
  ∀ N, ∃ M, N ≤ M ∧ ∃ M2, M ≤ M2 ∧ ∃ outer w, evalVal E M2 vsc v w ∧ (sem E H M sc outer t).all w

theorem isIntTy_eqTy {n : Nat} {sc : Scope} {t : Ty} (h : isIntTy E n sc t = true) : EqTy E n sc t := by
  unfold isIntTy at h
  split at h
  · rename_i s nb hb; exact ⟨s, _, hb, trivial⟩
  · simp at h

theorem intValOkB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (hv : ValIn E H vsc v sc t) :
    intValOkB E n sc t v vsc = true := by
  unfold intValOkB
  cases hi : isIntTy E n sc t with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    split
    · rename_i i hv'
      cases hn : intNotInTy E n 16 sc t i true with
      | false => rfl
      | true =>
        exfalso
        refine intNotInTy_sound (H := H) (isIntTy_eqTy hi) hn fun N => ?_
        obtain ⟨M, hM, M2, hM2, outer, w, he, hm⟩ := hv (max N (n + 9))
        rw [(evalVal_of_intOfV hv' M2 (by omega) w).mp he] at hm
        exact ⟨M, by omega, outer, by simpa [VSet.at] using hm⟩
    · rfl

theorem size_evalVal {M : Nat} {sc : Scope} {v w : Val} {len : Nat} (hs : v.size? = some len)
    (h : evalVal E M sc v w) : w.size? = some len := by
  cases M with
  | zero => simp [evalVal] at h
  | succ M =>
    cases v <;> simp [Val.size?] at hs
    all_goals first
      | (simp only [evalVal] at h; subst h; simpa [Val.size?] using hs)
      | (simp only [evalVal] at h; obtain ⟨ws, rfl, hw⟩ := h; simp [Val.size?, ← hs, hw.length_eq])

theorem sizeValOkB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (hv : ValIn E H vsc v sc t) :
    sizeValOkB E n sc t v = true := by
  unfold sizeValOkB
  split
  · rename_i len s bt hs hb
    have key : sizeNotInTy E n 16 sc t len true = false := by
      cases hn : sizeNotInTy E n 16 sc t len true with
      | false => rfl
      | true =>
        exfalso
        refine sizeNotInTy_sound (H := H) hn fun N => ?_
        obtain ⟨M, hM, M2, hM2, outer, w, he, hm⟩ := hv N
        exact ⟨M, hM, outer, w, size_evalVal hs he, by simpa [VSet.at] using hm⟩
    dsimp only
    have h1 : ((List.range 65).any fun d => !sizeNotInTy E n 16 sc t (len + d) true) = true :=
      List.any_eq_true.mpr ⟨0, List.mem_range.mpr (by omega), by simpa using key⟩
    have h2 : (!sizeNotInTy E n 16 sc t len true) = true := by simp [key]
    split_ifs <;> assumption
  · rfl

theorem charsValOkB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (hv : ValIn E H vsc v sc t) :
    charsValOkB E n sc t v vsc = true := by
  unfold charsValOkB
  split
  · rename_i s k hb
    split
    · rename_i cs hc
      cases hn : charsNotInTy E n 16 sc t cs true with
      | false => rfl
      | true =>
        exfalso
        refine charsNotInTy_sound (H := H) ⟨s, _, hb, trivial⟩ hn fun N => ?_
        obtain ⟨M, hM, M2, hM2, outer, w, he, hm⟩ := hv (max N (n + 9))
        rw [(evalVal_of_charsOfV hc M2 (by omega) w).mp he] at hm
        exact ⟨M, by omega, outer, by simpa [VSet.at] using hm⟩
    · rfl
  · rfl

/-- A value of `t`, through `builtinV`, at arbitrarily large fuel: the value notation, evaluated
with at least the type's fuel, is a value of the built-in type. -/
theorem valIn_builtinV {n : Nat} {sc vsc sc' : Scope} {t b : Ty} {v : Val} (hv : ValIn E H vsc v sc t)
    (hb : builtinV E n sc t = some (sc', b)) :
    ∀ N, ∃ M, N ≤ M ∧ ∃ M2, M ≤ M2 ∧ ∃ outer w x, evalVal E M2 vsc v x ∧ (sem E H M sc' outer b).at w x := by
  obtain ⟨d, hd⟩ := sem_builtinV (H := H) hb
  intro N
  obtain ⟨M, hM, M2, hM2, outer, x, he, hm⟩ := hv (max N n + d)
  obtain ⟨outer', w', hm'⟩ := hd (M - d) (by omega) outer x true
    (by rw [show M - d + d = M by omega]; simpa [VSet.at] using hm)
  exact ⟨M - d, by omega, M2, by omega, outer', w', x, he, hm'⟩

theorem timeFmtOkB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (hv : ValIn E H vsc v sc t) :
    timeFmtOkB E n sc t v vsc = true := by
  unfold timeFmtOkB
  split
  · rename_i s hb
    cases hc : charsOfV E n vsc 8 v with
    | none => rfl
    | some cs =>
      obtain ⟨M, hM, M2, hM2, outer, w, x, he, hm⟩ := valIn_builtinV hv hb (n + 10)
      rw [(evalVal_of_charsOfV hc M2 (by omega) x).mp he] at hm
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      cases w <;> simp [VSet.at, sem, formatVSet, VSet.plain] at hm <;> simp [hm.2]
  · rename_i s hb
    cases hc : charsOfV E n vsc 8 v with
    | none => rfl
    | some cs =>
      obtain ⟨M, hM, M2, hM2, outer, w, x, he, hm⟩ := valIn_builtinV hv hb (n + 10)
      rw [(evalVal_of_charsOfV hc M2 (by omega) x).mp he] at hm
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      cases w <;> simp [VSet.at, sem, formatVSet, VSet.plain] at hm <;> simp [hm.2]
  · rfl


theorem seq_comp_valIn {n : Nat} {sc vsc sc' : Scope} {t : Ty} {ro r2 : List Comp} {e : Option (List ExtAdd)}
    {cs : List (String × Val)} {nm : String} {w : Val} {b : Ty}
    (hv : ValIn E H vsc (.seq cs) sc t) (hb : builtinV E n sc t = some (sc', b))
    (hbt : b = .sequence ro e r2 ∨ b = .set ro e r2)
    (hk : entriesKnown E n sc' ro e r2 = true) (hm : (nm, w) ∈ cs) :
    ∃ en ∈ entries E n sc' ro e r2, en.name = nm ∧ ValIn E H vsc w en.scope en.ty := by
  obtain ⟨en, hen, hq⟩ := frequently_mem (l := entries E n sc' ro e r2)
    (Q := fun en M => en.name = nm ∧ ∃ M2, M ≤ M2 ∧ ∃ outer w', evalVal E M2 vsc w w' ∧
      (sem E H M en.scope outer en.ty).all w') fun N => by
    obtain ⟨M, hM, M2, hM2, outer, wb, x, he, hx⟩ := valIn_builtinV hv hb (max N n + 2)
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨M2, rfl⟩ : ∃ M', M2 = M' + 1 := ⟨M2 - 1, by omega⟩
    simp only [evalVal] at he
    obtain ⟨ds, rfl, hds⟩ := he
    have hok : ∀ p ∈ ds, ∃ en ∈ entries E n sc' ro e r2, en.name = p.1 ∧ ∃ outer',
        (sem E H M en.scope outer' en.ty).all p.2 := by
      intro p hp
      rcases hbt with rfl | rfl <;>
      · simp only [sem, seqVSet, VSet.at, entries_stable hk (by omega : n ≤ M)] at hx
        have hx' : ∃ cs', Val.seq ds = .seq cs' ∧ ∀ p ∈ cs', ∃ en ∈ entries E n sc' ro e r2,
            en.name = p.1 ∧ ∃ outer', (sem E H M en.scope outer' en.ty).all p.2 := by
          cases wb <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx
          · obtain ⟨cs', h1, ⟨-, h2⟩, -⟩ := hx
            exact ⟨cs', h1, fun p hp => by obtain ⟨en, h3, h4, h5⟩ := h2 p hp; exact ⟨en, h3, h4, _, h5⟩⟩
          · obtain ⟨cs', h1, -, h2⟩ := hx
            exact ⟨cs', h1, fun p hp => by obtain ⟨en, h3, h4, h5⟩ := h2 p hp; exact ⟨en, h3, h4, _, h5⟩⟩
        obtain ⟨cs', h1, h2⟩ := hx'
        simp only [Val.seq.injEq] at h1; subst h1
        exact h2 p hp
    obtain ⟨p, hp, hpe, hpev⟩ := forall₂_mem_left hds _ hm
    obtain ⟨en, hen, hname, outer', hsem⟩ := hok p hp
    exact ⟨M, by omega, en, hen, by rw [hname, ← hpe], M2, by omega, outer', p.2, hpev, hsem⟩
  refine ⟨en, hen, ?_, fun N => ?_⟩
  · obtain ⟨M, -, h, -⟩ := hq 0; exact h
  · obtain ⟨M, hM, -, h⟩ := hq N; exact ⟨M, hM, h⟩

theorem seqOf_comp_valIn {n : Nat} {sc vsc sc' : Scope} {t el : Ty} {v : Val} {vs : List Val} {w : Val} {b : Ty}
    (hv : ValIn E H vsc v sc t) (hvs : v = .seqOf vs ∨ v = .setOf vs) (hb : builtinV E n sc t = some (sc', b))
    (hbt : b = .sequenceOf el ∨ b = .setOf el) (hm : w ∈ vs) : ValIn E H vsc w sc' el := by
  intro N
  obtain ⟨M, hM, M2, hM2, outer, wb, x, he, hx⟩ := valIn_builtinV hv hb (max N n + 2)
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨M2, rfl⟩ : ∃ M', M2 = M' + 1 := ⟨M2 - 1, by omega⟩
  have hx' : ∃ ys, (x = .seqOf ys ∨ x = .setOf ys) ∧ ∀ y ∈ ys, ∃ outer', (sem E H M sc' outer' el).all y := by
    rcases hbt with rfl | rfl <;> cases wb <;> simp only [sem, VSet.at, VSet.plain, Bool.false_eq_true, ↓reduceIte] at hx <;>
      obtain ⟨ys, rfl, hy⟩ := hx <;> exact ⟨ys, by simp, fun y hy' => ⟨_, hy y hy'⟩⟩
  obtain ⟨ys, hxs, hys⟩ := hx'
  have hws : ∃ ws, (x = .seqOf ws ∨ x = .setOf ws) ∧ List.Forall₂ (evalVal E M2 vsc) vs ws := by
    rcases hvs with rfl | rfl <;> simp only [evalVal] at he <;> obtain ⟨ws, rfl, hw⟩ := he <;> exact ⟨ws, by simp, hw⟩
  obtain ⟨ws, hxw, hw⟩ := hws
  have : ws = ys := by rcases hxs with rfl | rfl <;> rcases hxw with h | h <;> simp_all
  subst this
  obtain ⟨y, hy, hev⟩ := forall₂_mem_left hw _ hm
  obtain ⟨outer', hsem⟩ := hys y hy
  exact ⟨M, by omega, M2, by omega, outer', y, hev, hsem⟩

theorem choice_comp_valIn {n : Nat} {sc vsc sc' : Scope} {t : Ty} {ro : List Alt} {ext : Option (List AltAdd)}
    {a : String} {w : Val} (hv : ValIn E H vsc (.choice a w) sc t)
    (hb : builtinV E n sc t = some (sc', .choice ro ext)) :
    ∃ alt ∈ choiceAlts ro ext, alt.name = a ∧ ValIn E H vsc w sc' alt.ty := by
  obtain ⟨al, hal, hq⟩ := frequently_mem (l := choiceAlts ro ext)
    (Q := fun al M => al.name = a ∧ ∃ M2, M ≤ M2 ∧ ∃ outer w', evalVal E M2 vsc w w' ∧
      (sem E H M sc' outer al.ty).all w') fun N => by
    obtain ⟨M, hM, M2, hM2, outer, wb, x, he, hx⟩ := valIn_builtinV hv hb (max N n + 2)
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨M2, rfl⟩ : ∃ M', M2 = M' + 1 := ⟨M2 - 1, by omega⟩
    simp only [evalVal] at he
    obtain ⟨y, rfl, hy⟩ := he
    have hx' : ∃ al ∈ choiceAlts ro ext, ∃ y', Val.choice a y = .choice al.name y' ∧ ∃ outer',
        (sem E H M sc' outer' al.ty).all y' := by
      cases wb <;> simp only [sem, choiceVSet, VSet.at, Bool.false_eq_true, ↓reduceIte] at hx
      · obtain ⟨al, hal, y', h1, h2⟩ := hx
        exact ⟨al, by simp [choiceAlts, hal], y', h1, _, h2⟩
      · obtain ⟨al, hal, y', h1, h2⟩ := hx
        exact ⟨al, hal, y', h1, _, h2⟩
    obtain ⟨al, hal, y', h1, outer', h2⟩ := hx'
    simp only [Val.choice.injEq] at h1
    obtain ⟨h1, h1'⟩ := h1
    subst h1'
    exact ⟨M, by omega, al, hal, h1.symm, M2, by omega, outer', y, hy, h2⟩
  refine ⟨al, hal, ?_, fun N => ?_⟩
  · obtain ⟨M, -, h, -⟩ := hq 0; exact h
  · obtain ⟨M, hM, -, h⟩ := hq N; exact ⟨M, hM, h⟩


theorem valSemB_of {n : Nat} {vsc : Scope} (v : Val) : ∀ {sc : Scope} {t : Ty}, ValIn E H vsc v sc t →
    valSemB E n sc t v vsc = true := by
  induction v using WellFounded.induction (measure (sizeOf : Val → Nat)).wf with
  | _ v ih =>
  intro sc t hv
  rw [valSemB.eq_def, intValOkB_of hv, sizeValOkB_of hv, charsValOkB_of hv, timeFmtOkB_of hv]
  simp only [Bool.true_and]
  cases v with
  | seq cs =>
    simp only
    split
    · rename_i sc' ro e r2 hb
      cases hk : entriesKnown E n sc' ro e r2 with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
        intro ⟨⟨nm, w⟩, hmem⟩ _
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
        right
        obtain ⟨en, hen, hname, hw⟩ := seq_comp_valIn hv hb (.inl rfl) hk hmem
        refine ⟨en, hen, hname, ih w ?_ hw⟩
        show sizeOf w < sizeOf (Val.seq cs)
        have := List.sizeOf_lt_of_mem hmem
        simp at this ⊢; omega
    · rename_i sc' ro e r2 hb
      cases hk : entriesKnown E n sc' ro e r2 with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
        intro ⟨⟨nm, w⟩, hmem⟩ _
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
        right
        obtain ⟨en, hen, hname, hw⟩ := seq_comp_valIn hv hb (.inr rfl) hk hmem
        refine ⟨en, hen, hname, ih w ?_ hw⟩
        show sizeOf w < sizeOf (Val.seq cs)
        have := List.sizeOf_lt_of_mem hmem
        simp at this ⊢; omega
    · rfl
  | seqOf vs =>
    simp only
    split
    · rename_i sc' el hb
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      exact ih w (show sizeOf w < sizeOf (Val.seqOf vs) by have := List.sizeOf_lt_of_mem hmem; simp; omega)
        (seqOf_comp_valIn hv (.inl rfl) hb (.inl rfl) hmem)
    · rename_i sc' el hb
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      exact ih w (show sizeOf w < sizeOf (Val.seqOf vs) by have := List.sizeOf_lt_of_mem hmem; simp; omega)
        (seqOf_comp_valIn hv (.inl rfl) hb (.inr rfl) hmem)
    · rfl
  | setOf vs =>
    simp only
    split
    · rename_i sc' el hb
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      exact ih w (show sizeOf w < sizeOf (Val.setOf vs) by have := List.sizeOf_lt_of_mem hmem; simp; omega)
        (seqOf_comp_valIn hv (.inr rfl) hb (.inl rfl) hmem)
    · rename_i sc' el hb
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      exact ih w (show sizeOf w < sizeOf (Val.setOf vs) by have := List.sizeOf_lt_of_mem hmem; simp; omega)
        (seqOf_comp_valIn hv (.inr rfl) hb (.inr rfl) hmem)
    · rfl
  | choice a w =>
    simp only
    split
    · rename_i sc' ro ext hb
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      right
      obtain ⟨al, hal, hname, hw⟩ := choice_comp_valIn hv hb
      exact ⟨al, hal, hname, ih w (show sizeOf w < sizeOf (Val.choice a w) by simp) hw⟩
    · rfl
  | _ => rfl


theorem refMapsB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (h : RefMaps E n sc t vsc v) :
    refMapsB E n sc t v vsc = true := by
  cases v with
  | ref mn nm args =>
    simp only [RefMaps] at h
    simp only [refMapsB]
    split
    · rename_i usc u p hu hp
      split
      · rename_i q hq; simp [h usc u p q hu hp hq]
      · rfl
    · rfl
  | _ => simp [refMapsB]

theorem valMapsB_of {n : Nat} {vsc : Scope} (v : Val) : ∀ {k : Nat} {sc : Scope} {t : Ty}, sizeOf v < k →
    ValMaps E n k sc t vsc v → valMapsB E n sc t v vsc = true := by
  induction v using WellFounded.induction (measure (sizeOf : Val → Nat)).wf with
  | _ v ih =>
  intro k sc t hk h
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [ValMaps] at h
  obtain ⟨hr, h⟩ := h
  rw [valMapsB.eq_def, refMapsB_of hr, Bool.true_and]
  cases v with
  | seq cs =>
    simp only
    split
    · rename_i sc' ro e r2 hb
      rw [hb] at h; simp only at h
      simp only [Bool.or_eq_true, List.all_eq_true]
      right
      intro ⟨⟨nm, w⟩, hmem⟩ _
      simp only
      split
      · rename_i en hen
        have hlt : sizeOf w < sizeOf (Val.seq cs) := by
          have := List.sizeOf_lt_of_mem hmem; simp at this ⊢; omega
        exact ih w hlt (by omega) (h nm w hmem en hen)
      · rfl
    · rename_i sc' ro e r2 hb
      rw [hb] at h; simp only at h
      simp only [Bool.or_eq_true, List.all_eq_true]
      right
      intro ⟨⟨nm, w⟩, hmem⟩ _
      simp only
      split
      · rename_i en hen
        have hlt : sizeOf w < sizeOf (Val.seq cs) := by
          have := List.sizeOf_lt_of_mem hmem; simp at this ⊢; omega
        exact ih w hlt (by omega) (h nm w hmem en hen)
      · rfl
    · rfl
  | seqOf vs =>
    simp only
    split
    · rename_i sc' el hb
      rw [hb] at h; simp only at h
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      have hlt : sizeOf w < sizeOf (Val.seqOf vs) := by
        have := List.sizeOf_lt_of_mem hmem; simp; omega
      exact ih w hlt (by omega) (h w hmem)
    · rename_i sc' el hb
      rw [hb] at h; simp only at h
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      have hlt : sizeOf w < sizeOf (Val.seqOf vs) := by
        have := List.sizeOf_lt_of_mem hmem; simp; omega
      exact ih w hlt (by omega) (h w hmem)
    · rfl
  | setOf vs =>
    simp only
    split
    · rename_i sc' el hb
      rw [hb] at h; simp only at h
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      have hlt : sizeOf w < sizeOf (Val.setOf vs) := by
        have := List.sizeOf_lt_of_mem hmem; simp; omega
      exact ih w hlt (by omega) (h w hmem)
    · rename_i sc' el hb
      rw [hb] at h; simp only at h
      simp only [List.all_eq_true]
      intro ⟨w, hmem⟩ _
      have hlt : sizeOf w < sizeOf (Val.setOf vs) := by
        have := List.sizeOf_lt_of_mem hmem; simp; omega
      exact ih w hlt (by omega) (h w hmem)
    · rfl
  | choice a w =>
    simp only
    split
    · rename_i sc' ro ext hb
      rw [hb] at h; simp only at h
      split
      · rename_i alt halt
        exact ih w (show sizeOf w < sizeOf (Val.choice a w) by simp) (by simp at hk; omega) (h alt halt)
      · rfl
    · rfl
  | _ => rfl

/-- A value of its type passes the checker's value test. -/
theorem valOkB_of {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (hv : ValIn E H vsc v sc t)
    (hmaps : ValMaps E n n sc t vsc v) (hs : sizeOf v < n) : valOkB E n sc t v vsc = true := by
  simp [valOkB, valMapsB_of v hs hmaps, valSemB_of v hv]

/-- `ValIn` from a value at every fuel from `n` on. -/
theorem ValIn.of_eventually {n : Nat} {sc vsc : Scope} {t : Ty} {v : Val}
    (h : ∀ M, n ≤ M → ∃ w, evalVal E M vsc v w ∧ (sem E H M sc [] t).all w) : ValIn E H vsc v sc t := by
  intro N
  obtain ⟨w, he, hm⟩ := h (max N n) (by omega)
  exact ⟨max N n, by omega, max N n, le_refl _, [], w, he, hm⟩

end Walk

end Asn1.X680
