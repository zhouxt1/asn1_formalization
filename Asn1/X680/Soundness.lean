import Asn1.X680.SoundParams

/-!
# The checker rejects only what the spec rejects

`checkEnv_sound`: when `Env.Valid E H` holds, then at every large enough fuel `checkEnv E n` reports
only rules about the notation (`Rule.status = .notation`), which `Valid` does not state. So a rule
of `Valid` that the checker reports broken, at enough fuel, is broken. With too little fuel a
reference may not resolve, and the checker then rejects what is valid; that is why the theorem
holds from some fuel on.

The proof follows `checkEnv`'s parts. For each, a lemma says that when the module is valid at fuel
`n`, the part reports nothing (or only notation rules).
-/

namespace Asn1.X680

/-- A violation of a rule about the notation, which `Valid` does not state. -/
def Violation.IsNotation (v : Violation) : Prop := v.rule.status = .notation

/-! ## Where the checker looks -/

/-- What `occurrences` lists occurs in the type (`Occurs`). -/
theorem occurs_of_mem_occurrences : ∀ {t s : Ty}, s ∈ occurrences t → Occurs t s := by
  intro t
  induction t using WellFounded.induction (measure (sizeOf : Ty → Nat)).wf with
  | _ t ih =>
  intro s hs
  have ih' : ∀ u, sizeOf u < sizeOf t → s ∈ occurrences u → Occurs u s := fun u h => ih u h
  unfold occurrences at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact .self _
  cases t with
  | sequence r e r2 =>
    simp only [List.mem_flatMap, List.mem_attach, true_and] at hs
    obtain ⟨⟨c, hc⟩, hs⟩ := hs
    have := Comp.sizeOf_lt hc
    cases c with
    | mk nm u p => exact .seqComp hc (ih' u (by simp at this ⊢; omega) hs)
    | componentsOf u => exact .seqCompsOf hc (ih' u (by simp at this ⊢; omega) hs)
  | set r e r2 =>
    simp only [List.mem_flatMap, List.mem_attach, true_and] at hs
    obtain ⟨⟨c, hc⟩, hs⟩ := hs
    have := Comp.sizeOf_lt hc
    cases c with
    | mk nm u p => exact .setComp hc (ih' u (by simp at this ⊢; omega) hs)
    | componentsOf u => exact .setCompsOf hc (ih' u (by simp at this ⊢; omega) hs)
  | sequenceOf u => exact .seqOf (ih' u (by simp) hs)
  | setOf u => exact .setOf (ih' u (by simp) hs)
  | selection nm u => exact .selection (ih' u (by simp) hs)
  | tagged tg k u => exact .tagged (ih' u (by simp) hs)
  | constrained u c =>
    simp only [List.mem_append, List.mem_flatMap, List.mem_attach, true_and] at hs
    rcases hs with hs | ⟨⟨w, hw⟩, hs⟩
    · exact .constrained (ih' u (by simp; omega) hs)
    · exact .inConstraint hw (ih' w (by have := consTypes_sizeOf hw; simp; omega) hs)
  | choice r e =>
    simp only [List.mem_flatMap, List.mem_attach, true_and] at hs
    obtain ⟨⟨a, ha⟩, hs⟩ := hs
    have := Alt.sizeOf_lt ha
    cases a with
    | mk nm u => exact .choiceAlt ha (ih' u (by simp at this ⊢; omega) hs)
  | paramRef mn nm args =>
    simp only [List.mem_flatMap, List.mem_attach, true_and] at hs
    obtain ⟨⟨a, ha⟩, hs⟩ := hs
    have := List.sizeOf_lt_of_mem ha
    cases a with
    | type u => exact .paramArg ha (ih' u (by simp at this ⊢; omega) hs)
    | _ => simp at hs
  | _ => simp at hs

-- the object listings `moduleTypes` uses list what `ObjHas`, `ObjSetHas`, `OElemsHas` say
mutual
  theorem objHas_of_mem : ∀ {o : Obj} {t : Ty}, t ∈ objTypes o → ObjHas o t
    | .defn ss, t, h => by
      unfold objTypes at h
      simp only [List.mem_flatMap, List.mem_attach, true_and] at h
      obtain ⟨⟨⟨f, st⟩, hm⟩, h⟩ := h
      cases st with
      | type u => simp at h; subst h; exact .type hm
      | object o => exact .object hm (objHas_of_mem h)
      | objectSet os => exact .objectSet hm (objSetHas_of_mem h)
      | _ => simp at h
    | .ref .., t, h | .fromObject .., t, h | .raw _, t, h => by unfold objTypes at h; simp at h
  termination_by o => sizeOf o
  decreasing_by all_goals (have := List.sizeOf_lt_of_mem hm; simp_all; omega)

  theorem objSetHas_of_mem : ∀ {os : ObjSet} {t : Ty}, t ∈ objSetTypes os → ObjSetHas os t
    | .spec (some r) x (some a), t, h => by
      unfold objSetTypes at h; simp only [List.mem_append] at h
      rcases h with h | h
      · exact .root (oelemsHas_of_mem h)
      · exact .addition (oelemsHas_of_mem h)
    | .spec (some r) x none, t, h => by unfold objSetTypes at h; exact .root (oelemsHas_of_mem h)
    | .spec none x (some a), t, h => by unfold objSetTypes at h; exact .addition (oelemsHas_of_mem h)
    | .spec none x none, t, h => by unfold objSetTypes at h; simp at h
    | .ref .., t, h => by unfold objSetTypes at h; simp at h
  termination_by os => sizeOf os

  theorem oelemsHas_of_mem : ∀ {e : OElems} {t : Ty}, t ∈ oelemsTypes e → OElemsHas e t
    | .obj o, t, h => by unfold oelemsTypes at h; exact .obj (objHas_of_mem h)
    | .set s, t, h => by unfold oelemsTypes at h; exact .set (objSetHas_of_mem h)
    | .union a b, t, h => by
      unfold oelemsTypes at h; simp only [List.mem_append] at h
      rcases h with h | h
      · exact .unionL (oelemsHas_of_mem h)
      · exact .unionR (oelemsHas_of_mem h)
    | .inter a b, t, h => by
      unfold oelemsTypes at h; simp only [List.mem_append] at h
      rcases h with h | h
      · exact .interL (oelemsHas_of_mem h)
      · exact .interR (oelemsHas_of_mem h)
    | .except a b, t, h => by
      unfold oelemsTypes at h; simp only [List.mem_append] at h
      rcases h with h | h
      · exact .exceptL (oelemsHas_of_mem h)
      · exact .exceptR (oelemsHas_of_mem h)
    | .fromObjects .., t, h => by unfold oelemsTypes at h; simp at h
  termination_by e => sizeOf e
end

theorem mem_moduleTypes {m : Module} {nm : String} {sc : Scope} {t : Ty}
    (h : (nm, sc, t) ∈ moduleTypes m) :
    (sc = .ofModule m ∧ m.Site nm t) ∨
      ∃ pa ∈ m.params, nm = pa.name ∧ sc = Scope.withDummies m pa.paramList ∧ pa.Has t := by
  simp only [moduleTypes, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · obtain ⟨⟨nm', t'⟩, hm, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl ⟨rfl, .type hm⟩
  · obtain ⟨⟨nm', t', v⟩, hm, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl ⟨rfl, .valueGov hm⟩
  · obtain ⟨⟨nm', c⟩, hm, u, hu, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl ⟨rfl, .classDef hm hu⟩
  · obtain ⟨⟨nm', cls, o⟩, hm, u, hu, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl ⟨rfl, .object hm (objHas_of_mem hu)⟩
  · obtain ⟨⟨nm', cls, os⟩, hm, u, hu, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl ⟨rfl, .objectSet hm (objSetHas_of_mem hu)⟩
  · obtain ⟨pa, hpa, u, hu, he⟩ := h; simp at he; obtain ⟨rfl, rfl, rfl⟩ := he
    refine .inr ⟨pa, hpa, rfl, rfl, ?_⟩
    cases pa with
    | type _ _ b => simp at hu; exact hu
    | value _ _ b _ => simp at hu; exact hu
    | valueSet _ _ b c => simp at hu; exact hu
    | cls _ _ c => exact hu
    | obj _ _ _ o => exact objHas_of_mem hu
    | objSet _ _ _ os => exact objSetHas_of_mem hu

/-! ## Sizes: the fuel the spec needs

`entries` spends a unit of fuel on each component, so the spec sees all of a type only at fuel
above its size. These bound the types of a module by the module. -/

theorem Occurs.sizeOf_le {t s : Ty} (h : Occurs t s) : sizeOf s ≤ sizeOf t := by
  induction h with
  | self => exact Nat.le_refl _
  | seqComp hc _ ih | setComp hc _ ih => have := Comp.sizeOf_lt hc; simp at this ⊢; omega
  | seqCompsOf hc _ ih | setCompsOf hc _ ih => have := Comp.sizeOf_lt hc; simp at this ⊢; omega
  | seqOf _ ih | setOf _ ih => simp; omega
  | choiceAlt ha _ ih => have := Alt.sizeOf_lt ha; simp at this ⊢; omega
  | selection _ ih | tagged _ ih => simp; omega
  | constrained _ ih => simp; omega
  | inConstraint hu _ ih => have := consTypes_sizeOf hu; simp; omega
  | paramArg ha _ ih => have := List.sizeOf_lt_of_mem ha; simp at this ⊢; omega

mutual
  theorem ObjHas.sizeOf_lt : ∀ {o : Obj} {t : Ty}, ObjHas o t → sizeOf t < sizeOf o
    | _, _, .type hm => by have := List.sizeOf_lt_of_mem hm; simp at this ⊢; omega
    | _, _, .object hm h => by have := List.sizeOf_lt_of_mem hm; have := ObjHas.sizeOf_lt h; simp at *; omega
    | _, _, .objectSet hm h => by have := List.sizeOf_lt_of_mem hm; have := ObjSetHas.sizeOf_lt h; simp at *; omega
  theorem ObjSetHas.sizeOf_lt : ∀ {os : ObjSet} {t : Ty}, ObjSetHas os t → sizeOf t < sizeOf os
    | _, _, .root h => by have := OElemsHas.sizeOf_lt h; simp; omega
    | _, _, .addition h => by have := OElemsHas.sizeOf_lt h; simp; omega
  theorem OElemsHas.sizeOf_lt : ∀ {e : OElems} {t : Ty}, OElemsHas e t → sizeOf t < sizeOf e
    | _, _, .obj h => by have := ObjHas.sizeOf_lt h; simp; omega
    | _, _, .set h => by have := ObjSetHas.sizeOf_lt h; simp; omega
    | _, _, .unionL h | _, _, .interL h | _, _, .exceptL h => by have := OElemsHas.sizeOf_lt h; simp; omega
    | _, _, .unionR h | _, _, .interR h | _, _, .exceptR h => by have := OElemsHas.sizeOf_lt h; simp; omega
end

theorem classTypes_sizeOf {c : ClassRef} {t : Ty} (h : t ∈ classTypes c) : sizeOf t < sizeOf c := by
  cases c with
  | defn fs syn =>
    simp only [classTypes, List.mem_flatMap] at h
    obtain ⟨f, hf, ht⟩ := h
    have := List.sizeOf_lt_of_mem hf
    cases f with
    | fixedValue _ u _ _ => simp at ht; subst ht; simp at this ⊢; omega
    | fixedValueSet _ u _ => simp at ht; subst ht; simp at this ⊢; omega
    | typeField _ o =>
      rcases o with _ | _ | u
      · simp at ht
      · simp at ht
      · simp at ht; subst ht; simp at this ⊢; omega
    | _ => simp at ht
  | _ => simp [classTypes] at h

theorem Module.Site.sizeOf_lt {m : Module} {nm : String} {t : Ty} (h : m.Site nm t) :
    sizeOf t < sizeOf m := by
  cases m
  cases h with
  | type hm => have := List.sizeOf_lt_of_mem hm; simp at this ⊢; omega
  | valueGov hm => have := List.sizeOf_lt_of_mem hm; simp at this ⊢; omega
  | classDef hm hc => have := List.sizeOf_lt_of_mem hm; have := classTypes_sizeOf hc; simp at *; omega
  | object hm ho => have := List.sizeOf_lt_of_mem hm; have := ObjHas.sizeOf_lt ho; simp at *; omega
  | objectSet hm ho => have := List.sizeOf_lt_of_mem hm; have := ObjSetHas.sizeOf_lt ho; simp at *; omega

theorem ParamAssign.Has.sizeOf_lt {pa : ParamAssign} {t : Ty} (h : pa.Has t) :
    sizeOf t ≤ sizeOf pa + 1 := by
  cases pa with
  | type _ _ b => simp [ParamAssign.Has] at h; subst h; simp; omega
  | value _ _ b _ => simp [ParamAssign.Has] at h; subst h; simp; omega
  | valueSet _ _ b c => simp [ParamAssign.Has] at h; subst h; simp; omega
  | cls _ _ c => have := classTypes_sizeOf h; simp; omega
  | obj _ _ _ o => have := ObjHas.sizeOf_lt h; simp; omega
  | objSet _ _ _ os => have := ObjSetHas.sizeOf_lt h; simp; omega

theorem sizeOf_param_lt {m : Module} {pa : ParamAssign} (h : pa ∈ m.params) : sizeOf pa < sizeOf m := by
  cases m; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega

/-! ## Each part of `checkEnv` -/

-- what a reference that resolves says about the module
theorem Env.resolveWith_some {α : Type} {E : Env} {get : Module → Option α} {name : String} {n : Nat}
    {m : Module} {r} (h : E.resolveWith get name n m = some r) :
    (get m).isSome ∨ m.imports.any (·.1 == name) := by
  cases n with
  | zero => simp [Env.resolveWith] at h
  | succ n =>
    unfold Env.resolveWith at h
    split at h
    next a heq _ => simp [heq]
    next mn hg himp =>
      right
      have : mn ∈ ((m.imports.filter (·.1 == name)).map (·.2)).eraseDups := by rw [himp]; simp
      have := List.mem_eraseDups.mp this
      simp only [List.mem_map, List.mem_filter] at this
      obtain ⟨p, ⟨hp, hpn⟩, -⟩ := this
      exact List.any_eq_true.mpr ⟨p, hp, hpn⟩
    next => simp at h

theorem knows_of_resolveVal {E : Env} {n : Nat} {m : Module} {mn : Option String} {v : String}
    (h : (resolveVal E n (.ofModule m) mn v []).isSome) : (Scope.ofModule m).knows mn v = true := by
  cases mn with
  | some _ => rfl
  | none =>
    simp only [resolveVal, resolveIn, Scope.ofModule, Scope.bound, Scope.binds, Scope.mod,
      List.find?_nil, Option.map_none, Option.isSome_map] at h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    simp only [Scope.knows, Scope.ofModule, Scope.mod, Scope.bound, Scope.binds, List.find?_nil,
      Option.map_none, Option.isSome_none, Bool.false_or, Bool.or_eq_true]
    rcases Env.resolveWith_some hr with hg | hi
    · left
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hg
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hx
      have hm := List.mem_of_find?_eq_some hy
      have hn : y.1 = v := by simpa using List.find?_some hy
      have : v ∈ m.values.map (·.1) := List.mem_map.mpr ⟨y, hm, hn⟩
      simp only [Module.assignedNames, List.elem_eq_mem, decide_eq_true_eq, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inr this))))
    · right; exact hi

theorem importsOkB_nil {E : Env} {m : Module} (h : ImportsOk E m) : importsOkB E m = [] := by
  simp only [importsOkB, List.filterMap_eq_nil_iff]
  rintro ⟨sym, mn⟩ hmem
  obtain ⟨m', hf, hs⟩ := h sym mn hmem
  simp only [hf]
  rcases hs with hs | hs <;> simp_all

theorem exportsOkB_nil {m : Module} (h : ExportsOk m) : exportsOkB m = [] := by
  simp only [exportsOkB, List.filter_eq_nil_iff]
  intro sym hs
  rcases h sym hs with h | h <;> simp_all

theorem moduleChecks_sound {E : Env} {H : ContentsHook} {n : Nat} {m : Module}
    (hV : m.ValidAt E H n) : ∀ v ∈ moduleChecks E m, v.IsNotation := by
  intro v hv
  simp only [moduleChecks, List.mem_append, List.mem_map, List.mem_filterMap] at hv
  rcases hv with (((((((hv | hv) | hv) | hv) | hv) | hv) | hv) | hv)
  · simp [hV.importsOnce] at hv
  · obtain ⟨_, _, rfl⟩ := hv; rfl
  · obtain ⟨pa, hpa, hv⟩ := hv
    have hb := hV.paramBodies pa hpa
    split at hv
    · rename_i nm ps r
      split at hv
      · rename_i hany
        simp only [ParamAssign.NotOnlyDummy] at hb
        exfalso; apply hb
        obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hany
        exact List.mem_map.mpr ⟨p, hp, by simpa using hpe⟩
      · simp at hv
    · simp at hv
  · obtain ⟨_, _, hv⟩ := hv; split at hv <;> simp_all; subst hv; rfl
  · obtain ⟨⟨mn, w⟩, hmem, hv⟩ := hv
    split at hv
    · simp at hv
    · rename_i hno
      exfalso; apply hno
      rcases hV.exceptionRefs mn w hmem with h | ⟨pa, hpa, p, hp, hpe⟩
      · simp [knows_of_resolveVal h]
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact .inr ⟨pa, hpa, p, hp, by simp [hpe]⟩
  · simp [show decide m.assignedNames.Nodup = true from decide_eq_true hV.assignedOnce] at hv
  · obtain ⟨_, h, _⟩ := hv; simp [importsOkB_nil hV.imports] at h
  · obtain ⟨_, h, _⟩ := hv; simp [exportsOkB_nil hV.exports] at h

/-! ### Values that evaluate have their references resolved -/

section Refs

variable {E : Env} {H : ContentsHook}

theorem forall₂_left {α β} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | [], [], _, a, ha => by simp at ha
  | x :: xs, y :: ys, .cons hxy hr, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, hxy⟩
    · exact forall₂_left hr a ha

/-- A value that evaluates at fuel `k` has every reference in it resolved at fuel `k`. -/
theorem evalVal_refs : ∀ {k : Nat} {sc : Scope} {v w : Val}, evalVal E k sc v w →
    ∀ r ∈ valRefs v, (resolveVal E k sc r.1 r.2.1 r.2.2).isSome
  | 0, _, _, _, h => by simp [evalVal] at h
  | k + 1, sc, v, w, h => by
    intro r hr
    cases v with
    | ref mn name args =>
      unfold valRefs at hr; simp at hr; subst hr
      unfold evalVal at h
      split at h
      · rename_i x hx; simp [resolveVal_mono hx (Nat.le_succ k)]
      · exact h.elim
    | seq cs =>
      unfold evalVal at h; obtain ⟨ds, rfl, hf⟩ := h
      unfold valRefs at hr
      simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
      obtain ⟨⟨⟨f, v'⟩, hm⟩, hr⟩ := hr
      obtain ⟨d, -, hd⟩ := forall₂_left hf _ hm
      have := evalVal_refs hd r hr
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
      simp [resolveVal_mono hx (Nat.le_succ k)]
    | seqOf vs =>
      unfold evalVal at h; obtain ⟨ws, rfl, hf⟩ := h
      unfold valRefs at hr
      simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
      obtain ⟨⟨v', hm⟩, hr⟩ := hr
      obtain ⟨d, hd⟩ := forall₂_left hf _ hm
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalVal_refs hd r hr)
      simp [resolveVal_mono hx (Nat.le_succ k)]
    | setOf vs =>
      unfold evalVal at h; obtain ⟨ws, rfl, hf⟩ := h
      unfold valRefs at hr
      simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
      obtain ⟨⟨v', hm⟩, hr⟩ := hr
      obtain ⟨d, hd⟩ := forall₂_left hf _ hm
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalVal_refs hd r hr)
      simp [resolveVal_mono hx (Nat.le_succ k)]
    | choice a v' =>
      unfold evalVal at h; obtain ⟨y, rfl, hy⟩ := h
      unfold valRefs at hr
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalVal_refs hy r hr)
      simp [resolveVal_mono hx (Nat.le_succ k)]
    | _ => unfold valRefs at hr; simp at hr

theorem valRefsOkB_of_eval {n k : Nat} {sc : Scope} {v w : Val} (h : evalVal E k sc v w) (hk : k ≤ n) :
    valRefsOkB E n sc v = true := by
  simp only [valRefsOkB, List.all_eq_true]
  rintro ⟨mn, nm, args⟩ hr
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalVal_refs h _ hr)
  simp [resolveVal_mono hx hk]

/-- A value written in a constraint is evaluated by `ConsOk`, at no more fuel than it has. -/
abbrev EvalsBelow (E : Env) (k : Nat) (sc : Scope) (v : Val) : Prop := ∃ k' ≤ k, ∃ w, evalVal E k' sc v w

theorem EvalsBelow.mono {k k' sc v} (h : EvalsBelow E k sc v) (hk : k ≤ k') : EvalsBelow E k' sc v := by
  obtain ⟨j, hj, w, hw⟩ := h; exact ⟨j, by omega, w, hw⟩

mutual
  theorem consOk_vals : ∀ {k : Nat} {sc : Scope} {pt : Ty} {inPA : Bool} {c : Constraint},
      ConsOk E H k sc pt inPA c → ∀ v ∈ consVals c, EvalsBelow E k sc v
    | 0, _, _, _, _, h => by simp [ConsOk] at h
    | k + 1, sc, pt, inPA, .mk root x (some a), h => by
      intro v hv
      simp only [ConsOk] at h
      simp only [consVals, List.mem_append] at hv
      rcases hv with hv | hv
      · exact (esOk_vals h.1 v hv).mono (Nat.le_succ k)
      · exact (esOk_vals (h.2 a rfl) v hv).mono (Nat.le_succ k)
    | k + 1, sc, pt, inPA, .mk root x none, h => by
      intro v hv
      simp only [ConsOk] at h
      simp only [consVals] at hv
      exact (esOk_vals h.1 v hv).mono (Nat.le_succ k)
    | k + 1, _, _, _, .table .., _ | k + 1, _, _, _, .contents .., _ | k + 1, _, _, _, .userDefined, _ => by
      intro v hv; simp [consVals] at hv
  theorem esOk_vals : ∀ {k : Nat} {sc : Scope} {pt : Ty} {inPA : Bool} {s : ElemSet},
      ESetOk E H k sc pt inPA s → ∀ v ∈ esVals s, EvalsBelow E k sc v
    | 0, _, _, _, _, h => by simp [ESetOk] at h
    | k + 1, sc, pt, inPA, .elem el, h => by
      intro v hv; simp only [ESetOk] at h; simp only [esVals] at hv
      exact (elOk_vals h v hv).mono (Nat.le_succ k)
    | k + 1, sc, pt, inPA, .union a b, h | k + 1, sc, pt, inPA, .inter a b, h
    | k + 1, sc, pt, inPA, .except a b, h => by
      intro v hv; simp only [ESetOk] at h; simp only [esVals, List.mem_append] at hv
      rcases hv with hv | hv
      · exact (esOk_vals h.1 v hv).mono (Nat.le_succ k)
      · exact (esOk_vals h.2 v hv).mono (Nat.le_succ k)
    | k + 1, sc, pt, inPA, .allExcept b, h => by
      intro v hv; simp only [ESetOk] at h; simp only [esVals] at hv
      exact (esOk_vals h v hv).mono (Nat.le_succ k)
  theorem elOk_vals : ∀ {k : Nat} {sc : Scope} {pt : Ty} {inPA : Bool} {el : Elem},
      ElemOk E H k sc pt inPA el → ∀ v ∈ elVals el, EvalsBelow E k sc v
    | 0, _, _, _, _, h => by simp [ElemOk] at h
    | k + 1, sc, pt, inPA, el, h => by
      intro v hv
      simp only [ElemOk] at h
      obtain ⟨sc', bt, r, -, -, -, -, hm⟩ := h
      cases el with
      | single v' =>
        simp only [elVals, List.mem_singleton] at hv; subst hv
        obtain ⟨⟨w, hw, -⟩, -⟩ := hm
        exact ⟨k, Nat.le_succ k, w, hw⟩
      | range lo lo' hi hi' =>
        obtain ⟨l, h', hl, hh, -⟩ := hm
        simp only [elVals, List.mem_append] at hv
        rcases hv with hv | hv
        · cases lo with
          | val x =>
            simp [boundVals] at hv; subst hv
            cases k with
            | zero => simp [EvalBound] at hl
            | succ j => obtain ⟨w, hw, -⟩ := hl; exact ⟨j, by omega, w, hw⟩
          | _ => simp [boundVals] at hv
        · cases hi with
          | val x =>
            simp [boundVals] at hv; subst hv
            cases k with
            | zero => simp [EvalBound] at hh
            | succ j => obtain ⟨w, hw, -⟩ := hh; exact ⟨j, by omega, w, hw⟩
          | _ => simp [boundVals] at hv
      | size c =>
        simp only [elVals] at hv
        exact (consOk_vals hm.2 v hv).mono (Nat.le_succ k)
      | from_ c =>
        simp only [elVals] at hv
        exact (consOk_vals hm.2 v hv).mono (Nat.le_succ k)
      | _ => simp [elVals] at hv
end

theorem List.length_le_sizeOf' {α} [SizeOf α] : ∀ (l : List α), l.length ≤ sizeOf l
  | [] => by simp
  | _ :: l => by have := List.length_le_sizeOf' l; simp; omega

theorem mem_expand {sc : Scope} {nm : String} {t : Ty} {p : Presence} :
    ∀ {k : Nat} {cs : List Comp}, Comp.mk nm t p ∈ cs → cs.length < k → (sc, nm, t, p) ∈ expand E k sc cs
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, [], h, _ => by simp at h
  | k + 1, c :: cs, h, hk => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp [expand]
    · have hk' : cs.length < k := by simpa using hk
      cases c with
      | mk => simp only [expand, List.mem_cons]; exact .inr (mem_expand h' hk')
      | componentsOf u =>
        simp only [expand, List.mem_append]; exact .inr (mem_expand h' hk')

theorem ExtAdd.length_comps_lt (a : ExtAdd) : a.comps.length < sizeOf a := by
  cases a with
  | one c => cases c <;> simp [ExtAdd.comps] <;> omega
  | group v cs => have := List.length_le_sizeOf' cs; simp [ExtAdd.comps]; omega

/-- A component written in a SEQUENCE or SET is an entry, in the scope it is written in, when the
fuel is above the type's size. -/
theorem mem_entries {n : Nat} {sc : Scope} {r r2 : List Comp} {e : Option (List ExtAdd)} {nm : String}
    {t : Ty} {p : Presence} (h : Comp.mk nm t p ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2)
    (hn : 1 + sizeOf r + sizeOf e + sizeOf r2 < n) :
    ∃ en ∈ entries E n sc r e r2, en.scope = sc ∧ en.name = nm ∧ en.ty = t ∧ en.presence = p := by
  have h1 := List.length_le_sizeOf' r; have h2 := List.length_le_sizeOf' r2
  simp only [List.mem_append] at h
  simp only [entries, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases h with (h | h) | h
  · exact ⟨_, .inl (.inl ⟨_, mem_expand h (by omega), rfl⟩), rfl, rfl, rfl, rfl⟩
  · cases e with
    | none => simp at h
    | some es =>
      simp only [Option.getD_some, List.mem_flatMap] at h
      obtain ⟨a, ha, hc⟩ := h
      obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp ha
      have ha' : (a, i) ∈ es.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?]; simp [← hi.2]
      have h3 := List.sizeOf_lt_of_mem ha; have h4 := ExtAdd.length_comps_lt a
      simp at hn
      exact ⟨_, .inl (.inr ⟨(a, i), ha', _, mem_expand hc (show a.comps.length < n by omega), rfl⟩), rfl, rfl, rfl, rfl⟩
  · exact ⟨_, .inr ⟨_, mem_expand h (by omega), rfl⟩, rfl, rfl, rfl, rfl⟩

theorem valRef_of_mem : ∀ {v : Val} {r}, r ∈ valRefs v → ValRef v r := by
  intro v
  induction v using WellFounded.induction (measure (sizeOf : Val → Nat)).wf with
  | _ v ih =>
  intro r hr
  have ih' : ∀ u, sizeOf u < sizeOf v → ∀ {r}, r ∈ valRefs u → ValRef u r := fun u h => ih u h
  cases v with
  | ref mn nm args => unfold valRefs at hr; simp at hr; subst hr; exact .ref
  | seq cs =>
    unfold valRefs at hr; simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
    obtain ⟨⟨⟨f, w⟩, hm⟩, hr⟩ := hr
    have := List.sizeOf_lt_of_mem hm
    exact .seq hm (ih' w (by simp at this ⊢; omega) hr)
  | seqOf vs =>
    unfold valRefs at hr; simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
    obtain ⟨⟨w, hm⟩, hr⟩ := hr
    have := List.sizeOf_lt_of_mem hm
    exact .seqOf hm (ih' w (by simp; omega) hr)
  | setOf vs =>
    unfold valRefs at hr; simp only [List.mem_flatMap, List.mem_attach, true_and] at hr
    obtain ⟨⟨w, hm⟩, hr⟩ := hr
    have := List.sizeOf_lt_of_mem hm
    exact .setOf hm (ih' w (by simp; omega) hr)
  | choice a w => unfold valRefs at hr; exact .choice (ih' w (by simp) hr)
  | _ => unfold valRefs at hr; simp at hr

theorem valRefsOkB_of_ok {n : Nat} {sc : Scope} {v : Val} (h : ValRefsOk E n sc v) : valRefsOkB E n sc v = true := by
  simp only [valRefsOkB, List.all_eq_true]
  rintro ⟨mn, nm, args⟩ hr
  rcases h mn nm args (valRef_of_mem hr) with ⟨rfl, rfl, hb⟩ | hres <;> simp_all

end Refs

/-! ### The rules on one type

For each rule of `typeChecks`, the spec's rule makes the check pass, in the same scope. -/

theorem tagsDistinctB_go_of : ∀ {ts : List CTag}, ts.Pairwise (fun a b => a.clash b = false) →
    tagsDistinctB.go ts = true
  | [], _ => rfl
  | t :: rest, h => by
    rw [List.pairwise_cons] at h
    simp only [tagsDistinctB.go, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
    exact ⟨h.1, tagsDistinctB_go_of h.2⟩

theorem tagsDistinctB_of {ts : List CTag} (h : TagsDistinct ts) : tagsDistinctB ts = true :=
  tagsDistinctB_go_of h

theorem runsDistinctB_go {series : List (List CTag × Bool)} (h : RunsDistinct series) (i : Nat) :
    ∀ (fuel j : Nat), i < j → (∀ k, i ≤ k → k < j → ∃ x : List CTag × Bool, series[k]? = some x ∧ x.2 = true) →
    runsDistinctB.go series.toArray i j fuel = true
  | 0, _, _, _ => by simp [runsDistinctB.go]
  | k + 1, j, hij, hrun => by
    unfold runsDistinctB.go
    split
    · rfl
    · rename_i hj
      simp only [List.size_toArray, not_le] at hj
      have hi : i < series.length := by omega
      have hxi : series.toArray[i]! = series[i] := by simp [hi]
      have hxj : series.toArray[j]! = series[j] := by simp [hj]
      rw [hxi, hxj]
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      refine ⟨fun t ht u hu => h i j hij hrun _ _ (by simp [hi]) (by simp [hj]) t ht u hu, ?_⟩
      split
      · rename_i hb
        apply runsDistinctB_go h i k (j + 1) (by omega)
        intro k' h1 h2
        by_cases hk : k' < j
        · exact hrun k' h1 hk
        · obtain rfl : k' = j := by omega
          exact ⟨_, by simp [hj], hb⟩
      · rfl

theorem runsDistinctB_of {series : List (List CTag × Bool)} (h : RunsDistinct series) :
    runsDistinctB series = true := by
  simp only [runsDistinctB, List.all_eq_true, List.mem_range, List.size_toArray]
  intro i hi
  have hxi : series.toArray[i]! = series[i] := by simp [hi]
  rw [hxi]
  split
  · rename_i hb
    apply runsDistinctB_go h i _ (i + 1) (by omega)
    intro k h1 h2
    obtain rfl : k = i := by omega
    exact ⟨_, by simp [hi], hb⟩
  · rfl

/-- An element of the run `takeWhile p ++ (dropWhile p).take 1` comes after elements that all
satisfy `p`. -/
theorem mem_firstRun {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l.takeWhile p ++ (l.dropWhile p).take 1 →
    ∃ k : Nat, l[k]? = some x ∧ ∀ (k' : Nat) y, k' < k → l[k']? = some y → p y = true
  | [], x, h => by simp at h
  | y :: l, x, h => by
    by_cases hy : p y = true
    · simp only [List.takeWhile_cons, hy, ↓reduceIte, List.dropWhile_cons, List.cons_append,
        List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, rfl, fun k' _ h _ => absurd h (by omega)⟩
      · obtain ⟨k, hk, hp⟩ := mem_firstRun h
        refine ⟨k + 1, by simpa using hk, fun k' z hk' hz => ?_⟩
        cases k' with
        | zero => simp at hz; subst hz; exact hy
        | succ k' => exact hp k' z (by omega) (by simpa using hz)
    · simp only [List.takeWhile_cons, hy, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte,
        List.nil_append, List.take_succ_cons, List.take_zero, List.mem_singleton] at h
      subst h
      exact ⟨0, rfl, fun k' _ h _ => absurd h (by omega)⟩

/-! ## Tags, read in a scope that knows less -/

section TagsLess

variable {E : Env}

theorem ect_sublist {n N : Nat} {auto : Bool} {x : Entry × Option (Option (List Tag))}
    {y : Entry × Option (List Tag)} (hsc : ScLess x.1.scope y.1.scope) (hty : x.1.ty = y.1.ty)
    (hN : n ≤ N) (hxy : ∀ o, x.2 = some o → o = y.2) :
    (match x.2 with
      | some o => ctags o ++ if (!auto && carriesConceptual E n x.1.scope x.1.ty) = true then [CTag.conceptual] else []
      | none => []).Sublist
    (ctags y.2 ++ if (!auto && carriesConceptual E N y.1.scope y.1.ty) = true then [CTag.conceptual] else []) := by
  cases hx : x.2 with
  | none => exact List.nil_sublist _
  | some o =>
    rw [hxy o hx]
    apply List.Sublist.append (List.Sublist.refl _)
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp [hc.1, ← hty, carriesConceptual_less hsc hN hc.2]
    · exact List.nil_sublist _

theorem alt_sublist {n N : Nat} {auto : Bool} {s1 s2 : Scope} {x : Alt × Option (Option (List Tag))}
    {y : Alt × Option (List Tag)} (hsc : ScLess s1 s2) (hty : x.1 = y.1)
    (hN : n ≤ N) (hxy : ∀ o, x.2 = some o → o = y.2) :
    (match x.2 with
      | some o => ctags o ++ if (!auto && carriesConceptual E n s1 x.1.ty) = true then [CTag.conceptual] else []
      | none => []).Sublist
    (ctags y.2 ++ if (!auto && carriesConceptual E N s2 y.1.ty) = true then [CTag.conceptual] else []) := by
  cases hx : x.2 with
  | none => exact List.nil_sublist _
  | some o =>
    rw [hxy o hx]
    apply List.Sublist.append (List.Sublist.refl _)
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp [hc.1, ← hty, carriesConceptual_less hsc hN hc.2]
    · exact List.nil_sublist _

theorem entLess_additions : ∀ {l1 l2 : List Entry}, List.Forall₂ EntLess l1 l2 →
    l1.map (·.addition.isSome) = l2.map (·.addition.isSome)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hr => by simp [h.2.2.2.2.1, entLess_additions hr]

theorem entryTags_rel {n N : Nat} {sc1 sc2 : Scope} {r r2 : List Comp} {e : Option (List ExtAdd)}
    (hsc : ScLess sc1 sc2) (hN : n ≤ N) (hk : entriesKnown E n sc1 r e r2 = true) :
    List.Forall₂ (fun x1 x2 => EntLess x1.1 x2.1 ∧ ∀ o, x1.2 = some o → o = x2.2)
      (entryTagsB E n sc1 r e r2) (entryTags E N sc2 r e r2) := by
  have hk2 := entriesKnown_less hsc hk
  have hst : entries E N sc2 r e r2 = entries E n sc2 r e r2 := entries_stable hk2 hN
  have hes := (entries_less (E := E) (n := n) (r := r) (e := e) (r2 := r2) hsc).2 hk
  unfold entryTagsB entryTags
  dsimp only
  rw [hst, ← hsc.mod]
  have hadd : (entries E n sc1 r e r2).map (·.addition.isSome) = (entries E n sc2 r e r2).map (·.addition.isSome) :=
    entLess_additions hes
  split
  · rw [hadd]
    refine forall₂_map (R := fun a b => EntLess a.1 b.1 ∧ a.2 = b.2) ?_ (forall₂_zip _ hes)
    rintro ⟨a, k⟩ ⟨b, k'⟩ ⟨hab, rfl⟩
    exact ⟨hab, by simp⟩
  · refine forall₂_map ?_ hes
    intro a b hab
    refine ⟨hab, fun o ho => ?_⟩
    rw [hab.2.2.1] at ho
    exact (tagsOfB_less hab.1 hN ho).symm


theorem runs_transfer {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β} (h : List.Forall₂ R l1 l2)
    {f : α → List CTag × Bool} {g : β → List CTag × Bool}
    (hfg : ∀ x y, R x y → (f x).1.Sublist (g y).1 ∧ (f x).2 = (g y).2)
    (hd : RunsDistinct (l2.map g)) : RunsDistinct (l1.map f) :=
  RunsDistinct.of_sublist (forall₂_map (fun x y hxy => hfg x y hxy) h) hd

theorem forall₂_refl {α} {R : α → α → Prop} (hr : ∀ x, R x x) : ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | x :: xs => .cons (hr x) (forall₂_refl hr xs)

theorem tagsOkB_seq_less {H : ContentsHook} {n N : Nat} {sc1 sc2 : Scope} {r r2 : List Comp}
    {e : Option (List ExtAdd)} (hsc : ScLess sc1 sc2) (hN : n ≤ N)
    (h : TagsOk E H N sc2 (.sequence r e r2)) : tagsOkB E n sc1 (.sequence r e r2) = true := by
  unfold TagsOk at h
  dsimp only at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold tagsOkB
  dsimp only
  cases hk : entriesKnown E n sc1 r e r2 with
  | false => rfl
  | true =>
  refine (Bool.or_eq_true _ _).mpr (.inr ?_)
  have hR := entryTags_rel hsc hN hk
  rw [hsc.mod]
  -- the items relate
  have hitem : ∀ (x : Entry × Option (Option (List Tag))) (y : Entry × Option (List Tag)),
      (EntLess x.1 y.1 ∧ ∀ o, x.2 = some o → o = y.2) →
      (match x.2 with
        | some o => ctags o ++ if (!autoSeq sc2.mod.header.tagDefault r e r2 && carriesConceptual E n x.1.scope x.1.ty) = true then [CTag.conceptual] else []
        | none => []).Sublist
      (ctags y.2 ++ if (!autoSeq sc2.mod.header.tagDefault r e r2 && carriesConceptual E N y.1.scope y.1.ty) = true then [CTag.conceptual] else []) :=
    fun x y hxy => ect_sublist hxy.1.1 hxy.1.2.2.1 hN hxy.2
  have hflag : ∀ (x : Entry × Option (Option (List Tag))) (y : Entry × Option (List Tag)),
      (EntLess x.1 y.1 ∧ ∀ o, x.2 = some o → o = y.2) → x.1.presence = y.1.presence :=
    fun x y hxy => hxy.1.2.2.2.1
  -- lengths
  have hlen : (entryTagsB E n sc1 r e r2).length = (entryTags E N sc2 r e r2).length := hR.length_eq
  have hk' : entriesKnown E n sc1 [] none r2 = true := by
    simp only [entriesKnown, Bool.and_eq_true, List.all_eq_true] at hk ⊢
    refine ⟨⟨?_, by simp⟩, hk.2⟩
    cases n with
    | zero => simp [expandKnown] at hk
    | succ => simp [expandKnown]
  have hlen2 : (entries E n sc1 [] none r2).length = (entries E N sc2 [] none r2).length := by
    rw [entries_stable (entriesKnown_less hsc hk') hN]
    exact ((entries_less (E := E) (n := n) (r := []) (e := none) (r2 := r2) hsc).2 hk').length_eq
  rw [hlen, hlen2]
  refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · refine runsDistinctB_of (runs_transfer (forall₂_filter (fun x y hxy => ?_) hR) (fun x y hxy => ?_) h1)
    · simp [hxy.1.2.2.2.2.1]
    · exact ⟨hitem x y hxy, by simp [hflag x y hxy]⟩
  · refine runsDistinctB_of (RunsDistinct.of_sublist ?_ h2)
    refine forall₂_append (forall₂_append ?_ (forall₂_refl (fun x => ⟨List.Sublist.refl _, rfl⟩) _)) ?_
    · refine forall₂_map (fun x y hxy => ⟨hitem x y hxy, by simp [hflag x y hxy]⟩) ?_
      rw [show (List.drop ((entryTags E N sc2 r e r2).length - (entries E N sc2 [] none r2).length)
          (entryTagsB E n sc1 r e r2)).length = (List.drop ((entryTags E N sc2 r e r2).length -
          (entries E N sc2 [] none r2).length) (entryTags E N sc2 r e r2)).length by simp [hlen]]
      exact forall₂_take _ hR
    · exact forall₂_map (fun x y hxy => ⟨hitem x y hxy, by simp [hflag x y hxy]⟩) (forall₂_drop _ hR)
  · rw [List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro t ht
    rw [List.all_eq_true]
    intro u hu
    rw [Bool.not_eq_true']
    have hadd := forall₂_filter (p := fun x => x.1.addition.isSome) (q := fun x => x.1.addition.isSome)
      (fun x y hxy => by simp [hxy.1.2.2.2.2.1]) hR
    obtain ⟨a2, ha2, haa⟩ := forall₂_mem_left hadd a ha
    obtain ⟨k, hk1, hp⟩ := mem_firstRun hx
    have htail := forall₂_drop ((entryTags E N sc2 r e r2).length - (entries E N sc2 [] none r2).length) hR
    obtain ⟨x2, hx2, hxx⟩ := (forall₂_getElem? htail k).1 x hk1
    refine h3 a2 ha2 k x2 hx2 (fun k' y2 hk' hy2 => ?_) t ((hitem a a2 haa).subset ht) u
      ((hitem x x2 hxx).subset hu)
    obtain ⟨y1, hy1, hyy⟩ : ∃ y1, (List.drop ((entryTags E N sc2 r e r2).length -
        (entries E N sc2 [] none r2).length) (entryTagsB E n sc1 r e r2))[k']? = some y1 ∧
        (EntLess y1.1 y2.1 ∧ ∀ o, y1.2 = some o → o = y2.2) := by
      cases hy1 : (List.drop ((entryTags E N sc2 r e r2).length - (entries E N sc2 [] none r2).length)
          (entryTagsB E n sc1 r e r2))[k']? with
      | none => have := ((forall₂_getElem? htail k').2).mp hy1; rw [this] at hy2; cases hy2
      | some y1 =>
        obtain ⟨y2', hy2', hyy⟩ := (forall₂_getElem? htail k').1 y1 hy1
        rw [hy2] at hy2'; cases hy2'
        exact ⟨y1, rfl, hyy⟩
    have := hp k' y1 hk' hy1
    simpa [← hflag y1 y2 hyy] using this


theorem sublist_of_all_nil {α β} {f : α → List β} {l : List α} {Y : List β} (h : ∀ x ∈ l, f x = []) :
    (l.flatMap f).Sublist Y := by
  rw [List.flatMap_eq_nil_iff.mpr h]; exact List.nil_sublist _

theorem sublist_of_all_none {α β} {f : α → Option β} {l : List α} {Y : List β} (h : ∀ x ∈ l, f x = none) :
    (l.filterMap f).Sublist Y := by
  rw [List.filterMap_eq_nil_iff.mpr h]; exact List.nil_sublist _

theorem altTags_rel {k K : Nat} {sc1 sc2 : Scope} {r : List Alt} {e : Option (List AltAdd)}
    (hsc : ScLess sc1 sc2) (hN : k ≤ K) :
    List.Forall₂ (fun x1 x2 => x1.1 = x2.1 ∧ ∀ o, x1.2 = some o → o = x2.2)
      (altTagsB E (k + 1) sc1 r e) (altTags E (K + 1) sc2 r e) := by
  simp only [altTagsB, altTags, ← hsc.mod]
  split
  · refine forall₂_map (R := fun a b => a = b) ?_ (forall₂_refl (fun _ => rfl) _)
    rintro _ _ rfl; exact ⟨rfl, by simp⟩
  · refine forall₂_map (R := fun a b => a = b) ?_ (forall₂_refl (fun _ => rfl) _)
    rintro a _ rfl
    exact ⟨rfl, fun o ho => (tagsOfB_less hsc hN ho).symm⟩

theorem tagsOkB_of_less {H : ContentsHook} {n N : Nat} {sc1 sc2 : Scope} {s : Ty} (hsc : ScLess sc1 sc2)
    (hN : n ≤ N) (h : TagsOk E H N sc2 s) : tagsOkB E n sc1 s = true := by
  cases s with
  | sequence r e r2 => exact tagsOkB_seq_less hsc hN h
  | set r e r2 =>
    unfold TagsOk at h
    dsimp only at h
    obtain ⟨h1, h2⟩ := h
    unfold tagsOkB
    dsimp only
    cases hk : entriesKnown E n sc1 r e r2 with
    | false => rfl
    | true =>
    refine (Bool.or_eq_true _ _).mpr (.inr ?_)
    have hR := entryTags_rel hsc hN hk
    rw [hsc.mod]
    refine (Bool.and_eq_true _ _).mpr ⟨tagsDistinctB_of ?_, decide_eq_true ?_⟩
    · refine List.Pairwise.sublist (List.Sublist.append (sublist_flatMap ?_) (List.Sublist.refl _)) h1
      exact hR.imp fun x y hxy => ect_sublist hxy.1.1 hxy.1.2.2.1 hN hxy.2
    · refine List.Pairwise.sublist (sublist_filterMap ?_ (forall₂_filter ?_ hR)) h2
      · intro x y hxy t ht
        split at ht
        · rename_i hx
          rw [← hxy.2 _ hx]; simpa using ht
        · simp at ht
      · intro x y hxy; simp [hxy.1.2.2.2.2.1]
  | choice r e =>
    unfold TagsOk at h
    dsimp only at h
    obtain ⟨h1, h2⟩ := h
    unfold tagsOkB
    dsimp only
    rw [hsc.mod]
    cases n with
    | zero =>
      have hz : ∀ x ∈ altTagsB E 0 sc1 r e, x.2 = none := by
        intro x hx; simp [altTagsB] at hx; obtain ⟨a, -, rfl⟩ := hx; rfl
      refine (Bool.and_eq_true _ _).mpr ⟨tagsDistinctB_of ?_, decide_eq_true ?_⟩
      · refine List.Pairwise.sublist (List.Sublist.append (sublist_of_all_nil fun x hx => ?_)
          (List.Sublist.refl _)) h1
        rw [hz x hx]
      · refine List.Pairwise.sublist (sublist_of_all_none fun x hx => ?_) h2
        rw [hz x (List.mem_of_mem_drop hx)]
    | succ k =>
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      have hR := altTags_rel (E := E) (r := r) (e := e) hsc (by omega : k ≤ K)
      refine (Bool.and_eq_true _ _).mpr ⟨tagsDistinctB_of ?_, decide_eq_true ?_⟩
      · refine List.Pairwise.sublist (List.Sublist.append (sublist_flatMap ?_) (List.Sublist.refl _)) h1
        exact hR.imp fun x y hxy => alt_sublist hsc hxy.1 hN hxy.2
      · refine List.Pairwise.sublist (sublist_filterMap ?_ (forall₂_drop _ hR)) h2
        intro x y hxy t ht
        split at ht
        · rename_i hx
          rw [← hxy.2 _ hx]; simpa using ht
        · simp at ht
  | tagged tg k t =>
    cases k with
    | implicit =>
      simp only [TagsOk] at h
      simp only [tagsOkB]
      cases hu : untaggedChoiceOrOpen E n sc1 t with
      | false => rfl
      | true => rw [untaggedChoiceOrOpen_less hsc hN hu] at h; cases h
    | _ => simp [tagsOkB]
  | _ => simp [tagsOkB]

end TagsLess

section TypeRules

variable {E : Env} {H : ContentsHook} {n : Nat} {sc : Scope}

theorem namesOkB_of {s : Ty} (h : NamesOk E H n sc s) : namesOkB E n sc s = true := by
  cases s <;> simp_all [NamesOk, namesOkB]

theorem autoAdditionsOkB_of {s : Ty} (h : AutoAdditionsOk sc s) : autoAdditionsOkB sc s = true := by
  cases s <;> simp_all [AutoAdditionsOk, autoAdditionsOkB] <;> grind

theorem refsOkB_of {s : Ty} (h : RefsOk E H n sc s) : refsOkB E n sc s = true := by
  cases s with
  | ref name => simp_all [RefsOk, refsOkB]
  | extRef mn name => simp_all [RefsOk, refsOkB]
  | paramRef mn name args =>
    cases mn with
    | none => simp_all [RefsOk, refsOkB]
    | some mn => simp_all [RefsOk, refsOkB]
  | selection nm t =>
    simp only [RefsOk] at h
    obtain ⟨sc', r, e, hb, ha⟩ := h
    simp only [refsOkB, hb, ha]
  | _ => rfl

theorem universalTagOkB_of {s : Ty} (h : UniversalTagOk s) : universalTagOkB s = true := by
  unfold UniversalTagOk at h; unfold universalTagOkB; split <;> simp_all

mutual
  theorem oelemsRefsOkB_of : ∀ {e : OElems}, (∀ r, OElemsRef e r → r.Resolves E n sc) →
      oelemsRefsOkB E n sc e = true
    | .obj (.ref mn nm args), h => by
      have := h _ .obj; simp [ORef.Resolves] at this; simp [oelemsRefsOkB, this]
    | .obj (.defn _), _ | .obj (.fromObject ..), _ | .obj (.raw _), _ => by simp [oelemsRefsOkB]
    | .set s, h => by
      simp only [oelemsRefsOkB]; exact objSetRefsOkB_of fun r hr => h r (.set hr)
    | .fromObjects s _, h => by
      simp only [oelemsRefsOkB]; exact objSetRefsOkB_of fun r hr => h r (.fromObjects hr)
    | .union a b, h => by
      simp only [oelemsRefsOkB, Bool.and_eq_true]
      exact ⟨oelemsRefsOkB_of fun r hr => h r (.unionL hr), oelemsRefsOkB_of fun r hr => h r (.unionR hr)⟩
    | .inter a b, h => by
      simp only [oelemsRefsOkB, Bool.and_eq_true]
      exact ⟨oelemsRefsOkB_of fun r hr => h r (.interL hr), oelemsRefsOkB_of fun r hr => h r (.interR hr)⟩
    | .except a b, h => by
      simp only [oelemsRefsOkB, Bool.and_eq_true]
      exact ⟨oelemsRefsOkB_of fun r hr => h r (.exceptL hr), oelemsRefsOkB_of fun r hr => h r (.exceptR hr)⟩
  theorem objSetRefsOkB_of : ∀ {os : ObjSet}, (∀ r, ObjSetRef os r → r.Resolves E n sc) →
      oelemsRefsOkB.objSetRefsOkB E n sc os = true
    | .ref mn nm args, h => by
      have := h _ .ref; simp [ORef.Resolves] at this; simp [oelemsRefsOkB.objSetRefsOkB, this]
    | .spec (some r) _ (some a), h => by
      simp only [oelemsRefsOkB.objSetRefsOkB, Bool.and_eq_true]
      exact ⟨oelemsRefsOkB_of fun x hx => h x (.root hx), oelemsRefsOkB_of fun x hx => h x (.addition hx)⟩
    | .spec (some r) _ none, h => by
      simp only [oelemsRefsOkB.objSetRefsOkB]; exact oelemsRefsOkB_of fun x hx => h x (.root hx)
    | .spec none _ (some a), h => by
      simp only [oelemsRefsOkB.objSetRefsOkB]; exact oelemsRefsOkB_of fun x hx => h x (.addition hx)
    | .spec none _ none, _ => by simp [oelemsRefsOkB.objSetRefsOkB]
end

theorem typeFromObjectsOkB_of {s : Ty} (h : TypeFromObjectsOk E n sc s) : typeFromObjectsOkB E n sc s = true := by
  cases s <;> simp_all [TypeFromObjectsOk, typeFromObjectsOkB, objSetRefsOkB_of]

theorem tableRefsOkB_of {s : Ty} (h : TableRefsOk E n sc s) : tableRefsOkB E n sc s = true := by
  unfold TableRefsOk at h; unfold tableRefsOkB; split
  · exact objSetRefsOkB_of h
  · rfl

theorem fieldMissingB_of : ∀ {n : Nat} {cf : Scope × List FieldSpec} {path : List String},
    (fieldAt E n cf path).isSome → fieldMissingB E n cf path = false
  | 0, _, _, h => by simp [fieldAt] at h
  | _ + 1, _, [], h => by simp [fieldAt] at h
  | _ + 1, (_, fs), [f], h => by simpa [fieldAt, fieldMissingB] using h
  | n + 1, (sc, fs), f :: g :: rest, h => by
    simp only [fieldAt] at h
    simp only [fieldMissingB]
    split at h
    · rename_i nm c o hf
      rw [hf]; simp only
      cases hc : classFields E n sc c with
      | none => rfl
      | some cf => rw [hc] at h; exact fieldMissingB_of h
    · rename_i nm c o hf
      rw [hf]; simp only
      cases hc : classFields E n sc c with
      | none => rfl
      | some cf => rw [hc] at h; exact fieldMissingB_of h
    · simp at h

theorem classRefsOkB_of {s : Ty} (h : ClassRefsOk E n sc s) : classRefsOkB E n sc s = true := by
  cases s with
  | instanceOf c =>
    cases c with
    | ref mn name args => simp_all [ClassRefsOk, classRefsOkB]
    | _ => simp [classRefsOkB]
  | classField cls path =>
    simp only [ClassRefsOk] at h
    obtain ⟨cf, hcf, hf⟩ := h
    cases cls with
    | ref mn name args =>
      have : (resolveClass E n sc mn name args).isSome := by
        cases n with
        | zero => simp [classFields] at hcf
        | succ k =>
          simp only [classFields] at hcf
          split at hcf
          · rename_i x hx; simp [resolveClass_mono hx (Nat.le_succ k)]
          · simp at hcf
      simp [classRefsOkB, hcf, fieldMissingB_of hf, this]
    | _ => simp [classRefsOkB, hcf, fieldMissingB_of hf]
  | _ => rfl

theorem tableClassB_of {s : Ty} (h : TableClassOk E n sc s) : tableClassB E n sc s = true := by
  unfold TableClassOk at h; unfold tableClassB
  split
  · rename_i cls _ os _
    split
    · rename_i osc c' hos
      split
      · rename_i a b ha hb; simp [h osc c' a b hos ha hb]
      · rfl
    · rfl
  · rfl

theorem tagsOkB_of {s : Ty} (h : TagsOk E H n sc s) : tagsOkB E n sc s = true :=
  tagsOkB_of_less (ScLess.refl sc) (Nat.le_refl n) h

theorem argsOkB_of {s : Ty} (h : ArgsOk E n sc s) (hs : sizeOf s < n) : argsOkB E n sc s = true := by
  cases s with
  | paramRef mn name args =>
    simp only [ArgsOk] at h
    obtain ⟨ho, hos, hv⟩ := h
    simp only [argsOkB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun a ha => ?_, ?_⟩
    · cases a with
      | obj o => exact oelemsRefsOkB_of (ho o ha)
      | objSet os => exact objSetRefsOkB_of (hos os ha)
      | _ => rfl
    · cases mn with
      | some _ => rfl
      | none =>
        simp only
        split
        · rename_i pa hpa
          have hmem := List.mem_of_find?_eq_some hpa
          have hty := List.find?_some hpa
          cases pa with
          | type nm ps b =>
            simp at hty; subst hty
            simp only [List.all_eq_true]
            rintro ⟨a, p⟩ hap
            cases a with
            | value v =>
              rcases hg : p.governor with _ | g
              · simp [hg]
              · cases g with
                | type t =>
                  have := hv rfl ps b hmem v p t (by simpa [ParamAssign.paramList] using hap) hg
                  simp only [hg]
                  revert this
                  rcases hb : builtin E n sc t with _ | ⟨sc', bt⟩
                  · intro _; rfl
                  · cases bt with
                    | enumerated => intro _; rfl
                    | integer named =>
                      cases named with
                      | nil => intro this; exact valRefsOkB_of_ok this
                      | cons _ _ => intro _; rfl
                    | _ => intro this; exact valRefsOkB_of_ok this
                | _ => simp [hg]
            | _ => rfl
          | _ => simp at hty
        · rfl
  | _ => rfl

theorem defaultRefsOkB_of {s : Ty} (h : ComponentsOk E H n sc s) (hs : sizeOf s < n) :
    defaultRefsOkB E n sc s = true := by
  cases s with
  | sequence r e r2 =>
    simp only [ComponentsOk] at h
    simp only [defaultRefsOkB, List.all_eq_true]
    intro c hc
    split
    · rename_i nm t v
      simp only [Bool.or_eq_true]; right
      obtain ⟨en, hen, hsc, -, -, hp⟩ := mem_entries (E := E) (sc := sc) hc (by simp at hs; omega)
      obtain ⟨d', hd, -⟩ := h.1 en hen v hp
      rw [hsc] at hd
      exact valRefsOkB_of_eval hd (Nat.le_refl n)
    · rfl
  | set r e r2 =>
    simp only [ComponentsOk] at h
    simp only [defaultRefsOkB, List.all_eq_true]
    intro c hc
    split
    · rename_i nm t v
      simp only [Bool.or_eq_true]; right
      obtain ⟨en, hen, hsc, -, -, hp⟩ := mem_entries (E := E) (sc := sc) hc (by simp at hs; omega)
      obtain ⟨d', hd, -⟩ := h.1 en hen v hp
      rw [hsc] at hd
      exact valRefsOkB_of_eval hd (Nat.le_refl n)
    · rfl
  | _ => rfl

theorem consRefsOkB_of {s : Ty} (h : ConstraintsOk E H n sc s) (hs : sizeOf s < n) :
    consRefsOkB E n sc s = true := by
  cases s with
  | constrained t c =>
    simp only [ConstraintsOk] at h
    simp only [consRefsOkB, Bool.or_eq_true, List.all_eq_true]
    right; intro v hv
    obtain ⟨k, hk, w, hw⟩ := consOk_vals h v hv
    exact valRefsOkB_of_eval hw hk
  | _ => rfl

theorem osf_match_iff (x : Option (Scope × FieldSpec)) :
    (match x with | some (_, .objectSetField ..) => true | _ => false) = true ↔
      ∃ a nm c o, x = some (a, .objectSetField nm c o) := by
  rcases x with _ | ⟨a, f⟩
  · simp
  · cases f <;> simp

theorem isSet_iff {src : ObjSet} {path : List String} {cf : Scope × List FieldSpec} :
    ((match src with | .ref .. => true | _ => false) ||
      (List.range (path.length - 1)).any fun i =>
        match fieldAt E n cf (path.take (i + 1)) with
        | some (_, .objectSetField ..) => true
        | _ => false) = true ↔
    ((∃ mn nm args, src = .ref mn nm args) ∨
      ∃ i, i + 1 < path.length ∧ ∃ x nm c o, fieldAt E n cf (path.take (i + 1)) = some (x, .objectSetField nm c o)) := by
  rw [Bool.or_eq_true, List.any_eq_true]
  apply or_congr
  · cases src <;> simp
  · simp only [List.mem_range, osf_match_iff]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩

theorem tableTargetB_of : ∀ {n : Nat} {sc : Scope} {t : Ty}, TableTarget E n sc t → tableTargetB E n sc t = true
  | 0, _, _, h => by simp [TableTarget] at h
  | n + 1, sc, t, h => by
    cases t with
    | classField c p => rfl
    | instanceOf c => rfl
    | ref name =>
      simp only [TableTarget] at h; obtain ⟨sc', t', hr, h⟩ := h
      simp [tableTargetB, hr, tableTargetB_of h]
    | extRef mn name =>
      simp only [TableTarget] at h; obtain ⟨sc', t', hr, h⟩ := h
      simp [tableTargetB, hr, tableTargetB_of h]
    | paramRef mn name args =>
      simp only [TableTarget] at h; obtain ⟨sc', t', hr, h⟩ := h
      simp [tableTargetB, hr, tableTargetB_of h]
    | tagged _ _ u => simp only [TableTarget] at h; simp [tableTargetB, tableTargetB_of h]
    | constrained u _ => simp only [TableTarget] at h; simp [tableTargetB, tableTargetB_of h]
    | _ => simp [TableTarget] at h

theorem typeFromObjectsTableB_of {s : Ty} (h : TypeFromObjectsTableOk E n sc s) :
    typeFromObjectsTableB E n sc s = true := by
  cases s with
  | fromObjects src path =>
    simp only [TypeFromObjectsTableOk] at h
    simp only [typeFromObjectsTableB]
    split; rotate_left; · rfl
    rename_i csc cls hos
    split; rotate_left; · rfl
    rename_i cf hcf
    split
    · rfl
    · rename_i fsc nm o hf
      have := h _ _ _ _ _ hos hcf hf
      simp only at this
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact fun hb => this (isSet_iff.mp hb)
    · rename_i fsc nm t u o hf
      have := h _ _ _ _ _ hos hcf hf
      simp only at this
      exact isSet_iff.mpr this
    · rename_i p h1 h2 h3 hp
      obtain ⟨fsc, f⟩ := p
      have := h _ _ _ _ _ hos hcf hp
      cases f with
      | fixedValueSet a b c => exact (h1 _ _ _ _ rfl).elim
      | typeField a b => exact (h2 _ _ _ rfl).elim
      | fixedValue a b c d => exact (h3 _ _ _ _ _ rfl).elim
      | _ => simp at this
    · rfl
  | _ => rfl

theorem tableOnFieldB_of {s : Ty} (h : TableOnFieldOk E n sc s) : tableOnFieldB E n sc s = true := by
  unfold TableOnFieldOk at h; unfold tableOnFieldB; split
  · exact tableTargetB_of h
  · rfl

theorem defaultsInTypeB_of {s : Ty} (hup : ∀ n', n ≤ n' → ComponentsOk E H n' sc s) (hs : sizeOf s < n) :
    defaultsInTypeB E n sc s = true := by
  have key : ∀ {r r2 : List Comp} {e : Option (List ExtAdd)} {c : Comp},
      1 + sizeOf r + sizeOf e + sizeOf r2 < n → c ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2 →
      (∀ M, n ≤ M → ∀ en ∈ entries E M sc r e r2, ∀ d, en.presence = .default_ d →
        ∃ d', evalVal E M en.scope d d' ∧ (sem E H M en.scope [] en.ty).all d') →
      (∀ nm t d, Comp.mk nm t (.default_ d) ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2 →
        ValMaps E n n sc t sc d) →
      (match c with
        | .mk _ t (.default_ v) => valOkB E n sc t v
        | _ => true) = true := by
    intro r r2 e c hsz hc hdef hmaps
    split
    · rename_i nm t v
      have hcs := Comp.sizeOf_lt hc
      refine valOkB_of (H := H) (ValIn.of_eventually (n := n) fun M hM => ?_) (hmaps nm t v hc) (by simp at hcs; omega)
      obtain ⟨en, hen, hsc, hnm, hty, hp⟩ := mem_entries (E := E) (n := M) (sc := sc) hc (by omega)
      obtain ⟨d', hd, hsem⟩ := hdef M hM en hen v hp
      rw [hsc, hty] at *
      exact ⟨d', hd, hsem⟩
    · rfl
  cases s with
  | sequence r e r2 =>
    simp only [defaultsInTypeB, List.all_eq_true]
    intro c hc
    exact key (by simp at hs; omega) hc (fun M hM => (hup M hM).1) (hup n (Nat.le_refl n)).2.1
  | set r e r2 =>
    simp only [defaultsInTypeB, List.all_eq_true]
    intro c hc
    exact key (by simp at hs; omega) hc (fun M hM => (hup M hM).1) (hup n (Nat.le_refl n)).2.1
  | _ => rfl

/-- An element of an element set, at the fuel the spec checks it: `d` below the set's for the
set arithmetic above it. -/
theorem elemOk_of_mem {pt : Ty} {inPA : Bool} : ∀ {es : ElemSet} {el : Elem}, el ∈ esElems es →
    ∃ d, ∀ m, ESetOk E H (m + d + 1) sc pt inPA es → ElemOk E H m sc pt inPA el
  | .elem e, el, h => by
    simp only [esElems, List.mem_singleton] at h; subst h
    exact ⟨0, fun m hm => by simpa [ESetOk] using hm⟩
  | .union a b, el, h | .inter a b, el, h | .except a b, el, h => by
    simp only [esElems, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨d, hd⟩ := elemOk_of_mem h
      exact ⟨d + 1, fun m hm => hd m (by
        rw [show m + (d + 1) + 1 = (m + d + 1) + 1 by omega] at hm; simp only [ESetOk] at hm; exact hm.1)⟩
    · obtain ⟨d, hd⟩ := elemOk_of_mem h
      exact ⟨d + 1, fun m hm => hd m (by
        rw [show m + (d + 1) + 1 = (m + d + 1) + 1 by omega] at hm; simp only [ESetOk] at hm; exact hm.2)⟩
  | .allExcept b, el, h => by
    simp only [esElems] at h
    obtain ⟨d, hd⟩ := elemOk_of_mem h
    exact ⟨d + 1, fun m hm => hd m (by
      rw [show m + (d + 1) + 1 = (m + d + 1) + 1 by omega] at hm; simp only [ESetOk] at hm; exact hm)⟩

/-- An element of a constraint's element sets, at the fuel at which the spec resolves the parent
type at `n`. -/
theorem elemOk_of_cons {t : Ty} {r : ElemSet} {x : Bool} {a : Option ElemSet} {el : Elem}
    (hup : ∀ n', n ≤ n' → ConsOk E H n' sc t false (.mk r x a))
    (hel : el ∈ esElems r ∨ ∃ b, a = some b ∧ el ∈ esElems b) : ElemOk E H (n + 1) sc t false el := by
  rcases hel with hel | ⟨b, rfl, hel⟩
  · obtain ⟨d, hd⟩ := elemOk_of_mem hel
    have := hup (n + 1 + d + 1 + 1) (by omega)
    simp only [ConsOk] at this
    exact hd _ this.1
  · obtain ⟨d, hd⟩ := elemOk_of_mem hel
    have := hup (n + 1 + d + 1 + 1) (by omega)
    simp only [ConsOk] at this
    exact hd _ (this.2 b rfl)

theorem mem_esWithComps : ∀ {es : ElemSet} {l : List String}, l ∈ esWithComps es →
    ∃ x ncs, Elem.withComponents x ncs ∈ esElems es ∧ l = ncs.map (·.1)
  | .elem e, l, h => by
    cases e with
    | withComponents p cs =>
      simp only [esWithComps, List.mem_singleton] at h; subst h; exact ⟨p, cs, by simp [esElems], rfl⟩
    | _ => simp [esWithComps] at h
  | .union a b, l, h | .inter a b, l, h | .except a b, l, h => by
    simp only [esWithComps, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, ncs, h1, h2⟩ := mem_esWithComps h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩
    · obtain ⟨x, ncs, h1, h2⟩ := mem_esWithComps h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩
  | .allExcept b, l, h => by
    simp only [esWithComps] at h
    obtain ⟨x, ncs, h1, h2⟩ := mem_esWithComps h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩

theorem mem_esWithPres : ∀ {es : ElemSet} {l : List (String × PresenceC)}, l ∈ esWithPres es →
    ∃ x ncs, Elem.withComponents x ncs ∈ esElems es ∧ l = ncs.map fun (nm, _, p) => (nm, p)
  | .elem e, l, h => by
    cases e with
    | withComponents p cs =>
      simp only [esWithPres, List.mem_singleton] at h; subst h; exact ⟨p, cs, by simp [esElems], rfl⟩
    | _ => simp [esWithPres] at h
  | .union a b, l, h | .inter a b, l, h | .except a b, l, h => by
    simp only [esWithPres, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, ncs, h1, h2⟩ := mem_esWithPres h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩
    · obtain ⟨x, ncs, h1, h2⟩ := mem_esWithPres h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩
  | .allExcept b, l, h => by
    simp only [esWithPres] at h
    obtain ⟨x, ncs, h1, h2⟩ := mem_esWithPres h; exact ⟨x, ncs, by simp [esElems, h1], h2⟩

theorem innerNamesOkB_of {s : Ty} (hup : ∀ n', n ≤ n' → ConstraintsOk E H n' sc s) :
    innerNamesOkB E n sc s = true := by
  cases s with
  | constrained t c =>
    cases c with
    | mk r x a =>
      simp only [ConstraintsOk] at hup
      have key : ∀ l ∈ esWithComps r ++ (a.map esWithComps).getD [], ∃ x' ncs, l = ncs.map (·.1) ∧
          ElemOk E H (n + 1) sc t false (.withComponents x' ncs) := by
        intro l hl
        rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨x', ncs, hel, rfl⟩ := mem_esWithComps hl
          exact ⟨x', ncs, rfl, elemOk_of_cons hup (.inl hel)⟩
        · cases a with
          | none => simp at hl
          | some b =>
            obtain ⟨x', ncs, hel, rfl⟩ := mem_esWithComps (by simpa using hl)
            exact ⟨x', ncs, rfl, elemOk_of_cons hup (.inr ⟨b, rfl, hel⟩)⟩
      simp only [innerNamesOkB]
      split
      · rfl
      · rename_i hne
        -- the names each WITH COMPONENTS writes are among the structure's, once each
        have hok : ∀ sc' bt, builtin E n sc t = some (sc', bt) →
            ∀ l ∈ esWithComps r ++ (a.map esWithComps).getD [],
              (∀ nm ∈ l, ∃ csc ct, (nm, csc, ct) ∈ structComps E n (innerTarget sc' bt).1
                (innerTarget sc' bt).2) ∧ l.Nodup := by
          intro sc' bt hb l hl
          obtain ⟨x', ncs, rfl, hel⟩ := key l hl
          unfold ElemOk at hel
          obtain ⟨sc'', bt', row, hb', -, -, -, -, hnd, hcomp, -⟩ := hel
          rw [hb] at hb'; cases hb'
          refine ⟨fun nm hnm => ?_, hnd⟩
          obtain ⟨⟨nm', oc, p⟩, hm, rfl⟩ := List.mem_map.1 hnm
          obtain ⟨csc, ct, h1, -⟩ := hcomp nm' oc p hm
          exact ⟨csc, ct, h1⟩
        rcases n with _ | k
        · simp [builtin]
        have hall : ∀ names : List String, (∀ sc' bt, builtin E (k + 1) sc t = some (sc', bt) →
            ∀ nm csc ct, (nm, csc, ct) ∈ structComps E (k + 1) (innerTarget sc' bt).1 (innerTarget sc' bt).2 →
              nm ∈ names) → (∃ sc' bt, builtin E (k + 1) sc t = some (sc', bt)) →
            ((esWithComps r ++ (a.map esWithComps).getD []).all fun l =>
              (l.all fun x => names.contains x) && decide l.Nodup) = true := by
          intro names hnames ⟨sc', bt, hb⟩
          simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq]
          intro l hl
          obtain ⟨h1, h2⟩ := hok sc' bt hb l hl
          refine ⟨fun nm hnm => ?_, h2⟩
          obtain ⟨csc, ct, h3⟩ := h1 nm hnm
          exact hnames sc' bt hb nm csc ct h3
        split
        · rename_i sc' ro e r2 hb
          refine (Bool.or_eq_true _ _).mpr (.inr ?_)
          refine hall _ (fun sc'' bt hb' nm csc ct h => ?_) ⟨_, _, hb⟩
          rw [hb] at hb'; cases hb'
          simp only [innerTarget, structComps, builtin, List.mem_map] at h
          obtain ⟨en, hen, he⟩ := h
          simp only [Prod.mk.injEq] at he
          exact List.mem_map.2 ⟨en, hen, he.1⟩
        · rename_i sc' ro e r2 hb
          refine (Bool.or_eq_true _ _).mpr (.inr ?_)
          refine hall _ (fun sc'' bt hb' nm csc ct h => ?_) ⟨_, _, hb⟩
          rw [hb] at hb'; cases hb'
          simp only [innerTarget, structComps, builtin, List.mem_map] at h
          obtain ⟨en, hen, he⟩ := h
          simp only [Prod.mk.injEq] at he
          exact List.mem_map.2 ⟨en, hen, he.1⟩
        · rename_i sc' ro e hb
          refine hall _ (fun sc'' bt hb' nm csc ct h => ?_) ⟨_, _, hb⟩
          rw [hb] at hb'; cases hb'
          simp only [innerTarget, structComps, builtin, List.mem_map] at h
          obtain ⟨en, hen, he⟩ := h
          simp only [Prod.mk.injEq] at he
          exact List.mem_map.2 ⟨en, hen, he.1⟩
        · rfl
    | _ => rfl
  | _ => rfl

/-- An element of a constraint's element sets, at arbitrarily large fuel. -/
theorem elemOk_freq {pt : Ty} {inPA : Bool} {r : ElemSet} {x : Bool} {a : Option ElemSet} {el : Elem}
    (h : ∀ N, ∃ M, N ≤ M ∧ ConsOk E H M sc pt inPA (.mk r x a))
    (hel : el ∈ esElems r ∨ ∃ b, a = some b ∧ el ∈ esElems b) :
    ∀ N, ∃ M, N ≤ M ∧ ElemOk E H M sc pt inPA el := by
  intro N
  rcases hel with hel | ⟨b, rfl, hel⟩
  · obtain ⟨d, hd⟩ := elemOk_of_mem (E := E) (H := H) (sc := sc) (pt := pt) (inPA := inPA) hel
    obtain ⟨M, hM, hc⟩ := h (N + d + 2)
    obtain ⟨m, rfl⟩ : ∃ m, M = m + d + 2 := ⟨M - d - 2, by omega⟩
    rw [show m + d + 2 = (m + d + 1) + 1 by omega] at hc
    simp only [ConsOk] at hc
    exact ⟨m, by omega, hd m hc.1⟩
  · obtain ⟨d, hd⟩ := elemOk_of_mem (E := E) (H := H) (sc := sc) (pt := pt) (inPA := inPA) hel
    obtain ⟨M, hM, hc⟩ := h (N + d + 2)
    obtain ⟨m, rfl⟩ : ∃ m, M = m + d + 2 := ⟨M - d - 2, by omega⟩
    rw [show m + d + 2 = (m + d + 1) + 1 by omega] at hc
    simp only [ConsOk] at hc
    exact ⟨m, by omega, hd m (hc.2 b rfl)⟩

theorem evalBound_int {sc : Scope} {v : Val} {i : Int} {M : Nat} (hv : intOfV E n sc 8 v = some i)
    (hM : n + 10 ≤ M) {b : Bound} (h : EvalBound E M sc (.val v) b) : b = .val (.int i) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  simp only [EvalBound] at h
  obtain ⟨w, hw, rfl⟩ := h
  rw [(evalVal_of_intOfV hv M (by omega) w).mp hw]

theorem evalBound_max {sc : Scope} {M : Nat} (hM : 1 ≤ M) {b : Bound} (h : EvalBound E M sc .max b) :
    b = .max := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  simpa [EvalBound] using h

theorem evalBound_min {sc : Scope} {M : Nat} (hM : 1 ≤ M) {b : Bound} (h : EvalBound E M sc .min b) :
    b = .min := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  simpa [EvalBound] using h

/-- A number `intPoints` lists is a root value of the parent, at arbitrarily large fuel. -/
theorem intPoints_root {pt : Ty} {el : Elem} {i : Int} (hint : isIntTy E n sc pt = true)
    (hel : ∀ N, ∃ M, N ≤ M ∧ ElemOk E H M sc pt false el) (hi : i ∈ intPoints E n sc el) :
    ∀ N, ∃ M, N ≤ M ∧ ∃ outer, (sem E H M sc outer pt).at false (.int i) := by
  intro N
  obtain ⟨M, hM, hok⟩ := hel (N + n + 12)
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨sc', bt, r, hb, -, -, -, hm⟩ := hok
  unfold isIntTy at hint
  split at hint
  · rename_i s nb hbn
    rw [builtin_mono hbn (by omega : n ≤ M)] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨M, by omega, [], ?_⟩
    simp only [VSet.at, Bool.false_eq_true, ↓reduceIte]
    cases el with
    | single v =>
      simp only [intPoints, Option.mem_toList, Option.mem_def] at hi
      obtain ⟨⟨w, hw, hroot⟩, -⟩ := hm
      rwa [(evalVal_of_intOfV hi M (by omega) w).mp hw] at hroot
    | range lo loOpen hi' hiOpen =>
      obtain ⟨l, h, hl, hh, hall, -⟩ := hm
      have hint : (sem E H M s [] (.integer nb)).all (.int i) := by
        obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        simp [sem, VSet.plain]
      refine hall _ hint ?_
      simp only [RangeHas, InRange]
      simp only [intPoints, List.mem_append] at hi
      rcases hi with hi | hi
      · cases loOpen <;> simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hi
        cases lo with
        | val v =>
          simp only [Option.mem_toList, Option.mem_def, Option.filter_eq_some_iff] at hi
          obtain ⟨hvi, hinHi⟩ := hi
          rw [evalBound_int hvi (by omega) hl]
          refine ⟨by simp [Val.le], ?_⟩
          cases hi' with
          | max => rw [evalBound_max (by omega) hh]; trivial
          | min => simp at hinHi
          | val v' =>
            simp only [Option.any_eq_true] at hinHi
            obtain ⟨j, hj, hij⟩ := hinHi
            rw [evalBound_int hj (by omega) hh]
            cases hiOpen <;> simp_all [Val.lt, Val.le] <;> omega
        | _ => simp at hi
      · cases hiOpen <;> simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hi
        cases hi' with
        | val v =>
          simp only [Option.mem_toList, Option.mem_def, Option.filter_eq_some_iff] at hi
          obtain ⟨hvi, hinLo⟩ := hi
          rw [evalBound_int hvi (by omega) hh]
          refine ⟨?_, by simp [Val.le]⟩
          cases lo with
          | min => rw [evalBound_min (by omega) hl]; trivial
          | max => simp at hinLo
          | val v' =>
            simp only [Option.any_eq_true] at hinLo
            obtain ⟨j, hj, hij⟩ := hinLo
            rw [evalBound_int hj (by omega) hl]
            cases loOpen <;> simp_all [Val.lt, Val.le] <;> omega
        | _ => simp at hi
    | _ => simp [intPoints] at hi
  · simp at hint

theorem intConsValsOkB_of {pt : Ty} {c : Constraint} (h : ∀ N, ∃ M, N ≤ M ∧ ConsOk E H M sc pt false c) :
    intConsValsOkB E n sc pt c = true := by
  unfold intConsValsOkB
  cases hint : isIntTy E n sc pt with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro el hel i hi
    cases c with
    | mk r x a =>
      have hel' : el ∈ esElems r ∨ ∃ b, a = some b ∧ el ∈ esElems b := by
        simp only [consElems, List.mem_append] at hel
        rcases hel with hel | hel
        · exact .inl hel
        · cases a with
          | none => simp at hel
          | some b => exact .inr ⟨b, rfl, by simpa using hel⟩
      cases hn : intNotInTy E n 16 sc pt i false with
      | false => rfl
      | true =>
        exact absurd (intPoints_root hint (elemOk_freq h hel') hi) (intNotInTy_sound (isIntTy_eqTy hint) hn)
    | _ => simp [consElems] at hel


theorem structComps_stable {sc : Scope} {t : Ty} {M : Nat} (hk : structKnown E n sc t = true)
    (hne : structComps E n sc t ≠ []) (hM : n ≤ M) : structComps E M sc t = structComps E n sc t := by
  unfold structKnown at hk
  unfold structComps at hne ⊢
  cases hb : builtin E n sc t with
  | none => simp [hb] at hne
  | some r =>
    rw [builtin_mono hb hM]
    obtain ⟨s, b⟩ := r
    rw [hb] at hk
    cases b <;> simp only at hk ⊢
    · rw [entries_stable hk hM]
    · rw [entries_stable hk hM]

/-- The spec at arbitrarily large fuel. -/
abbrev Freq (P : Nat → Prop) : Prop := ∀ N, ∃ M, N ≤ M ∧ P M

theorem Freq.shift {P : Nat → Prop} (h : Freq P) (k : Nat) : ∀ N, ∃ M, N ≤ M ∧ P (M + k) := by
  intro N
  obtain ⟨M, hM, hp⟩ := h (N + k)
  exact ⟨M - k, by omega, by rw [show M - k + k = M by omega]; exact hp⟩

theorem refMapsB_of_mono {M : Nat} {sc vsc : Scope} {t : Ty} {v : Val} (h : RefMaps E M sc t vsc v)
    (hM : n ≤ M) : refMapsB E n sc t v vsc = true := by
  cases v with
  | ref mn nm args =>
    simp only [RefMaps] at h
    simp only [refMapsB]
    split
    · rename_i usc u p hu hp
      split
      · rename_i q hq
        have hp' : ((builtin E M sc t).bind fun x => mapName x.2) = some p := by
          simp only [Option.bind_eq_some_iff] at hp ⊢
          obtain ⟨x, hx, hx'⟩ := hp; exact ⟨x, builtin_mono hx hM, hx'⟩
        have hq' : ((builtin E M usc u).bind fun x => mapName x.2) = some q := by
          simp only [Option.bind_eq_some_iff] at hq ⊢
          obtain ⟨x, hx, hx'⟩ := hq; exact ⟨x, builtin_mono hx hM, hx'⟩
        simp [h usc u p q (resolveValTy_mono hu hM) hp' hq']
      · rfl
    · rfl
  | _ => simp [refMapsB]

/-- What `consOkB_of` says, for each kind of syntax. -/
def ConsOkBOf (E : Env) (H : ContentsHook) (n : Nat) (c : Constraint) : Prop :=
  ∀ {sc : Scope} {pt : Ty} {inPA : Bool}, Freq (fun M => ConsOk E H M sc pt inPA c) → consOkB E n sc pt inPA c = true
def ESetOkBOf (E : Env) (H : ContentsHook) (n : Nat) (es : ElemSet) : Prop :=
  ∀ {sc : Scope} {pt : Ty} {inPA : Bool}, Freq (fun M => ESetOk E H M sc pt inPA es) → esOkB E n sc pt inPA es = true
def ElemOkBOf (E : Env) (H : ContentsHook) (n : Nat) (el : Elem) : Prop :=
  ∀ {sc : Scope} {pt : Ty} {inPA : Bool}, Freq (fun M => ElemOk E H M sc pt inPA el) → elemOkB E n sc pt inPA el = true

theorem consOkB_all : ∀ k : Nat, (∀ c : Constraint, sizeOf c < k → ConsOkBOf E H n c) ∧
    (∀ es : ElemSet, sizeOf es < k → ESetOkBOf E H n es) ∧ (∀ el : Elem, sizeOf el < k → ElemOkBOf E H n el)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
    obtain ⟨ihc, ihes, ihel⟩ := consOkB_all k
    refine ⟨fun c hs => ?_, fun es hs => ?_, fun el hs => ?_⟩
    · intro sc pt inPA h
      cases c with
      | mk root x adds =>
        unfold consOkB
        simp only [Bool.and_eq_true]
        refine ⟨ihes root (by simp at hs; omega) fun N => ?_, ?_⟩
        · obtain ⟨M, hM, hc⟩ := h.shift 1 N
          simp only [ConsOk] at hc
          exact ⟨M, hM, hc.1⟩
        · cases adds with
          | none => rfl
          | some a =>
            simp only
            exact ihes a (by simp at hs; omega) fun N => by
              obtain ⟨M, hM, hc⟩ := h.shift 1 N
              simp only [ConsOk] at hc
              exact ⟨M, hM, hc.2 a rfl⟩
      | contents t enc =>
        unfold consOkB
        cases hb : builtin E n sc pt with
        | none => rfl
        | some p =>
          obtain ⟨s, b⟩ := p
          obtain ⟨M, hM, hc⟩ := h.shift 1 n
          simp only [ConsOk, builtin_mono hb hM] at hc
          cases b <;> first | rfl | exact absurd hc id
      | table os refs => unfold consOkB; rfl
      | userDefined => unfold consOkB; rfl
    · intro sc pt inPA h
      cases es with
      | elem el =>
        unfold esOkB
        exact ihel el (by simp at hs; omega) fun N => by
          obtain ⟨M, hM, hc⟩ := h.shift 1 N
          simp only [ESetOk] at hc
          exact ⟨M, hM, hc⟩
      | union a b | inter a b | except a b =>
        unfold esOkB
        simp only [Bool.and_eq_true]
        refine ⟨ihes a (by simp at hs; omega) fun N => ?_, ihes b (by simp at hs; omega) fun N => ?_⟩
        all_goals
          obtain ⟨M, hM, hc⟩ := h.shift 1 N
          simp only [ESetOk] at hc
        · exact ⟨M, hM, hc.1⟩
        · exact ⟨M, hM, hc.2⟩
      | allExcept b =>
        unfold esOkB
        exact ihes b (by simp at hs; omega) fun N => by
          obtain ⟨M, hM, hc⟩ := h.shift 1 N
          simp only [ESetOk] at hc
          exact ⟨M, hM, hc⟩
    · intro sc pt inPA h
      unfold elemOkB
      split
      · rfl
      · rename_i sc' bt hb
        split
        · rfl
        · rename_i r hr
          -- the spec's facts, with the checker's built-in type
          have spec : Freq (fun M => n + 12 ≤ M ∧ ∃ r', builtin E M sc pt = some (sc', bt) ∧ rowOf bt = some r' ∧
              (r'.allows el.kind ∨ (∃ k, r' = .restricted k ∧ k.knownOrder ∧ inPA ∧ el.kind = .range)) ∧
              (inPA = true → el.kind ∈ [.single, .contained, .range, .size]) ∧
              ElemOk E H (M + 1) sc pt inPA el) := fun N => by
            obtain ⟨M, hM, hok⟩ := h.shift 1 (N + n + 12)
            have hok' := hok
            obtain ⟨sc'', bt'', r'', hb', hr', ha, hi, -⟩ := hok
            rw [builtin_mono hb (by omega : n ≤ M)] at hb'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'
            obtain ⟨rfl, rfl⟩ := hb'
            exact ⟨M, by omega, by omega, r'', builtin_mono hb (by omega), hr', ha, hi, hok'⟩
          obtain ⟨M, -, -, r', -, hr', ha, hi, -⟩ := spec 0
          rw [hr] at hr'; cases hr'
          simp only [Bool.and_eq_true]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rcases ha with ha | ⟨k, rfl, hk, hpa, hkind⟩
            · simp [ha]
            · simp [hk, hpa, hkind]
          · cases inPA
            · rfl
            · simpa using hi rfl
          -- the element's own rules
          have get : ∀ N, ∃ M, N ≤ M ∧ n ≤ M ∧ ElemOk E H (M + 1) sc pt inPA el ∧ builtin E M sc pt = some (sc', bt) :=
            fun N => by
              obtain ⟨M, hM, hM', r', hb', -, -, -, hok⟩ := spec N
              exact ⟨M, hM, by omega, hok, hb'⟩
          cases el with
          | single v =>
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, -, hm⟩ := hok
            exact refMapsB_of_mono hm (by omega)
          | range lo lo' hi' hi'' =>
            obtain ⟨M, hMN, hM, hok, hb'⟩ := get (n + 12)
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, l, hh, hl, hhv, -, hsingle, -, hmlo, hmhi⟩ := hok
            simp only [Bool.and_eq_true]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · cases inPA
              · rfl
              · obtain ⟨s1, s2⟩ := hsingle rfl
                simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
                constructor
                · cases lo with
                  | val v =>
                    simp only
                    cases hc : charsOfV E n sc 8 v with
                    | none => rfl
                    | some cs =>
                      obtain ⟨M2, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
                      simp only [EvalBound] at hl
                      obtain ⟨w, hw, rfl⟩ := hl
                      rw [(evalVal_of_charsOfV hc M2 (by omega) w).mp hw] at s1
                      rcases cs with _ | ⟨c1, _ | _⟩ <;> simp_all [SingleChar]
                  | _ => rfl
                · cases hi' with
                  | val v =>
                    simp only
                    cases hc : charsOfV E n sc 8 v with
                    | none => rfl
                    | some cs =>
                      obtain ⟨M2, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
                      simp only [EvalBound] at hhv
                      obtain ⟨w, hw, rfl⟩ := hhv
                      rw [(evalVal_of_charsOfV hc M2 (by omega) w).mp hw] at s2
                      rcases cs with _ | ⟨c1, _ | _⟩ <;> simp_all [SingleChar]
                  | _ => rfl
            · cases lo with
              | val v => exact refMapsB_of_mono (hmlo v rfl) (by omega)
              | _ => rfl
            · cases hi' with
              | val v => exact refMapsB_of_mono (hmhi v rfl) (by omega)
              | _ => rfl
          | contained t' x =>
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', hr'', -, -, sc3, bt3, hb3, hr3⟩ := hok
            rw [hb'] at hb''; cases hb''
            rw [hr] at hr''; cases hr''
            simp only
            split
            · rename_i r2 hr2
              simp only [Option.bind_eq_some_iff] at hr2
              obtain ⟨⟨s4, b4⟩, hb4, hr4⟩ := hr2
              rw [builtin_mono hb4 hM] at hb3; cases hb3
              rw [hr4] at hr3; cases hr3
              simp
            · rfl
          | size c =>
            simp only [Bool.and_eq_true]
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, hsub, -⟩ := hok
            have hc : Freq (fun M => ConsOk E H M sc sizeParentTy false c) := fun N => by
              obtain ⟨M, hM, -, hok, -⟩ := get N
              obtain ⟨-, -, -, -, -, -, -, -, hcons⟩ := hok
              exact ⟨M, hM, hcons⟩
            exact ⟨⟨hsub, ihc c (by simp at hs; omega) hc⟩, intConsValsOkB_of hc⟩
          | from_ c =>
            simp only [Bool.and_eq_true]
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, hsub, -⟩ := hok
            refine ⟨hsub, ihc c (by simp at hs; omega) fun N => ?_⟩
            obtain ⟨M, hM, -, hok, -⟩ := get N
            obtain ⟨-, -, -, -, -, -, -, -, hcons⟩ := hok
            exact ⟨M, hM, hcons⟩
          | withComponent c =>
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, hm⟩ := hok
            rw [hb'] at hb''; cases hb''
            simp only
            split
            · rename_i et
              refine ihc c (by simp at hs; omega) fun N => ?_
              obtain ⟨M, hM, -, hok, hb'⟩ := get N
              obtain ⟨sc'', bt'', r'', hb'', -, -, -, hm⟩ := hok
              rw [hb'] at hb''; cases hb''
              exact ⟨M, hM, hm⟩
            · rename_i et
              refine ihc c (by simp at hs; omega) fun N => ?_
              obtain ⟨M, hM, -, hok, hb'⟩ := get N
              obtain ⟨sc'', bt'', r'', hb'', -, -, -, hm⟩ := hok
              rw [hb'] at hb''; cases hb''
              exact ⟨M, hM, hm⟩
            · simp_all
          | withComponents isPartial ncs =>
            obtain ⟨M0, -, hM0, hok0, hb0⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, -, hm0⟩ := hok0
            rw [hb0] at hb''; cases hb''
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm0 ⊢
            generalize hit : innerTarget sc' bt = itp at hm0 ⊢
            obtain ⟨isc, it⟩ := itp
            simp only at hm0 ⊢
            refine ⟨hm0.1, ?_⟩
            by_cases hne : structComps E n isc it = []
            · simp [hne]
            by_cases hk : structKnown E n isc it = true
            · right
              simp only [List.all_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
              intro ⟨⟨nm, oc, p⟩, hmem⟩ _
              -- the spec's components are the checker's
              have hspec : Freq (fun M => ∃ csc ct, (nm, csc, ct) ∈ structComps E n isc it ∧
                  ∀ c, oc = some c → ConsOk E H M csc ct false c) := fun N => by
                obtain ⟨M, hM, hMn, hok, hbM⟩ := get N
                obtain ⟨sc'', bt'', r'', hb'', -, -, -, -, hm⟩ := hok
                rw [hbM] at hb''; cases hb''
                simp only [hit] at hm
                obtain ⟨-, hall, -⟩ := hm
                obtain ⟨csc, ct, hc, hcons⟩ := hall nm oc p hmem
                rw [structComps_stable hk hne hMn] at hc
                exact ⟨M, hM, csc, ct, hc, hcons⟩
              obtain ⟨M, -, csc, ct, hc, -⟩ := hspec 0
              refine ⟨⟨_, hc, rfl⟩, ?_⟩
              cases oc with
              | none => rfl
              | some c =>
                simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
                obtain ⟨x, hx, hq⟩ := frequently_mem (l := structComps E n isc it)
                  (Q := fun x M => x.1 = nm ∧ ConsOk E H M x.2.1 x.2.2 false c) fun N => by
                    obtain ⟨M, hM, csc, ct, hc, hcons⟩ := hspec N
                    exact ⟨M, hM, _, hc, rfl, hcons c rfl⟩
                obtain ⟨-, -, hname, -⟩ := hq 0
                refine ⟨x, hx, hname, ihc c ?_ fun N => ?_⟩
                · have := List.sizeOf_lt_of_mem hmem
                  simp at this hs ⊢; omega
                · obtain ⟨M, hM, -, h2⟩ := hq N; exact ⟨M, hM, h2⟩
            · left; right; simpa using hk
          | typeC t' => rfl
          | pattern re => rfl
          | settings ps =>
            obtain ⟨M, -, hM, hok, hb'⟩ := get 0
            obtain ⟨sc'', bt'', r'', hb'', -, -, -, hm⟩ := hok
            exact hm

theorem consOkB_of {sc : Scope} {pt : Ty} {inPA : Bool} {c : Constraint}
    (h : Freq (fun M => ConsOk E H M sc pt inPA c)) : consOkB E n sc pt inPA c = true :=
  (consOkB_all (sizeOf c + 1)).1 c (by omega) h


/-! ### X.680 49.7: a constraint selects some value -/

/-- `i` and `j` lie alike against `k`. -/
def SameSide (i j k : Int) : Prop := (i < k ↔ j < k) ∧ (i = k ↔ j = k)

theorem intInElem_profile {sc : Scope} {i j : Int} {ks : List Int} {e : Elem}
    (hks : ∀ v ∈ elVals e, ∀ k, intOfV E n sc 8 v = some k → k ∈ ks)
    (hp : ∀ k ∈ ks, SameSide i j k) : intInElem E n sc i e = intInElem E n sc j e := by
  have lt_iff : ∀ k ∈ ks, (k < i ↔ k < j) := by
    intro k hk; obtain ⟨h1, h2⟩ := hp k hk; constructor <;> intro h <;> omega
  have le_iff : ∀ k ∈ ks, (k ≤ i ↔ k ≤ j) := by
    intro k hk; obtain ⟨h1, h2⟩ := hp k hk; constructor <;> intro h <;> omega
  cases e with
  | single v =>
    simp only [intInElem]
    cases hv : intOfV E n sc 8 v with
    | none => rfl
    | some k =>
      have hk := hks v (by simp [elVals]) k hv
      simp only [Option.map_some, Option.some.injEq]
      have := (hp k hk).2
      by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  | range lo loOpen hi hiOpen =>
    simp only [intInElem]
    congr 1
    · cases lo with
      | val v =>
        simp only
        cases hv : intOfV E n sc 8 v with
        | none => rfl
        | some l =>
          have hk := hks v (by simp [elVals, boundVals]) l hv
          simp only [Option.map_some, Option.some.injEq]
          cases loOpen <;> simp [lt_iff l hk, le_iff l hk]
      | _ => rfl
    · cases hi with
      | val v =>
        simp only
        cases hv : intOfV E n sc 8 v with
        | none => rfl
        | some h =>
          have hk := hks v (by simp [elVals, boundVals]) h hv
          simp only [Option.map_some, Option.some.injEq]
          obtain ⟨h1, h2⟩ := hp h hk
          cases hiOpen
          · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_decide]; constructor <;> intro <;> omega
          · simp only [↓reduceIte, decide_eq_decide]; exact h1
      | _ => rfl
  | _ => rfl

theorem intInES_profile {sc : Scope} {i j : Int} {ks : List Int} (hp : ∀ k ∈ ks, SameSide i j k) :
    ∀ es : ElemSet, (∀ v ∈ esVals es, ∀ k, intOfV E n sc 8 v = some k → k ∈ ks) →
      intInES E n sc i es = intInES E n sc j es
  | .elem e, hks => by
    simp only [intInES, decES]
    rw [intInElem_profile (fun v hv k hk => hks v (by simpa [esVals] using hv) k hk) hp]
  | .union a b, hks | .inter a b, hks | .except a b, hks => by
    have ha := intInES_profile hp a (fun v hv k hk => hks v (by simp [esVals, hv]) k hk)
    have hb := intInES_profile hp b (fun v hv k hk => hks v (by simp [esVals, hv]) k hk)
    simp only [intInES] at ha hb ⊢
    simp only [decES, ha, hb]
  | .allExcept b, hks => by
    have hb := intInES_profile hp b (fun v hv k hk => hks v (by simpa [esVals] using hv) k hk)
    simp only [intInES] at hb ⊢
    simp only [decES, hb]

theorem foldl_min_le : ∀ (ks : List Int) (init : Int), ks.foldl min init ≤ init ∧ ∀ k ∈ ks, ks.foldl min init ≤ k
  | [], init => by simp
  | k :: ks, init => by
    obtain ⟨h1, h2⟩ := foldl_min_le ks (min init k)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨by omega, by omega, h2⟩

theorem exists_max_below (j : Int) : ∀ (ks : List Int), (∃ k ∈ ks, k < j) →
    ∃ a ∈ ks, a < j ∧ ∀ k ∈ ks, k < j → k ≤ a
  | [], h => by simp at h
  | k :: ks, h => by
    by_cases hr : ∃ k' ∈ ks, k' < j
    · obtain ⟨a, ha, haj, hmax⟩ := exists_max_below j ks hr
      by_cases hk : k < j ∧ a < k
      · exact ⟨k, by simp, hk.1, fun k' hk' hk'j => by
          rcases List.mem_cons.mp hk' with rfl | hk'
          · omega
          · have := hmax k' hk' hk'j; omega⟩
      · exact ⟨a, by simp [ha], haj, fun k' hk' hk'j => by
          rcases List.mem_cons.mp hk' with rfl | hk'
          · omega
          · exact hmax k' hk' hk'j⟩
    · obtain ⟨k0, hk0, hk0j⟩ := h
      rcases List.mem_cons.mp hk0 with rfl | hk0
      · exact ⟨k0, by simp, hk0j, fun k' hk' hk'j => by
          rcases List.mem_cons.mp hk' with rfl | hk'
          · omega
          · exact absurd ⟨k', hk', hk'j⟩ hr⟩
      · exact absurd ⟨k0, hk0, hk0j⟩ hr

/-- Some candidate of `intNonEmptyB` lies alike against every number as `j` does. -/
theorem exists_candidate (ks : List Int) (j : Int) :
    ∃ c ∈ [ks.foldl min 0 - 2, ks.foldl max 0 + 2] ++ ks.flatMap (fun k => [k - 1, k, k + 1]),
      ∀ k ∈ ks, SameSide c j k := by
  by_cases hj : j ∈ ks
  · exact ⟨j, by simp; exact .inr (.inr ⟨j, hj, by simp⟩), fun k _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  by_cases hb : ∃ k ∈ ks, k < j
  · obtain ⟨a, ha, haj, hmax⟩ := exists_max_below j ks hb
    refine ⟨a + 1, by simp; exact .inr (.inr ⟨a, ha, by simp⟩), fun k hk => ?_⟩
    by_cases hkj : k < j
    · have := hmax k hk hkj; constructor <;> constructor <;> intro <;> omega
    · have hne : k ≠ j := fun h => hj (h ▸ hk)
      constructor <;> constructor <;> intro <;> omega
  · push Not at hb
    obtain ⟨-, hlo⟩ := foldl_min_le ks 0
    refine ⟨ks.foldl min 0 - 2, by simp, fun k hk => ?_⟩
    have := hlo k hk; have := hb k hk
    have hne : k ≠ j := fun h => hj (h ▸ hk)
    constructor <;> constructor <;> intro <;> omega

/-- `intNonEmptyB` decides nothing wrong: when it says empty, no value of the governor is in the
element sets (with their additions). -/
theorem intNonEmpty_sound {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop}
    {root : ElemSet} {adds : Option ElemSet} (hn : intNonEmptyB E n sc root adds = false)
    (hpt : ∀ M, n + 1 ≤ M → ∀ x y, eqv E M sc pt x y ↔ x = y) {M : Nat}
    (hM : n + 11 + sizeOf root + sizeOf adds ≤ M) {j : Int} (hg : g (.int j))
    (hin : (eset E H M sc outer pt g root).a (.int j) ∨ ∃ a, adds = some a ∧ (eset E H M sc outer pt g a).a (.int j)) :
    False := by
  simp only [intNonEmptyB, Bool.not_eq_false', List.all_eq_true, beq_iff_eq] at hn
  set ks := (esVals root ++ (adds.map esVals).getD []).filterMap (intOfV E n sc 8) with hks
  obtain ⟨c, hc, hside⟩ := exists_candidate ks j
  have hfalse := hn c hc
  have hroot := intInES_profile (E := E) (n := n) (sc := sc) hside root (fun v hv k hk => by
    rw [hks]; exact List.mem_filterMap.mpr ⟨v, by simp [hv], hk⟩)
  have hD := intInES_decides (H := H) (outer := outer) hg hpt root M (by omega)
  have key : (Dec.ofSpecs (intInES E n sc j root) (adds.map (intInES E n sc j))).2 ≠ some false := by
    intro hf
    cases adds with
    | none =>
      simp only [Dec.ofSpecs, Option.map_none] at hf
      rcases hin with hin | ⟨a, ha, -⟩
      · exact hD.2.some_false hf hin
      · simp at ha
    | some a =>
      have hDa := intInES_decides (H := H) (outer := outer) hg hpt a M (by simp at hM <;> omega)
      simp only [Dec.ofSpecs, Option.map_some] at hf
      have := (hD.2.orB hDa.2).some_false hf
      rcases hin with hin | ⟨a', ha', hin⟩
      · exact this (.inl hin)
      · simp at ha'; subst ha'; exact this (.inr hin)
  apply key
  rw [← hfalse]
  simp only [Dec.ofSpecs, hroot]
  cases adds with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    rw [intInES_profile (E := E) (n := n) (sc := sc) hside a (fun v hv k hk => by
      rw [hks]; exact List.mem_filterMap.mpr ⟨v, by simp [hv], hk⟩)]


theorem sizeEmpty_sound {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} :
    ∀ (es : ElemSet) (M : Nat), n + 14 + sizeOf es ≤ M → sizeEmptyB E n sc es = true →
      ∀ x, ¬ ((eset E H M sc outer pt g es).r x ∨ (eset E H M sc outer pt g es).a x)
  | .elem (.size (.mk r ext a)), M + 3, hM, h, x, hx => by
    simp only [sizeEmptyB, Bool.not_eq_true'] at h
    simp only [eset, elem, ESet.bySize] at hx
    have hall : ∃ k : Nat, (cons E H (M + 1) sc outer (.integer []) sizeParent (.mk r ext a)).all (.int k) := by
      rcases hx with ⟨-, k, -, hk⟩ | ⟨-, k, -, hk⟩
      · exact ⟨k, cons_root_all hk⟩
      · exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hall
    simp only [cons, VSet.keepExt, VSet.ofSpecs] at hk
    refine intNonEmpty_sound (H := H) (outer := outer) (pt := .integer []) (g := sizeParent.root) h
      (fun M hM => eqv_integer M (by omega)) (M := M) (by simp at hM <;> omega) (j := k) ⟨k, rfl⟩ ?_
    rcases hk with hk | ⟨e, he, hk⟩
    · exact .inl hk
    · cases a with
      | none => simp at he
      | some a => simp at he; subst he; exact .inr ⟨a, rfl, hk⟩
  | .elem (.size (.mk ..)), 0, hM, _, _, _ | .elem (.size (.mk ..)), 1, hM, _, _, _
  | .elem (.size (.mk ..)), 2, hM, _, _, _ => by simp at hM <;> omega
  | .elem (.size (.contents ..)), _, _, h, _, _ | .elem (.size (.table ..)), _, _, h, _, _
  | .elem (.size .userDefined), _, _, h, _, _ => by simp [sizeEmptyB] at h
  | .elem (.single _), _, _, h, _, _ | .elem (.contained ..), _, _, h, _, _ | .elem (.range ..), _, _, h, _, _
  | .elem (.typeC _), _, _, h, _, _ | .elem (.from_ _), _, _, h, _, _ | .elem (.withComponent _), _, _, h, _, _
  | .elem (.withComponents ..), _, _, h, _, _ | .elem (.pattern _), _, _, h, _, _
  | .elem (.settings _), _, _, h, _, _ | .allExcept _, _, _, h, _, _ => by simp [sizeEmptyB] at h
  | .union a b, M + 1, hM, h, x, hx => by
    simp only [sizeEmptyB, Bool.and_eq_true] at h
    simp only [eset, ESet.union] at hx
    have ha := sizeEmpty_sound (outer := outer) (pt := pt) (g := g) a M (by simp at hM <;> omega) h.1 x
    have hb := sizeEmpty_sound (outer := outer) (pt := pt) (g := g) b M (by simp at hM <;> omega) h.2 x
    rcases hx with (hx | hx) | (hx | hx | hx | hx) <;> simp_all
  | .inter a b, M + 1, hM, h, x, hx => by
    simp only [sizeEmptyB, Bool.or_eq_true] at h
    simp only [eset, ESet.inter] at hx
    rcases h with h | h
    · have ha := sizeEmpty_sound (outer := outer) (pt := pt) (g := g) a M (by simp at hM <;> omega) h x
      rcases hx with hx | hx | hx <;> simp_all
    · have hb := sizeEmpty_sound (outer := outer) (pt := pt) (g := g) b M (by simp at hM <;> omega) h x
      rcases hx with hx | hx | hx <;> simp_all
  | .except a b, M + 1, hM, h, x, hx => by
    simp only [sizeEmptyB] at h
    simp only [eset, ESet.except] at hx
    have ha := sizeEmpty_sound (outer := outer) (pt := pt) (g := g) a M (by simp at hM <;> omega) h x
    rcases hx with hx | hx | hx <;> simp_all
  | .union .., 0, hM, _, _, _ | .inter .., 0, hM, _, _, _ | .except .., 0, hM, _, _, _ => by simp at hM

theorem onlySingles_mem {sc : Scope} {outer : List Frame} {pt : Ty} {g : Val → Prop} {x : Val} :
    ∀ (es : ElemSet) (M : Nat), n + 11 + sizeOf es ≤ M → charsNonEmptyB.onlySingles es = true →
      (eset E H M sc outer pt g es).r x ∨ (eset E H M sc outer pt g es).a x →
      ∃ s ∈ esVals es, ∃ M', n + 9 ≤ M' ∧ ∃ w, evalVal E M' sc s w ∧ eqv E M' sc pt x w
  | .elem (.single v), M + 2, hM, _, hx => by
    simp only [eset, elem, ESet.fixed, or_self] at hx
    obtain ⟨-, w, hw, hq⟩ := hx
    exact ⟨v, by simp [esVals, elVals], M, by simp at hM <;> omega, w, hw, hq⟩
  | .elem (.single _), 0, hM, _, _ | .elem (.single _), 1, hM, _, _ => by simp at hM <;> omega
  | .elem (.contained ..), _, _, h, _ | .elem (.range ..), _, _, h, _ | .elem (.size _), _, _, h, _
  | .elem (.typeC _), _, _, h, _ | .elem (.from_ _), _, _, h, _ | .elem (.withComponent _), _, _, h, _
  | .elem (.withComponents ..), _, _, h, _ | .elem (.pattern _), _, _, h, _
  | .elem (.settings _), _, _, h, _ | .allExcept _, _, _, h, _ => by simp [charsNonEmptyB.onlySingles] at h
  | .union a b, M + 1, hM, h, hx => by
    simp only [charsNonEmptyB.onlySingles, Bool.and_eq_true] at h
    simp only [eset, ESet.union] at hx
    have ha := onlySingles_mem (sc := sc) (outer := outer) (pt := pt) (g := g) (x := x) a M (by simp at hM <;> omega) h.1
    have hb := onlySingles_mem (sc := sc) (outer := outer) (pt := pt) (g := g) (x := x) b M (by simp at hM <;> omega) h.2
    have lift : ∀ {l : List Val}, (∃ s ∈ l, ∃ M', n + 9 ≤ M' ∧ ∃ w, evalVal E M' sc s w ∧ eqv E M' sc pt x w) →
        l ⊆ esVals (.union a b) → ∃ s ∈ esVals (.union a b), ∃ M', n + 9 ≤ M' ∧ ∃ w, evalVal E M' sc s w ∧ eqv E M' sc pt x w :=
      fun ⟨s, hs, rest⟩ hsub => ⟨s, hsub hs, rest⟩
    have sa : esVals a ⊆ esVals (.union a b) := by intro v hv; simp [esVals, hv]
    have sb : esVals b ⊆ esVals (.union a b) := by intro v hv; simp [esVals, hv]
    rcases hx with (hx | hx) | (hx | hx | hx | hx)
    · exact lift (ha (.inl hx)) sa
    · exact lift (hb (.inl hx)) sb
    · exact lift (ha (.inl hx)) sa
    · exact lift (hb (.inl hx)) sb
    · exact lift (ha (.inr hx)) sa
    · exact lift (hb (.inr hx)) sb
  | .inter a b, M + 1, hM, h, hx => by
    simp only [charsNonEmptyB.onlySingles, Bool.and_eq_true] at h
    simp only [eset, ESet.inter] at hx
    have ha := onlySingles_mem (sc := sc) (outer := outer) (pt := pt) (g := g) (x := x) a M (by simp at hM <;> omega) h.1
    have hx' : (eset E H M sc outer pt g a).r x ∨ (eset E H M sc outer pt g a).a x := by
      rcases hx with hx | hx | hx
      · exact .inl hx.1
      · exact .inl hx.1
      · exact .inr hx.1
    obtain ⟨s, hs, rest⟩ := ha hx'
    exact ⟨s, by simp [esVals, hs], rest⟩
  | .except a b, M + 1, hM, h, hx => by
    simp only [charsNonEmptyB.onlySingles, Bool.and_eq_true] at h
    simp only [eset, ESet.except] at hx
    have ha := onlySingles_mem (sc := sc) (outer := outer) (pt := pt) (g := g) (x := x) a M (by simp at hM <;> omega) h.1
    have hx' : (eset E H M sc outer pt g a).r x ∨ (eset E H M sc outer pt g a).a x := by
      rcases hx with hx | hx | hx
      · exact .inl hx.1
      · exact .inl hx.1
      · exact .inr hx.1
    obtain ⟨s, hs, rest⟩ := ha hx'
    exact ⟨s, by simp [esVals, hs], rest⟩
  | .union .., 0, hM, _, _ | .inter .., 0, hM, _, _ | .except .., 0, hM, _, _ => by simp at hM

theorem filterMap_length_eq {α β} {f : α → Option β} {l : List α}
    (h : (l.filterMap f).length = l.length) : ∀ x ∈ l, (f x).isSome := by
  simpa using h


theorem nonEmpty_cons {t : Ty} {root : ElemSet} {x : Bool} {adds : Option ElemSet}
    (hne : ∀ n', n ≤ n' → NonEmpty E H n' sc (.constrained t (.mk root x adds))) (N : Nat) :
    ∃ M, N ≤ M ∧ ∃ v, (sem E H (M + 1) sc [] t).root v ∧
      ((eset E H M sc [] t (sem E H (M + 1) sc [] t).root root).a v ∨
        ∃ a, adds = some a ∧ (eset E H M sc [] t (sem E H (M + 1) sc [] t).root a).a v) := by
  obtain ⟨v, hv⟩ := hne (N + n + 2) (by omega)
  rw [show N + n + 2 = (N + n) + 1 + 1 by omega] at hv
  simp only [sem] at hv
  have hroot := cons_sub_parent (.inr hv)
  simp only [cons, VSet.keepExt, VSet.ofSpecs] at hv
  refine ⟨N + n, by omega, v, hroot, ?_⟩
  rcases hv with hv | ⟨e, he, hv⟩
  · exact .inl hv
  · cases adds with
    | none => simp at he
    | some a => simp at he; subst he; exact .inr ⟨a, rfl, hv⟩

theorem constraintKindsOkB_of {s : Ty} (hup : ∀ n', n ≤ n' → ConstraintsOk E H n' sc s)
    (hne : ∀ n', n ≤ n' → NonEmpty E H n' sc s) : constraintKindsOkB E n sc s = true := by
  cases s with
  | constrained t c =>
    unfold constraintKindsOkB
    simp only [Bool.and_eq_true]
    refine ⟨consOkB_of fun N => ⟨max N n, by omega, hup (max N n) (by omega)⟩, ?_⟩
    cases c with
    | mk root x adds =>
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases hi : isIntTyV E n sc t with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_or]
          by_contra hf
          simp only [Bool.not_eq_true] at hf
          unfold isIntTyV at hi
          split at hi
          · rename_i s' nb hb
            obtain ⟨d, hd⟩ := sem_builtinV (H := H) hb
            obtain ⟨M, hM, v, hroot, hin⟩ := nonEmpty_cons hne (n + d + 14 + sizeOf root + sizeOf adds)
            obtain ⟨outer', w', hbase⟩ := hd (M + 1 - d) (by omega) [] v false
              (by rw [show M + 1 - d + d = M + 1 by omega]; simpa [VSet.at] using hroot)
            obtain ⟨M3, hM3⟩ : ∃ M3, M + 1 - d = M3 + 1 := ⟨M - d, by omega⟩
            rw [hM3] at hbase
            have : ∃ j, v = .int j := by cases w' <;> simpa [VSet.at, sem, VSet.plain] using hbase
            obtain ⟨j, rfl⟩ := this
            have hpt : EqTy E n sc t := ⟨s', _, builtin_of_builtinV hb, trivial⟩
            exact intNonEmpty_sound hf hpt.eqv (M := M) (by omega) hroot hin
          · simp at hi
      · split
        · rename_i s' k hb
          by_contra hf
          simp only [Bool.not_eq_true] at hf
          unfold charsNonEmptyB at hf
          split at hf
          · simp at hf
          · rename_i hos
            simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hos
            dsimp only at hf
            split at hf
            · simp at hf
            · rename_i hlen
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
              simp only [Bool.not_eq_false', List.all_eq_true, beq_iff_eq] at hf
              have hpt : EqTy E n sc t := ⟨s', _, hb, trivial⟩
              have hres := filterMap_length_eq hlen
              obtain ⟨M, hM, v, hroot, hin⟩ := nonEmpty_cons hne (n + 14 + sizeOf root + sizeOf adds)
              -- `v` is the value of one of the single values
              have hsing : ∃ sv ∈ esVals root ++ (adds.map esVals).getD [], ∃ M', n + 9 ≤ M' ∧ ∃ w,
                  evalVal E M' sc sv w ∧ eqv E M' sc t v w := by
                rcases hin with hin | ⟨a, rfl, hin⟩
                · obtain ⟨sv, hsv, rest⟩ := onlySingles_mem (n := n) (sc := sc) (outer := []) (pt := t) root M (by omega) hos.1 (.inr hin)
                  exact ⟨sv, by simp [hsv], rest⟩
                · obtain ⟨sv, hsv, rest⟩ := onlySingles_mem (n := n) (sc := sc) (outer := []) (pt := t) a M (by have := Option.some.sizeOf_spec a; omega)
                    (by simpa using hos.2) (.inr hin)
                  exact ⟨sv, by simp [hsv], rest⟩
              obtain ⟨sv, hsv, M', hM', w, hw, hq⟩ := hsing
              rw [hpt.eqv M' (by omega)] at hq; subst hq
              obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp (hres sv hsv)
              rw [(evalVal_of_charsOfV hcs M' hM' v).mp hw] at hroot hin
              have hcand := hf cs (List.mem_filterMap.mpr ⟨sv, hsv, hcs⟩)
              have hD := charsInES_decides (H := H) (outer := []) hroot hpt.eqv root M (by omega)
              cases adds with
              | none =>
                simp only [Dec.ofSpecs, Option.map_none] at hcand
                rcases hin with hin | ⟨a, ha, -⟩
                · exact hD.2.some_false hcand hin
                · simp at ha
              | some a =>
                have hDa := charsInES_decides (H := H) (outer := []) hroot hpt.eqv a M (by have := Option.some.sizeOf_spec a; omega)
                simp only [Dec.ofSpecs, Option.map_some] at hcand
                have := (hD.2.orB hDa.2).some_false hcand
                rcases hin with hin | ⟨a', ha', hin⟩
                · exact this (.inl hin)
                · simp at ha'; subst ha'; exact this (.inr hin)
        · rfl
      · by_contra hf
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hf
        obtain ⟨M, hM, v, hroot, hin⟩ := nonEmpty_cons hne (n + 14 + sizeOf root + sizeOf adds)
        rcases hin with hin | ⟨a, rfl, hin⟩
        · exact sizeEmpty_sound (n := n) (sc := sc) (outer := []) (pt := t) root M (by omega) hf.1 v (.inr hin)
        · exact sizeEmpty_sound (n := n) (sc := sc) (outer := []) (pt := t) a M (by have := Option.some.sizeOf_spec a; omega) (by simpa using hf.2) v (.inr hin)
    | _ => simp
  | _ => rfl

theorem serialValsOkB_of {s : Ty} (hup : ∀ n', n ≤ n' → ConstraintsOk E H n' sc s) :
    serialValsOkB E n sc s = true := by
  cases s with
  | constrained t c =>
    simp only [serialValsOkB]
    exact intConsValsOkB_of fun N => ⟨max N n, by omega, hup (max N n) (by omega)⟩
  | _ => rfl

theorem componentsOfOkB_of {s : Ty} (h : ComponentsOk E H n sc s) : componentsOfOkB E n sc s = true := by
  cases s with
  | sequence r e r2 =>
    simp only [ComponentsOk] at h
    simp only [componentsOfOkB, List.all_eq_true]
    intro c hc
    cases c with
    | mk => rfl
    | componentsOf t =>
      have ht : t ∈ componentsOfTypes r e r2 := by
        simp only [componentsOfTypes, List.mem_filterMap]; exact ⟨_, hc, rfl⟩
      obtain ⟨sc', r', e', r2', hb, -⟩ := h.2.2 t ht
      simp [hb]
  | set r e r2 =>
    simp only [ComponentsOk] at h
    simp only [componentsOfOkB, List.all_eq_true]
    intro c hc
    cases c with
    | mk => rfl
    | componentsOf t =>
      have ht : t ∈ componentsOfTypes r e r2 := by
        simp only [componentsOfTypes, List.mem_filterMap]; exact ⟨_, hc, rfl⟩
      obtain ⟨sc', r', e', r2', hb, -⟩ := h.2.2 t ht
      simp [hb]
  | _ => rfl

theorem presenceOkB_of {s : Ty} (hup : ∀ n', n ≤ n' → ConstraintsOk E H n' sc s) :
    presenceOkB E n sc s = true := by
  cases s with
  | constrained t c =>
    cases c with
    | mk r x a =>
      simp only [ConstraintsOk] at hup
      have key : ∀ l ∈ esWithPres r ++ (a.map esWithPres).getD [], ∃ x' ncs,
          l = (ncs.map fun (nm, _, p) => (nm, p)) ∧ ElemOk E H (n + 1) sc t false (.withComponents x' ncs) := by
        intro l hl
        rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨x', ncs, hel, rfl⟩ := mem_esWithPres hl
          exact ⟨x', ncs, rfl, elemOk_of_cons hup (.inl hel)⟩
        · cases a with
          | none => simp at hl
          | some b =>
            obtain ⟨x', ncs, hel, rfl⟩ := mem_esWithPres (by simpa using hl)
            exact ⟨x', ncs, rfl, elemOk_of_cons hup (.inr ⟨b, rfl, hel⟩)⟩
      -- the PRESENT and ABSENT each WITH COMPONENTS writes are on OPTIONAL components
      have hok : ∀ sc' bt, builtin E n sc t = some (sc', bt) →
          ∀ l ∈ esWithPres r ++ (a.map esWithPres).getD [], ∃ ncs,
            l = (ncs.map fun (nm, _, p) => (nm, p)) ∧
            PresenceOk E n (innerTarget sc' bt).1 (innerTarget sc' bt).2 ncs := by
        intro sc' bt hb l hl
        obtain ⟨x', ncs, rfl, hel⟩ := key l hl
        unfold ElemOk at hel
        obtain ⟨sc'', bt', row, hb', -, -, -, -, -, -, hp⟩ := hel
        rw [hb] at hb'; cases hb'
        exact ⟨ncs, rfl, hp⟩
      simp only [presenceOkB]
      rcases n with _ | k
      · simp [builtin]
      have hseq : ∀ sc' ro e r2, (∀ nm p, (∃ l ∈ esWithPres r ++ (a.map esWithPres).getD [], (nm, p) ∈ l) →
            p.isEmpty = false → ∃ en ∈ entries E (k + 1) sc' ro e r2, en.name = nm ∧ en.presence = .optional) →
          ((esWithPres r ++ (a.map esWithPres).getD []).all fun l => l.all fun (nm, p) =>
            (match p with | .present | .absent => false | _ => true) ||
            (entries E (k + 1) sc' ro e r2).any (fun en => en.name == nm && !en.presence.isMandatory) ||
            !(entries E (k + 1) sc' ro e r2).any (·.name == nm)) = true := by
        intro sc' ro e r2 h
        simp only [List.all_eq_true]
        rintro l hl ⟨nm, p⟩ hp
        cases p with
        | present | absent =>
          obtain ⟨en, hen, h1, h2⟩ := h nm _ ⟨l, hl, hp⟩ rfl
          simp only [Bool.false_or, Bool.or_eq_true, List.any_eq_true]
          left; exact ⟨en, hen, by simp [h1, h2, Presence.isMandatory]⟩
        | _ => rfl
      split
      · rename_i sc' ro e r2 hb
        refine (Bool.or_eq_true _ _).mpr (.inr (hseq sc' ro e r2 fun nm p ⟨l, hl, hp⟩ he => ?_))
        obtain ⟨ncs, rfl, hpo⟩ := hok _ _ hb l hl
        simp only [innerTarget, PresenceOk, builtin] at hpo
        obtain ⟨⟨nm', oc, p'⟩, hm, he'⟩ := List.mem_map.1 hp
        simp only [Prod.mk.injEq] at he'; obtain ⟨rfl, rfl⟩ := he'
        exact hpo.2 _ hm he
      · rename_i sc' ro e r2 hb
        refine (Bool.or_eq_true _ _).mpr (.inr (hseq sc' ro e r2 fun nm p ⟨l, hl, hp⟩ he => ?_))
        obtain ⟨ncs, rfl, hpo⟩ := hok _ _ hb l hl
        simp only [innerTarget, PresenceOk, builtin] at hpo
        obtain ⟨⟨nm', oc, p'⟩, hm, he'⟩ := List.mem_map.1 hp
        simp only [Prod.mk.injEq] at he'; obtain ⟨rfl, rfl⟩ := he'
        exact hpo _ hm he
      · rfl
    | _ => rfl
  | _ => rfl

end TypeRules

theorem typeChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String} {sc : Scope}
    {s : Ty} (h : TypeOk E H n sc s) (hup' : ∀ n', n ≤ n' → TypeOk E H n' sc s)
    (hs : sizeOf s < n) : typeChecks E n m nm sc s = [] := by
  have hup : ∀ n', n ≤ n' → ConstraintsOk E H n' sc s := fun n' hn' => (hup' n' hn').constraints
  have h0 : namesOkB E n sc s = true := namesOkB_of h.names
  have h1 : tagsOkB E n sc s = true := tagsOkB_of h.tags
  have h2 : autoAdditionsOkB sc s = true := autoAdditionsOkB_of h.autoAdditions
  have h3 : refsOkB E n sc s = true := refsOkB_of h.refs
  have h4 : typeFromObjectsOkB E n sc s = true := typeFromObjectsOkB_of h.typeFromObjects
  have h5 : argsOkB E n sc s = true := argsOkB_of h.args hs
  have h6 : classRefsOkB E n sc s = true := classRefsOkB_of h.classRefs
  have h7 : defaultRefsOkB E n sc s = true := defaultRefsOkB_of h.components hs
  have h8 : consRefsOkB E n sc s = true := consRefsOkB_of h.constraints hs
  have h9 : typeFromObjectsTableB E n sc s = true := typeFromObjectsTableB_of h.typeFromObjectsTable
  have h10 : tableRefsOkB E n sc s = true := tableRefsOkB_of h.tableRefs
  have h11 : tableClassB E n sc s = true := tableClassB_of h.tableClass
  have h12 : tableOnFieldB E n sc s = true := tableOnFieldB_of h.tableOnField
  have h13 : defaultsInTypeB E n sc s = true := defaultsInTypeB_of (fun n' hn' => (hup' n' hn').components) hs
  have h14 : serialValsOkB E n sc s = true := serialValsOkB_of hup
  have h15 : innerNamesOkB E n sc s = true := innerNamesOkB_of hup
  have h16 : constraintKindsOkB E n sc s = true := constraintKindsOkB_of hup (fun n' hn' => (hup' n' hn').nonEmpty)
  have h17 : componentsOfOkB E n sc s = true := componentsOfOkB_of h.components
  have h18 : universalTagOkB s = true := universalTagOkB_of h.universalTag
  have h19 : presenceOkB E n sc s = true := presenceOkB_of hup
  unfold typeChecks
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  simp only [↓reduceIte, List.append_nil]

theorem atWalkB_of {E : Env} {n : Nat} {os : ObjSet} : ∀ {sc : Scope} {t : Ty} {path : List String},
    AtWalk E n os sc t path → atRefOkB.walk E n os sc t path = true
  | _, _, [], _ => by simp [atRefOkB.walk]
  | sc, t, [id], h => by
    simp only [AtWalk] at h
    obtain ⟨cs, x, csc, ct, os', h1, h2, h3, h4⟩ := h
    simp only [atRefOkB.walk, h1, h2, h3, ObjSet.differs, h4]
    refine (Bool.or_eq_true _ _).mpr (.inr ?_)
    split <;> simp_all
  | sc, t, id :: id2 :: rest, h => by
    simp only [AtWalk] at h
    obtain ⟨cs, x, csc, ct, h1, h2, h3⟩ := h
    simp only [atRefOkB.walk, h1, h2]
    exact (Bool.or_eq_true _ _).mpr (.inr (atWalkB_of h3))

theorem atRefOkB_of {E : Env} {n : Nat} {sc : Scope} {anc : List Ty} {os : ObjSet} {a : AtRef}
    (h : ∃ p, atParent anc a = some p ∧ AtWalk E n os sc p a.path) : atRefOkB E n sc anc os a = true := by
  obtain ⟨p, hp, hw⟩ := h
  show (match atParent anc a with | none => false | some p => atRefOkB.walk E n os sc p a.path) = true
  rw [hp]; exact atWalkB_of hw

theorem atPathsOkB_gen {E : Env} {n : Nat} {sc : Scope} (t : Ty) : ∀ (anc : List Ty),
    (∀ anc' s, Within anc t anc' s → ∀ u os refs, s = .constrained u (.table os refs) →
      ∀ a ∈ refs, ∃ p, atParent anc' a = some p ∧ AtWalk E n os sc p a.path) →
    atPathsOkB E n sc anc t = true := by
  induction t using WellFounded.induction (measure (sizeOf : Ty → Nat)).wf with
  | _ t ih =>
  intro anc h
  have ih' : ∀ u, sizeOf u < sizeOf t → ∀ anc, (∀ anc' s, Within anc u anc' s → ∀ u os refs,
      s = .constrained u (.table os refs) → ∀ a ∈ refs, ∃ p, atParent anc' a = some p ∧
        AtWalk E n os sc p a.path) → atPathsOkB E n sc anc u = true := fun u hu => ih u hu
  cases t with
  | sequence r e r2 =>
    unfold atPathsOkB
    simp only [List.all_eq_true]
    rintro ⟨c, hc⟩ -
    cases c with
    | mk nm ct p =>
      simp only
      have := Comp.sizeOf_lt hc
      exact ih' ct (by simp at this ⊢; omega) _ fun anc' s hw => h anc' s (.seqComp hc hw)
    | componentsOf _ => rfl
  | set r e r2 =>
    unfold atPathsOkB
    simp only [List.all_eq_true]
    rintro ⟨c, hc⟩ -
    cases c with
    | mk nm ct p =>
      simp only
      have := Comp.sizeOf_lt hc
      exact ih' ct (by simp at this ⊢; omega) _ fun anc' s hw => h anc' s (.setComp hc hw)
    | componentsOf _ => rfl
  | choice r e =>
    unfold atPathsOkB
    simp only [List.all_eq_true]
    rintro ⟨al, ha⟩ -
    cases al with
    | mk nm at' =>
      simp only
      have := Alt.sizeOf_lt ha
      exact ih' at' (by simp at this ⊢; omega) _ fun anc' s hw => h anc' s (.alt ha hw)
  | sequenceOf et =>
    unfold atPathsOkB
    exact ih' et (by simp) _ fun anc' s hw => h anc' s (.seqOf hw)
  | setOf et =>
    unfold atPathsOkB
    exact ih' et (by simp) _ fun anc' s hw => h anc' s (.setOf hw)
  | tagged tg k u =>
    unfold atPathsOkB
    exact ih' u (by simp) _ fun anc' s hw => h anc' s (.tagged hw)
  | constrained u c =>
    unfold atPathsOkB
    simp only [Bool.and_eq_true]
    refine ⟨?_, ih' u (by simp; omega) _ fun anc' s hw => h anc' s (.constrained hw)⟩
    cases c with
    | table os refs =>
      simp only [List.all_eq_true]
      intro a ha
      exact atRefOkB_of (h anc _ .here u os refs rfl a ha)
    | _ => rfl
  | _ => unfold atPathsOkB; rfl

theorem atPathsOkB_of {E : Env} {n : Nat} {sc : Scope} {t : Ty} (h : AtPathsOk E n sc t) :
    atPathsOkB E n sc [] t = true :=
  atPathsOkB_gen t [] h

theorem siteChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String} {sc : Scope}
    {t : Ty} (hup : ∀ n', n ≤ n' → SiteOk E H n' sc t) (ht : sizeOf t < n) :
    siteChecks E n m nm sc t = [] := by
  have h := hup n (Nat.le_refl n)
  have ha : atPathsOkB E n sc [] t = true := atPathsOkB_of h.atPaths
  simp only [siteChecks, ha, ↓reduceIte, List.nil_append, List.flatMap_eq_nil_iff]
  intro s hs
  have ho := occurs_of_mem_occurrences hs
  exact typeChecks_nil (h.types s ho) (fun n' hn' => (hup n' hn').types s ho)
    (Nat.lt_of_le_of_lt ho.sizeOf_le ht)

/-! ### A parameterized body: the checker knows less than the spec -/

section ValuesLess

variable {E : Env} {n : Nat} {sc1 sc2 vsc1 vsc2 : Scope}

theorem find_rel {α β γ : Type} [BEq γ] {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hk : ∀ x y, R x y → f x = g y) {key : γ} : ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
    (l1.find? (f · == key) = none ∧ l2.find? (g · == key) = none) ∨
      ∃ x y, l1.find? (f · == key) = some x ∧ l2.find? (g · == key) = some y ∧ R x y
  | [], [], .nil => .inl ⟨rfl, rfl⟩
  | x :: r1, y :: r2, .cons h hr => by
    simp only [List.find?_cons, hk x y h]
    split
    · exact .inr ⟨x, y, rfl, rfl, h⟩
    · exact find_rel hk hr

theorem refMapsB_less (hsc : ScLess sc1 sc2) (hvsc : ScLess vsc1 vsc2) {t : Ty} {v : Val}
    (h : refMapsB E n sc2 t v vsc2 = true) : refMapsB E n sc1 t v vsc1 = true := by
  cases v with
  | ref mn nm args =>
    simp only [refMapsB] at h ⊢
    cases hr : resolveValTy E n vsc1 mn nm args with
    | none => rfl
    | some p =>
      obtain ⟨usc1, u⟩ := p
      obtain ⟨usc2, hr2, hus⟩ := resolveValTy_less hvsc hr
      rw [hr2] at h
      cases hb : (builtin E n sc1 t).bind (mapName ·.2) with
      | none => rfl
      | some pn =>
        have hb2 : (builtin E n sc2 t).bind (mapName ·.2) = some pn := by
          simp only [Option.bind_eq_some_iff] at hb ⊢
          obtain ⟨⟨s1, b⟩, h1, h2⟩ := hb
          obtain ⟨s2, h1', -⟩ := builtin_less hsc h1
          exact ⟨(s2, b), h1', h2⟩
        rw [hb2] at h
        simp only at h ⊢
        cases hq : (builtin E n usc1 u).bind (mapName ·.2) with
        | none => rfl
        | some q =>
          have hq2 : (builtin E n usc2 u).bind (mapName ·.2) = some q := by
            simp only [Option.bind_eq_some_iff] at hq ⊢
            obtain ⟨⟨s1, b⟩, h1, h2⟩ := hq
            obtain ⟨s2, h1', -⟩ := builtin_less hus h1
            exact ⟨(s2, b), h1', h2⟩
          rw [hq2] at h; exact h
  | _ => simp [refMapsB]

theorem valMapsB_less (hvsc : ScLess vsc1 vsc2) (v : Val) : ∀ {sc1 sc2 : Scope} {t : Ty}, ScLess sc1 sc2 →
    valMapsB E n sc2 t v vsc2 = true → valMapsB E n sc1 t v vsc1 = true := by
  induction v using WellFounded.induction (measure (sizeOf : Val → Nat)).wf with
  | _ v ih =>
  intro sc1 sc2 t hsc h
  rw [valMapsB.eq_def] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨refMapsB_less hsc hvsc h.1, ?_⟩
  have h2 := h.2
  cases v with
  | seq cs =>
    simp only at h2 ⊢
    cases hb : builtin E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
      rw [hb2] at h2
      have seqcase : ∀ (ro r2 : List Comp) (e : Option (List ExtAdd)),
          (!entriesKnown E n s2 ro e r2 || cs.attach.all fun ⟨(nm, w), _⟩ =>
            match (entries E n s2 ro e r2).find? (·.name == nm) with
            | some en => valMapsB E n en.scope en.ty w vsc2
            | none => true) = true →
          (!entriesKnown E n s1 ro e r2 || cs.attach.all fun ⟨(nm, w), _⟩ =>
            match (entries E n s1 ro e r2).find? (·.name == nm) with
            | some en => valMapsB E n en.scope en.ty w vsc1
            | none => true) = true := by
        intro ro r2 e hh
        cases hk : entriesKnown E n s1 ro e r2 with
        | false => rfl
        | true =>
          rw [entriesKnown_less hs hk] at hh
          simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hh ⊢
          intro ⟨⟨nm, w⟩, hmem⟩ hx
          have := hh ⟨⟨nm, w⟩, hmem⟩ hx
          have hes := (entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk
          rcases find_rel (f := (·.name)) (g := (·.name)) (key := nm) (fun x y hxy => hxy.2.1) hes with
            ⟨h1, -⟩ | ⟨x, y, h1, h2', hxy⟩
          · simp only [h1]
          · simp only [h1]; simp only [h2'] at this
            have hlt : sizeOf w < sizeOf (Val.seq cs) := by
              have := List.sizeOf_lt_of_mem hmem; simp at this ⊢; omega
            rw [← hxy.2.2.1] at this
            exact ih w hlt hxy.1 this
      cases b with
      | sequence ro e r2 => exact seqcase ro r2 e h2
      | set ro e r2 => exact seqcase ro r2 e h2
      | _ => rfl
  | seqOf vs | setOf vs =>
    simp only at h2 ⊢
    cases hb : builtin E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
      rw [hb2] at h2
      cases b with
      | sequenceOf el | setOf el =>
        simp only [List.all_eq_true] at h2 ⊢
        intro ⟨w, hmem⟩ hx
        exact ih w (by have := List.sizeOf_lt_of_mem hmem; show sizeOf w < _; simp; omega) hs (h2 ⟨w, hmem⟩ hx)
      | _ => rfl
  | choice a w =>
    simp only at h2 ⊢
    cases hb : builtin E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
      rw [hb2] at h2
      cases b with
      | choice ro ext =>
        simp only at h2 ⊢
        cases hf : findAlt (choiceAlts ro ext) a with
        | none => rfl
        | some alt =>
          rw [hf] at h2
          exact ih w (by show sizeOf w < _; simp) hs h2
      | _ => rfl
  | _ => rfl



theorem isIntTy_less (hsc : ScLess sc1 sc2) {t : Ty} (h : isIntTy E n sc1 t = true) : isIntTy E n sc2 t = true := by
  unfold isIntTy at h ⊢
  split at h
  · rename_i s nb hb
    obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
    rw [hb2]
  · cases h

theorem intValOkB_less (hsc : ScLess sc1 sc2) (hvsc : ScLess vsc1 vsc2) {t : Ty} {v : Val}
    (h : intValOkB E n sc2 t v vsc2 = true) : intValOkB E n sc1 t v vsc1 = true := by
  unfold intValOkB at h ⊢
  cases hi : isIntTy E n sc1 t with
  | false => rfl
  | true =>
    rw [isIntTy_less hsc hi] at h
    simp only [Bool.not_true, Bool.false_or] at h ⊢
    cases hv : intOfV E n vsc1 8 v with
    | none => rfl
    | some i =>
      rw [intOfV_less hvsc hv] at h
      simp only at h ⊢
      cases hn : intNotInTy E n 16 sc1 t i true with
      | false => rfl
      | true => rw [intNotInTy_less hsc hn] at h; cases h

theorem sizeValOkB_less (hsc : ScLess sc1 sc2) {t : Ty} {v : Val}
    (h : sizeValOkB E n sc2 t v = true) : sizeValOkB E n sc1 t v = true := by
  unfold sizeValOkB at h ⊢
  cases hs : v.size? with
  | none => rfl
  | some len =>
    cases hb : builtin E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, bt⟩ := p
      obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
      rw [hs, hb2] at h
      dsimp only at h ⊢
      split_ifs at h ⊢ with hnm
      · simp only [List.any_eq_true, Bool.not_eq_true'] at h ⊢
        obtain ⟨d, hd, hnd⟩ := h
        refine ⟨d, hd, ?_⟩
        cases hn : sizeNotInTy E n 16 sc1 t (len + d) true with
        | false => rfl
        | true => rw [sizeNotInTy_less hsc hn] at hnd; cases hnd
      · simp only [Bool.not_eq_true'] at h ⊢
        cases hn : sizeNotInTy E n 16 sc1 t len true with
        | false => rfl
        | true => rw [sizeNotInTy_less hsc hn] at h; cases h

theorem charsValOkB_less (hsc : ScLess sc1 sc2) (hvsc : ScLess vsc1 vsc2) {t : Ty} {v : Val}
    (h : charsValOkB E n sc2 t v vsc2 = true) : charsValOkB E n sc1 t v vsc1 = true := by
  unfold charsValOkB at h ⊢
  cases hb : builtin E n sc1 t with
  | none => rfl
  | some p =>
    obtain ⟨s1, bt⟩ := p
    obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
    rw [hb2] at h
    cases bt with
    | restricted k =>
      simp only at h ⊢
      cases hv : charsOfV E n vsc1 8 v with
      | none => rfl
      | some cs =>
        rw [charsOfV_less hvsc hv] at h
        simp only at h ⊢
        cases hn : charsNotInTy E n 16 sc1 t cs true with
        | false => rfl
        | true => rw [charsNotInTy_less hsc hn] at h; cases h
    | _ => rfl

theorem timeFmtOkB_less (hsc : ScLess sc1 sc2) (hvsc : ScLess vsc1 vsc2) {t : Ty} {v : Val}
    (h : timeFmtOkB E n sc2 t v vsc2 = true) : timeFmtOkB E n sc1 t v vsc1 = true := by
  unfold timeFmtOkB at h ⊢
  cases hb : builtinV E n sc1 t with
  | none => rfl
  | some p =>
    obtain ⟨s1, bt⟩ := p
    obtain ⟨s2, hb2, -⟩ := builtinV_less hsc hb
    rw [hb2] at h
    cases bt with
    | generalizedTime | utcTime =>
      simp only at h ⊢
      cases hv : charsOfV E n vsc1 8 v with
      | none => rfl
      | some cs => rw [charsOfV_less hvsc hv] at h; exact h
    | _ => rfl

theorem valSemB_less (hvsc : ScLess vsc1 vsc2) (v : Val) : ∀ {sc1 sc2 : Scope} {t : Ty}, ScLess sc1 sc2 →
    valSemB E n sc2 t v vsc2 = true → valSemB E n sc1 t v vsc1 = true := by
  induction v using WellFounded.induction (measure (sizeOf : Val → Nat)).wf with
  | _ v ih =>
  intro sc1 sc2 t hsc h
  rw [valSemB.eq_def] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨intValOkB_less hsc hvsc h1, sizeValOkB_less hsc h2⟩, charsValOkB_less hsc hvsc h3⟩,
    timeFmtOkB_less hsc hvsc h4⟩, ?_⟩
  cases v with
  | seq cs =>
    simp only at h5 ⊢
    cases hb : builtinV E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtinV_less hsc hb
      rw [hb2] at h5
      have seqcase : ∀ (ro r2 : List Comp) (e : Option (List ExtAdd)),
          (!entriesKnown E n s2 ro e r2 || cs.attach.all fun ⟨(nm, w), _⟩ =>
            !((entries E n s2 ro e r2).any (·.name == nm)) ||
              (entries E n s2 ro e r2).any fun en => en.name == nm && valSemB E n en.scope en.ty w vsc2) = true →
          (!entriesKnown E n s1 ro e r2 || cs.attach.all fun ⟨(nm, w), _⟩ =>
            !((entries E n s1 ro e r2).any (·.name == nm)) ||
              (entries E n s1 ro e r2).any fun en => en.name == nm && valSemB E n en.scope en.ty w vsc1) = true := by
        intro ro r2 e hh
        cases hk : entriesKnown E n s1 ro e r2 with
        | false => rfl
        | true =>
          rw [entriesKnown_less hs hk] at hh
          have hes := (entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk
          have hnames := entLess_names hes
          simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hh ⊢
          intro ⟨⟨nm, w⟩, hmem⟩ hx
          have := hh ⟨⟨nm, w⟩, hmem⟩ hx
          have hany : ((entries E n s1 ro e r2).any (·.name == nm)) = ((entries E n s2 ro e r2).any (·.name == nm)) := by
            have := congrArg (fun l => l.any (· == nm)) hnames
            simp only [List.any_map] at this; exact this
          simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this ⊢
          rcases this with h0 | ⟨en2, hen2, hname, hsem⟩
          · left; rw [hany]; exact h0
          · right
            obtain ⟨en1, hen1, hrel⟩ := forall₂_mem_right hes en2 hen2
            have hlt : sizeOf w < sizeOf (Val.seq cs) := by
              have := List.sizeOf_lt_of_mem hmem; simp at this ⊢; omega
            refine ⟨en1, hen1, by rw [hrel.2.1]; exact hname, ?_⟩
            rw [← hrel.2.2.1] at hsem
            exact ih w hlt hrel.1 hsem
      cases b with
      | sequence ro e r2 => exact seqcase ro r2 e h5
      | set ro e r2 => exact seqcase ro r2 e h5
      | _ => rfl
  | seqOf vs | setOf vs =>
    simp only at h5 ⊢
    cases hb : builtinV E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtinV_less hsc hb
      rw [hb2] at h5
      cases b with
      | sequenceOf el | setOf el =>
        simp only [List.all_eq_true] at h5 ⊢
        intro ⟨w, hmem⟩ hx
        exact ih w (by have := List.sizeOf_lt_of_mem hmem; show sizeOf w < _; simp; omega) hs (h5 ⟨w, hmem⟩ hx)
      | _ => rfl
  | choice a w =>
    simp only at h5 ⊢
    cases hb : builtinV E n sc1 t with
    | none => rfl
    | some p =>
      obtain ⟨s1, b⟩ := p
      obtain ⟨s2, hb2, hs⟩ := builtinV_less hsc hb
      rw [hb2] at h5
      cases b with
      | choice ro ext =>
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h5 ⊢
        rcases h5 with h0 | ⟨al, hal, hname, hsem⟩
        · left; exact h0
        · right; exact ⟨al, hal, hname, ih w (by show sizeOf w < _; simp) hs hsem⟩
      | _ => rfl
  | _ => rfl

theorem valOkB_less (hsc : ScLess sc1 sc2) (hvsc : ScLess vsc1 vsc2) {t : Ty} {v : Val}
    (h : valOkB E n sc2 t v vsc2 = true) : valOkB E n sc1 t v vsc1 = true := by
  simp only [valOkB, Bool.and_eq_true] at h ⊢
  exact ⟨valMapsB_less hvsc v hsc h.1, valSemB_less hvsc v hsc h.2⟩

theorem defaultsInTypeB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : defaultsInTypeB E n sc2 s = true) :
    defaultsInTypeB E n sc1 s = true := by
  have key : ∀ (c : Comp), (match c with
      | .mk _ t (.default_ v) => valOkB E n sc2 t v
      | _ => true) = true → (match c with
      | .mk _ t (.default_ v) => valOkB E n sc1 t v
      | _ => true) = true := by
    intro c hc
    split
    · rename_i nm t v; simp only at hc; exact valOkB_less hsc hsc hc
    · rfl
  cases s with
  | sequence r e r2 =>
    simp only [defaultsInTypeB, List.all_eq_true] at h ⊢; exact fun c hc => key c (h c hc)
  | set r e r2 =>
    simp only [defaultsInTypeB, List.all_eq_true] at h ⊢; exact fun c hc => key c (h c hc)
  | _ => rfl



theorem intPoints_less (hsc : ScLess sc1 sc2) {el : Elem} {i : Int} (h : i ∈ intPoints E n sc1 el) :
    i ∈ intPoints E n sc2 el := by
  cases el with
  | single v =>
    simp only [intPoints, Option.mem_toList] at h ⊢
    exact intOfV_less hsc h
  | range lo loOpen hi hiOpen =>
    simp only [intPoints, List.mem_append] at h ⊢
    rcases h with h | h
    · left
      cases loOpen <;> simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at h ⊢
      simp only [Option.mem_toList, Option.filter_eq_some_iff] at h ⊢
      obtain ⟨hl, hin⟩ := h
      cases lo with
      | val v =>
        refine ⟨intOfV_less hsc hl, ?_⟩
        cases hi with
        | val v' =>
          simp only [Option.any_eq_true] at hin ⊢
          obtain ⟨j, hj, hij⟩ := hin
          exact ⟨j, intOfV_less hsc hj, hij⟩
        | _ => exact hin
      | _ => cases hl
    · right
      cases hiOpen <;> simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at h ⊢
      simp only [Option.mem_toList, Option.filter_eq_some_iff] at h ⊢
      obtain ⟨hl, hin⟩ := h
      cases hi with
      | val v =>
        refine ⟨intOfV_less hsc hl, ?_⟩
        cases lo with
        | val v' =>
          simp only [Option.any_eq_true] at hin ⊢
          obtain ⟨j, hj, hij⟩ := hin
          exact ⟨j, intOfV_less hsc hj, hij⟩
        | _ => exact hin
      | _ => cases hl
  | _ => simp [intPoints] at h

theorem intConsValsOkB_less (hsc : ScLess sc1 sc2) {pt : Ty} {c : Constraint}
    (h : intConsValsOkB E n sc2 pt c = true) : intConsValsOkB E n sc1 pt c = true := by
  unfold intConsValsOkB at h ⊢
  cases hi : isIntTy E n sc1 pt with
  | false => rfl
  | true =>
    rw [isIntTy_less hsc hi] at h
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true, Bool.not_eq_true'] at h ⊢
    intro el hel i hip
    cases hn : intNotInTy E n 16 sc1 pt i false with
    | false => rfl
    | true =>
      have := h el hel i (intPoints_less hsc hip)
      rw [intNotInTy_less hsc hn] at this; cases this

theorem serialValsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : serialValsOkB E n sc2 s = true) :
    serialValsOkB E n sc1 s = true := by
  cases s with
  | constrained t c => simp only [serialValsOkB] at h ⊢; exact intConsValsOkB_less hsc h
  | _ => rfl



theorem innerTarget_less {s1 s2 : Scope} (hs : ScLess s1 s2) (bt : Ty) :
    ScLess (innerTarget s1 bt).1 (innerTarget s2 bt).1 ∧ (innerTarget s1 bt).2 = (innerTarget s2 bt).2 := by
  cases bt <;> simp [innerTarget, hs, ScLess.refl]

theorem structComps_less {t : Ty} (hsc : ScLess sc1 sc2) (hk : structKnown E n sc1 t = true) :
    List.Forall₂ CompLess (structComps E n sc1 t) (structComps E n sc2 t) ∨ structComps E n sc1 t = [] := by
  unfold structComps
  unfold structKnown at hk
  cases hb : builtin E n sc1 t with
  | none => right; rfl
  | some p =>
    obtain ⟨s1, b⟩ := p
    obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
    rw [hb] at hk; rw [hb2]
    left
    have entr : ∀ (ro r2 : List Comp) (e : Option (List ExtAdd)), entriesKnown E n s1 ro e r2 = true →
        List.Forall₂ CompLess ((entries E n s1 ro e r2).map fun en => (en.name, en.scope, en.ty))
          ((entries E n s2 ro e r2).map fun en => (en.name, en.scope, en.ty)) := by
      intro ro r2 e hk'
      exact forall₂_map (fun x y hxy => ⟨hxy.2.1, hxy.1, hxy.2.2.1⟩)
        ((entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk')
    cases b with
    | sequence ro e r2 => exact entr ro r2 e hk
    | set ro e r2 => exact entr ro r2 e hk
    | choice ro e =>
      exact forall₂_map (R := fun a b => a = b) (fun x y hxy => by subst hxy; exact ⟨rfl, hs, rfl⟩)
        (forall₂_refl' (fun _ => rfl) _)
    | _ => exact .nil

theorem structKnown_less {t : Ty} (hsc : ScLess sc1 sc2) (hk : structKnown E n sc1 t = true)
    (hne : structComps E n sc1 t ≠ []) : structKnown E n sc2 t = true := by
  unfold structKnown at hk ⊢
  unfold structComps at hne
  cases hb : builtin E n sc1 t with
  | none => rw [hb] at hne; exact absurd rfl hne
  | some p =>
    obtain ⟨s1, b⟩ := p
    obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
    rw [hb] at hk; rw [hb2]
    cases b with
    | sequence ro e r2 => exact entriesKnown_less hs hk
    | set ro e r2 => exact entriesKnown_less hs hk
    | _ => rfl

/-- What `consOkB_less` says, for each kind of syntax. -/
def ConsLessP (E : Env) (n : Nat) (c : Constraint) : Prop :=
  ∀ {sc1 sc2 : Scope} {pt : Ty} {inPA : Bool}, ScLess sc1 sc2 →
    consOkB E n sc2 pt inPA c = true → consOkB E n sc1 pt inPA c = true
def ESetLessP (E : Env) (n : Nat) (es : ElemSet) : Prop :=
  ∀ {sc1 sc2 : Scope} {pt : Ty} {inPA : Bool}, ScLess sc1 sc2 →
    esOkB E n sc2 pt inPA es = true → esOkB E n sc1 pt inPA es = true
def ElemLessP (E : Env) (n : Nat) (el : Elem) : Prop :=
  ∀ {sc1 sc2 : Scope} {pt : Ty} {inPA : Bool}, ScLess sc1 sc2 →
    elemOkB E n sc2 pt inPA el = true → elemOkB E n sc1 pt inPA el = true

theorem consOkB_less_all : ∀ k : Nat, (∀ c : Constraint, sizeOf c < k → ConsLessP E n c) ∧
    (∀ es : ElemSet, sizeOf es < k → ESetLessP E n es) ∧ (∀ el : Elem, sizeOf el < k → ElemLessP E n el)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
    obtain ⟨ihc, ihes, ihel⟩ := consOkB_less_all k
    refine ⟨fun c hs => ?_, fun es hs => ?_, fun el hs => ?_⟩
    · intro sc1 sc2 pt inPA hsc h
      cases c with
      | mk root x adds =>
        unfold consOkB at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        refine ⟨ihes root (by simp at hs; omega) hsc h.1, ?_⟩
        cases adds with
        | none => rfl
        | some a => exact ihes a (by simp at hs; omega) hsc h.2
      | contents t enc =>
        unfold consOkB at h ⊢
        cases hb : builtin E n sc1 pt with
        | none => rfl
        | some p =>
          obtain ⟨s1, b⟩ := p
          obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
          rw [hb2] at h; revert h; cases b <;> simp
      | table os refs => unfold consOkB; rfl
      | userDefined => unfold consOkB; rfl
    · intro sc1 sc2 pt inPA hsc h
      cases es with
      | elem el => unfold esOkB at h ⊢; exact ihel el (by simp at hs; omega) hsc h
      | union a b | inter a b | except a b =>
        unfold esOkB at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ihes a (by simp at hs; omega) hsc h.1, ihes b (by simp at hs; omega) hsc h.2⟩
      | allExcept b => unfold esOkB at h ⊢; exact ihes b (by simp at hs; omega) hsc h
    · intro sc1 sc2 pt inPA hsc h
      unfold elemOkB at h ⊢
      cases hb : builtin E n sc1 pt with
      | none => rfl
      | some p =>
        obtain ⟨s1, bt⟩ := p
        obtain ⟨s2, hb2, hs2⟩ := builtin_less hsc hb
        rw [hb2] at h
        simp only at h ⊢
        cases hr : rowOf bt with
        | none => rfl
        | some r =>
          rw [hr] at h
          simp only [Bool.and_eq_true] at h ⊢
          refine ⟨h.1, ?_⟩
          have h3 := h.2
          cases el with
          | single v => exact refMapsB_less hsc hsc h3
          | range lo lo' hi hi' =>
            simp only [Bool.and_eq_true, Bool.or_eq_true] at h3 ⊢
            obtain ⟨⟨h1, h2⟩, h4⟩ := h3
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rcases h1 with h1 | h1
              · exact .inl h1
              · right
                try simp only [Bool.and_eq_true] at h1 ⊢
                constructor
                · cases lo with
                  | val v =>
                    have h11 := h1.1
                    simp only at h11 ⊢
                    cases hv : charsOfV E n sc1 8 v with
                    | none => rfl
                    | some cs => rw [charsOfV_less hsc hv] at h11; exact h11
                  | _ => rfl
                · cases hi with
                  | val v =>
                    have h12 := h1.2
                    simp only at h12 ⊢
                    cases hv : charsOfV E n sc1 8 v with
                    | none => rfl
                    | some cs => rw [charsOfV_less hsc hv] at h12; exact h12
                  | _ => rfl
            · cases lo with
              | val v => exact refMapsB_less hsc hsc h2
              | _ => rfl
            · cases hi with
              | val v => exact refMapsB_less hsc hsc h4
              | _ => rfl
          | contained t' x =>
            simp only at h3 ⊢
            cases hb' : (builtin E n sc1 t').bind (rowOf ·.2) with
            | none => rfl
            | some r' =>
              have : (builtin E n sc2 t').bind (rowOf ·.2) = some r' := by
                simp only [Option.bind_eq_some_iff] at hb' ⊢
                obtain ⟨⟨s, b⟩, h1, h2⟩ := hb'
                obtain ⟨s', h1', -⟩ := builtin_less hsc h1
                exact ⟨(s', b), h1', h2⟩
              rw [this] at h3; exact h3
          | size c =>
            simp only [Bool.and_eq_true] at h3 ⊢
            exact ⟨⟨h3.1.1, ihc c (by simp at hs; omega) hsc h3.1.2⟩, intConsValsOkB_less hsc h3.2⟩
          | from_ c =>
            simp only [Bool.and_eq_true] at h3 ⊢
            exact ⟨h3.1, ihc c (by simp at hs; omega) hsc h3.2⟩
          | withComponent c =>
            simp only at h3 ⊢
            cases bt with
            | sequenceOf et => exact ihc c (by simp at hs; omega) hs2 h3
            | setOf et => exact ihc c (by simp at hs; omega) hs2 h3
            | _ => exact h3
          | withComponents isPartial ncs =>
            simp only [Bool.and_eq_true, Bool.or_eq_true] at h3 ⊢
            obtain ⟨hnd, h3⟩ := h3
            refine ⟨hnd, ?_⟩
            obtain ⟨hisc, hit⟩ := innerTarget_less hs2 bt
            generalize innerTarget s1 bt = it1 at hisc hit ⊢
            generalize innerTarget s2 bt = it2 at hisc hit h3
            obtain ⟨isc1, it⟩ := it1
            obtain ⟨isc2, it'⟩ := it2
            simp only at hisc hit h3 ⊢
            subst hit
            by_cases hne : structComps E n isc1 it = []
            · left; left; simp [hne]
            by_cases hk : structKnown E n isc1 it = true
            · right
              have hk2 := structKnown_less hisc hk hne
              rcases structComps_less (E := E) (n := n) (t := it) hisc hk with hrel | hnil
              · simp only [hk2, Bool.not_true, Bool.false_eq_true, false_or] at h3
                rcases h3 with (h3 | h3) | h3
                · exfalso
                  have := hrel.length_eq
                  simp only [List.isEmpty_iff] at h3
                  rw [h3] at this; simp at this; exact hne this
                · exact h3.elim
                · simp only [List.all_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h3 ⊢
                  intro ⟨⟨nm, oc, p⟩, hmem⟩ hx
                  obtain ⟨⟨y, hy, hny⟩, hc⟩ := h3 ⟨⟨nm, oc, p⟩, hmem⟩ hx
                  obtain ⟨x1, hx1, hxy⟩ := forall₂_mem_right hrel y hy
                  refine ⟨⟨x1, hx1, by rw [hxy.1]; exact hny⟩, ?_⟩
                  cases oc with
                  | none => rfl
                  | some c =>
                    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc ⊢
                    obtain ⟨y2, hy2, hny2, hc2⟩ := hc
                    obtain ⟨x2, hx2, hxy2⟩ := forall₂_mem_right hrel y2 hy2
                    refine ⟨x2, hx2, by rw [hxy2.1]; exact hny2, ?_⟩
                    have hlt : sizeOf c < k := by
                      have := List.sizeOf_lt_of_mem hmem; simp at hs this; omega
                    rw [← hxy2.2.2] at hc2
                    exact ihc c hlt hxy2.2.1 hc2
              · exact absurd hnil hne
            · left; right; simpa using hk
          | settings ps => exact h3
          | _ => exact h3

theorem consOkB_less (hsc : ScLess sc1 sc2) {pt : Ty} {inPA : Bool} {c : Constraint}
    (h : consOkB E n sc2 pt inPA c = true) : consOkB E n sc1 pt inPA c = true :=
  (consOkB_less_all (sizeOf c + 1)).1 c (by omega) hsc h



/-- When the scope that knows less finds an INTEGER element set empty, so does the other: its
decision for every number is "not in", and the other decides alike. -/
theorem intNonEmptyB_less (hsc : ScLess sc1 sc2) {root : ElemSet} {adds : Option ElemSet}
    (h : intNonEmptyB E n sc1 root adds = false) : intNonEmptyB E n sc2 root adds = false := by
  have hall : ∀ j : Int, (Dec.ofSpecs (intInES E n sc1 j root) (adds.map (intInES E n sc1 j))).2 = some false := by
    intro j
    simp only [intNonEmptyB, Bool.not_eq_false', List.all_eq_true, beq_iff_eq] at h
    set ks := (esVals root ++ (adds.map esVals).getD []).filterMap (intOfV E n sc1 8) with hks
    obtain ⟨c, hc, hside⟩ := exists_candidate ks j
    have hfalse := h c hc
    have hroot := intInES_profile (E := E) (n := n) (sc := sc1) hside root (fun v hv k hk => by
      rw [hks]; exact List.mem_filterMap.mpr ⟨v, by simp [hv], hk⟩)
    rw [← hfalse]
    simp only [Dec.ofSpecs, hroot]
    cases adds with
    | none => rfl
    | some a =>
      simp only [Option.map_some]
      rw [intInES_profile (E := E) (n := n) (sc := sc1) hside a (fun v hv k hk => by
        rw [hks]; exact List.mem_filterMap.mpr ⟨v, by simp [hv], hk⟩)]
  have hall2 : ∀ j : Int, (Dec.ofSpecs (intInES E n sc2 j root) (adds.map (intInES E n sc2 j))).2 = some false := by
    intro j
    have hle : OLe (Dec.ofSpecs (intInES E n sc1 j root) (adds.map (intInES E n sc1 j))).2
        (Dec.ofSpecs (intInES E n sc2 j root) (adds.map (intInES E n sc2 j))).2 := by
      have := decCons_le (es1 := intInES E n sc1 j) (es2 := intInES E n sc2 j)
        (intInES_le hsc j) (.mk root false adds)
      simpa [decCons] using this.2
    exact hle false (hall j)
  simp only [intNonEmptyB, Bool.not_eq_false', List.all_eq_true, beq_iff_eq]
  intro i _
  exact hall2 i

theorem sizeEmptyB_less (hsc : ScLess sc1 sc2) : ∀ {es : ElemSet},
    sizeEmptyB E n sc1 es = true → sizeEmptyB E n sc2 es = true
  | .elem (.size (.mk r x a)), h => by
    simp only [sizeEmptyB, Bool.not_eq_true'] at h ⊢
    exact intNonEmptyB_less hsc h
  | .union a b, h => by
    simp only [sizeEmptyB, Bool.and_eq_true] at h ⊢
    exact ⟨sizeEmptyB_less hsc h.1, sizeEmptyB_less hsc h.2⟩
  | .inter a b, h => by
    simp only [sizeEmptyB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact .inl (sizeEmptyB_less hsc h)
    · exact .inr (sizeEmptyB_less hsc h)
  | .except a b, h => by simp only [sizeEmptyB] at h ⊢; exact sizeEmptyB_less hsc h
  | .elem (.size (.contents ..)), h | .elem (.size (.table ..)), h | .elem (.size .userDefined), h
  | .elem (.single _), h | .elem (.contained ..), h | .elem (.range ..), h | .elem (.typeC _), h
  | .elem (.from_ _), h | .elem (.withComponent _), h | .elem (.withComponents ..), h
  | .elem (.pattern _), h | .elem (.settings _), h | .allExcept _, h => by simp [sizeEmptyB] at h

theorem charsNonEmptyB_less (hsc : ScLess sc1 sc2) {root : ElemSet} {adds : Option ElemSet}
    (h : charsNonEmptyB E n sc1 root adds = false) : charsNonEmptyB E n sc2 root adds = false := by
  unfold charsNonEmptyB at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i hos
    rw [if_neg hos]
    split at h
    · cases h
    · rename_i hlen
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      have hres := filterMap_length_eq hlen
      set vals := esVals root ++ (adds.map esVals).getD [] with hvals
      have heq : vals.filterMap (charsOfV E n sc2 8) = vals.filterMap (charsOfV E n sc1 8) := by
        apply List.filterMap_congr
        intro x hx
        obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp (hres x hx)
        rw [hcs, charsOfV_less hsc hcs]
      rw [heq, if_neg (by simp [hlen])]
      simp only [Bool.not_eq_false', List.all_eq_true, beq_iff_eq] at h ⊢
      intro cs hcs
      have hle : OLe (Dec.ofSpecs (charsInES E n sc1 cs root) (adds.map (charsInES E n sc1 cs))).2
          (Dec.ofSpecs (charsInES E n sc2 cs root) (adds.map (charsInES E n sc2 cs))).2 := by
        have := decCons_le (es1 := charsInES E n sc1 cs) (es2 := charsInES E n sc2 cs)
          (charsInES_le hsc cs) (.mk root false adds)
        simpa [decCons] using this.2
      exact hle false (h cs hcs)

theorem constraintKindsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : constraintKindsOkB E n sc2 s = true) :
    constraintKindsOkB E n sc1 s = true := by
  cases s with
  | constrained t c =>
    unfold constraintKindsOkB at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨consOkB_less hsc h.1, ?_⟩
    have h2 := h.2
    cases c with
    | mk root x adds =>
      simp only [Bool.and_eq_true] at h2 ⊢
      obtain ⟨⟨hi, hc⟩, hs⟩ := h2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases hiv : isIntTyV E n sc1 t with
        | false => rfl
        | true =>
          have hiv2 : isIntTyV E n sc2 t = true := by
            unfold isIntTyV at hiv ⊢
            split at hiv
            · rename_i s nb hb
              obtain ⟨s2, hb2, -⟩ := builtinV_less hsc hb
              rw [hb2]
            · cases hiv
          rw [hiv2] at hi
          simp only [Bool.not_true, Bool.false_or] at hi ⊢
          cases hn : intNonEmptyB E n sc1 root adds with
          | true => rfl
          | false => rw [intNonEmptyB_less hsc hn] at hi; cases hi
      · cases hb : builtin E n sc1 t with
        | none => rfl
        | some p =>
          obtain ⟨s1, bt⟩ := p
          obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
          rw [hb2] at hc
          cases bt with
          | restricted k =>
            simp only at hc ⊢
            cases hn : charsNonEmptyB E n sc1 root adds with
            | true => rfl
            | false => rw [charsNonEmptyB_less hsc hn] at hc; cases hc
          | _ => rfl
      · simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at hs ⊢
        by_contra hne
        push Not at hne
        obtain ⟨h1, h2'⟩ := hne
        have e1 := sizeEmptyB_less hsc (by simpa using h1)
        have e2 : adds.all (sizeEmptyB E n sc2) = true := by
          cases adds with
          | none => rfl
          | some a => simp at h2' ⊢; exact sizeEmptyB_less hsc h2'
        rcases hs with hs | hs
        · rw [e1] at hs; cases hs
        · rw [e2] at hs; cases hs
    | _ => rfl
  | _ => rfl



theorem argKindOk_of_fits {H : ContentsHook} {sc : Scope} {g : Option ParamGov} {a : Arg}
    (h : ArgFits E H n sc g a) : ArgKindOk g a := by
  cases g with
  | none => cases a <;> simp_all [ArgFits, ArgKindOk]
  | some g => cases g <;> cases a <;> simp_all [ArgFits, ArgKindOk]

theorem withDummies_less {m : Module} : ∀ {ps : List Param} {args : List Arg},
    List.Forall₂ (fun p a => ArgKindOk p.governor a) ps args →
    ScLess (Scope.withDummies m ps) (bindParams m ps args (.ofModule m))
  | ps, args, h => by
    unfold Scope.withDummies bindParams
    refine .mk ?_
    induction h with
    | nil => exact .nil
    | cons hk _ ih => exact .dummy hk ih

end ValuesLess

/-- The rules on one type, read in a scope that knows less, where the scope that knows more passes
them (and the spec's tag rule holds there). -/
theorem typeChecks_less {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String} {sc1 sc2 : Scope}
    {s : Ty} (hsc : ScLess sc1 sc2) (htags : TagsOk E H n sc2 s) (h : typeChecks E n m nm sc2 s = []) :
    typeChecks E n m nm sc1 s = [] := by
  unfold typeChecks at h ⊢
  simp only [List.append_eq_nil_iff, ite_eq_left_iff, reduceCtorEq, imp_false, Bool.not_eq_false, Decidable.not_not] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩, h18⟩, h19⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨namesOkB_less hsc h0, tagsOkB_of_less hsc (Nat.le_refl n) htags⟩,
    autoAdditionsOkB_less hsc h2⟩, refsOkB_less hsc h3⟩, typeFromObjectsOkB_less hsc h4⟩, argsOkB_less hsc h5⟩,
    classRefsOkB_less hsc h6⟩, defaultRefsOkB_less hsc h7⟩, consRefsOkB_less hsc h8⟩,
    typeFromObjectsTableB_less hsc h9⟩, tableRefsOkB_less hsc h10⟩, tableClassB_less hsc h11⟩,
    tableOnFieldB_less hsc h12⟩, defaultsInTypeB_less hsc h13⟩, serialValsOkB_less hsc h14⟩,
    innerNamesOkB_less hsc h15⟩, constraintKindsOkB_less hsc h16⟩, componentsOfOkB_less hsc h17⟩, h18⟩,
    presenceOkB_less hsc h19⟩

theorem siteChecks_less {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String} {sc1 sc2 : Scope}
    {t : Ty} (hsc : ScLess sc1 sc2) (htags : ∀ s ∈ occurrences t, TagsOk E H n sc2 s)
    (h : siteChecks E n m nm sc2 t = []) : siteChecks E n m nm sc1 t = [] := by
  unfold siteChecks at h ⊢
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h ⊢
  refine ⟨?_, fun s hs => typeChecks_less hsc (htags s hs) (h.2 s hs)⟩
  have h1 := h.1
  split at h1
  · rename_i ha
    rw [if_pos (atPathsOkB_less hsc t [] ha)]
  · cases h1

/-- A parameterized body: the checker reads it with its dummies bound to nothing, the spec with
actual parameters its governors allow (the same at every fuel). What the checker decides with less
knowledge it decides alike with the actual parameters, where the spec holds. -/
theorem siteChecks_param_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {pa : ParamAssign}
    {args : List Arg} {t : Ty} (hup : ∀ n', n ≤ n' → ParamBodyOk E H n' m pa args) (hhas : pa.Has t)
    (ht : sizeOf t < n) :
    siteChecks E n m pa.name (Scope.withDummies m pa.paramList) t = [] := by
  have hP := hup n (Nat.le_refl n)
  have hsc : ScLess (Scope.withDummies m pa.paramList) (bindParams m pa.paramList args (.ofModule m)) :=
    withDummies_less (hP.1.imp fun p a h => argKindOk_of_fits h)
  have hsite : ∀ n', n ≤ n' → SiteOk E H n' (bindParams m pa.paramList args (.ofModule m)) t :=
    fun n' hn' => (hup n' hn').2 t hhas
  exact siteChecks_less hsc (fun s hs => ((hsite n (Nat.le_refl n)).types s (occurs_of_mem_occurrences hs)).tags)
    (siteChecks_nil hsite ht)

/-! ### Parameters, classes, type and value assignments -/

section Assignments

variable {E : Env} {H : ContentsHook} {n : Nat} {sc : Scope}

theorem classDefOkB_of {c : ClassRef} (h : FieldClassesOk E n sc c) : classDefOkB E n sc c = true := by
  cases c with
  | defn fs syn =>
    simp only [FieldClassesOk] at h
    simp only [classDefOkB, List.all_eq_true]
    intro f hf
    have hf' := h f hf
    split
    · rename_i mn name args; simp_all
    · rename_i mn name args; simp_all
    · rename_i p
      obtain ⟨o, ho⟩ := hf'
      exact List.any_eq_true.mpr ⟨_, ho, by simp⟩
    · rename_i p
      obtain ⟨o, ho⟩ := hf'
      exact List.any_eq_true.mpr ⟨_, ho, by simp⟩
    · rfl
  | _ => rfl

theorem paramGovsOkB_of {m : Module} {pa : ParamAssign} (h : ParamGovsOk E H n m pa) :
    paramGovsOkB E n (.ofModule m) pa = true := by
  simp only [paramGovsOkB, List.all_eq_true]
  intro p hp
  have h1 := h p hp
  split
  · rename_i mn name args hg
    rw [hg] at h1
    rcases h1 with h1 | ⟨q, hq, hqn⟩
    · simp [h1]
    · simp only [Bool.or_eq_true]; right; exact List.any_eq_true.mpr ⟨q, hq, by simp [hqn]⟩
  · rename_i t hg
    rw [hg] at h1
    simp only [List.all_eq_true]
    intro s hs
    exact refsOkB_of (h1 s (occurs_of_mem_occurrences hs))
  · rfl

theorem tyChainB_of : ∀ {k : Nat} {sc : Scope} {t : Ty}, RefChainEnds E n k sc t →
    tyChainB E n k sc t = true
  | 0, _, _, h => by simp [RefChainEnds] at h
  | k + 1, sc, t, h => by
    cases t with
    | ref name =>
      simp only [RefChainEnds] at h
      simp only [tyChainB]
      split
      · rename_i sc' t' hr
        rcases h with h | h
        · simp [h]
        · simp [tyChainB_of (h sc' t' hr)]
      · rfl
    | extRef mn name =>
      simp only [RefChainEnds] at h
      simp only [tyChainB]
      split
      · rename_i sc' t' hr; exact tyChainB_of (h sc' t' hr)
      · rfl
    | tagged _ _ u => simp only [RefChainEnds] at h; simp only [tyChainB]; exact tyChainB_of h
    | constrained u _ => simp only [RefChainEnds] at h; simp only [tyChainB]; exact tyChainB_of h
    | _ => rfl

theorem valChainB_of : ∀ {k : Nat} {sc : Scope} {v w : Val}, evalVal E k sc v w → k ≤ n →
    valChainB E n k sc v = true
  | 0, _, _, _, h, _ => by simp [evalVal] at h
  | k + 1, sc, v, w, h, hk => by
    cases v with
    | ref mn name args =>
      cases args with
      | nil =>
        unfold evalVal at h
        split at h
        · rename_i sc' v' hr
          simp only [valChainB, resolveVal_mono hr (by omega : k ≤ n), Bool.or_eq_true]
          right; exact valChainB_of h (by omega)
        · exact h.elim
      | cons a as => rfl
    | _ => rfl

/-- A name that resolves in a parameterized body's scope is a dummy of it, or one its module
assigns or imports. -/
theorem knows_of_resolveIn {α : Type} {E : Env} {n : Nat} {m : Module} {ps : List Param} {as : List Arg}
    {caller : Scope} {name : String} {args : List Arg}
    {fromArg : Arg → Option ParamGov → Scope → Option (Scope × α)} {fromModule : Module → Option α}
    {fromParam : ParamAssign → Option (List Param × α)}
    (hmod : (fromModule m).isSome → name ∈ m.assignedNames)
    (h : (resolveIn E n (bindParams m ps as caller) none name args fromArg fromModule fromParam).isSome) :
    ((ps.map (·.name)).contains name || (Scope.ofModule m).knows none name) = true := by
  have hk : m.imports.any (·.1 == name) = true ∨ name ∈ m.assignedNames →
      (Scope.ofModule m).knows none name = true := by
    rintro (hi | hi) <;>
      simp [Scope.knows, Scope.ofModule, Scope.mod, Scope.bound, Scope.binds, hi]
  unfold resolveIn at h
  simp only [Bool.or_eq_true]
  cases args with
  | nil =>
    cases hb : (bindParams m ps as caller).bound name with
    | some x =>
      left
      simp only [Scope.bound, Scope.binds, bindParams, Option.map_eq_some_iff] at hb
      obtain ⟨y, hy, -⟩ := hb
      have hm := List.mem_of_find?_eq_some hy
      have hn : y.1 = name := by simpa using List.find?_some hy
      simp only [List.mem_map, List.contains_iff_mem] at hm ⊢
      obtain ⟨⟨p, a⟩, hpa, rfl⟩ := hm
      exact ⟨p, List.of_mem_zip hpa |>.1, hn⟩
    | none =>
      right
      simp only [hb, Option.isSome_map] at h
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
      simp only [bindParams, Scope.mod] at hr
      rcases Env.resolveWith_some hr with hg | hi
      · exact hk (.inr (hmod hg))
      · exact hk (.inl hi)
  | cons a as' =>
    right
    simp only [Option.isSome_map] at h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    simp only [bindParams, Scope.mod] at hr
    rcases Env.resolveWith_some hr with hg | hi
    · apply hk; right
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hg
      obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hx
      have hm := List.mem_of_find?_eq_some hy
      have hn : y.name = name := by simpa using List.find?_some hy
      simp only [Module.assignedNames, List.mem_append]
      exact .inr (List.mem_map.mpr ⟨y, hm, hn⟩)
    · exact hk (.inl hi)

/-- The body of a parameterized type names what exists, or dummies: from the spec's reading with
actual parameters. -/
theorem paramBodyOkB_of {m : Module} {pa : ParamAssign}
    (hP : ∃ args, ParamBodyOk E H n m pa args) : paramBodyOkB E n (.ofModule m) pa = true := by
  cases pa with
  | type nm ps body =>
    obtain ⟨args, -, hall⟩ := hP
    have hsite := hall body rfl
    simp only [paramBodyOkB, List.all_eq_true]
    intro t ht
    have hok := hsite.types t (occurs_of_mem_occurrences ht)
    simp only [ParamAssign.paramList] at hok
    have hcls : ∀ {c}, (fun m : Module => (m.classes.find? (·.1 == c)).map (·.2)) m |>.isSome →
        c ∈ m.assignedNames := by
      intro c hc
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hx
      have hn : y.1 = c := by simpa using List.find?_some hy
      simp only [Module.assignedNames, List.mem_append]
      exact .inl (.inl (.inl (.inr (List.mem_map.mpr ⟨y, List.mem_of_find?_eq_some hy, hn⟩))))
    split
    · rename_i x
      have h := hok.refs
      simp only [RefsOk] at h
      refine knows_of_resolveIn (fun hc => ?_) h
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc
      simp only [Module.lookup, Option.map_eq_some_iff] at hy
      obtain ⟨z, hz, -⟩ := hy
      have hn : z.1 = x := by simpa using List.find?_some hz
      simp only [Module.assignedNames, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (List.mem_map.mpr ⟨z, List.mem_of_find?_eq_some hz, hn⟩)))))
    · rename_i c args' path
      have h := hok.classRefs
      simp only [ClassRefsOk] at h
      obtain ⟨cf, hcf, -⟩ := h
      rcases n with _ | k
      · simp [classFields] at hcf
      simp only [classFields] at hcf
      split at hcf
      · rename_i sc'' c' hr
        have := knows_of_resolveIn hcls (Option.isSome_iff_exists.mpr ⟨_, hr⟩)
        simp only [Bool.or_eq_true] at this ⊢
        rcases this with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · simp at hcf
    · rename_i c args'
      have h := hok.classRefs
      simp only [ClassRefsOk] at h
      have := knows_of_resolveIn hcls h
      simp only [Bool.or_eq_true] at this ⊢
      rcases this with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rename_i c a' path
      have h := hok.typeFromObjects
      simp only [TypeFromObjectsOk] at h
      have h := h _ .ref
      simp only [ORef.Resolves] at h
      refine knows_of_resolveIn (fun hc => ?_) h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hx
      have hn : y.1 = c := by simpa using List.find?_some hy
      simp only [Module.assignedNames, List.mem_append]
      exact .inl (.inr (List.mem_map.mpr ⟨y, List.mem_of_find?_eq_some hy, hn⟩))
    · rfl
  | _ => rfl

end Assignments

theorem paramChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module}
    (hV : m.ValidAt E H n) (hP : ∀ pa ∈ m.params, ∃ args, ParamBodyOk E H n m pa args) (hm : sizeOf m < n) :
    paramChecks E n m = [] := by
  simp only [paramChecks, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  constructor
  · intro pa hpa; simp [paramGovsOkB_of (hV.paramGovs pa hpa)]
  · intro pa hpa; simp [paramBodyOkB_of (hP pa hpa)]

theorem classChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module}
    (hV' : ∀ n', n ≤ n' → m.ValidAt E H n') (hm : sizeOf m < n) : classChecks E n m = [] := by
  have hV := hV' n (Nat.le_refl n)
  simp only [classChecks, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  constructor
  · rintro ⟨nm, c⟩ hc
    have hok := hV.classes nm c hc
    cases c with
    | defn fs syn =>
      simp only [List.filterMap_eq_nil_iff]
      intro f hf
      split
      · rename_i fnm t u v
        obtain ⟨-, hmaps⟩ := hok.fieldDefaults fnm t u v hf
        have hsz : sizeOf t + sizeOf v < n := by
          have h1 := List.sizeOf_lt_of_mem hf; have h2 := List.sizeOf_lt_of_mem hc
          cases m; simp at h1 h2 hm ⊢; omega
        have hin : ValIn E H (.ofModule m) v (.ofModule m) t := ValIn.of_eventually fun M hM =>
          (((hV' M hM).classes nm _ hc).fieldDefaults fnm t u v hf).1
        simp [valOkB_of hin hmaps (by omega)]
      · rfl
    | _ => rfl
  · rintro ⟨nm, c⟩ hc
    simp [classDefOkB_of (hV.classes nm c hc).fieldClasses]

/-! ### Objects and object sets -/

section Objects

variable {E : Env} {n : Nat} {sc : Scope}

theorem evalObj_defn {k : Nat} {cf : Option (Scope × List FieldSpec)} {ss} {x : ObjV}
    (h : evalObj E (k + 1) sc cf (.defn ss) x) :
    x = ⟨sc, ss, (cf.getD (sc, [])).1, (cf.getD (sc, [])).2⟩ := by
  simp only [evalObj] at h; exact h

theorem objFieldsOkB_of {cls : ClassRef} {o : Obj}
    (h : ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.FieldsSet) (hn : 0 < n) :
    objFieldsOkB E n sc cls o = true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases o with
  | defn ss =>
    simp only [objFieldsOkB]
    split
    · rename_i csc fs hcf
      have := h _ (by simp only [evalObj, hcf]; rfl)
      simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      intro f hf
      by_cases hm : f.mandatory = true
      · obtain ⟨st, hst⟩ := this f (by simpa using hf) hm
        right; exact List.any_eq_true.mpr ⟨_, hst, by simp⟩
      · left; simpa using hm
    · rfl
  | _ => rfl

theorem objValRefsOkB_of {cls : ClassRef} {o : Obj}
    (h : ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.SettingRefsOk E n) (hn : 0 < n) :
    objValRefsOkB E n sc cls o = true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases o with
  | defn ss =>
    have := h _ (by simp only [evalObj]; rfl)
    simp only [objValRefsOkB, Bool.or_eq_true, List.all_eq_true]
    right
    rintro ⟨f, st⟩ hst
    have h1 := this f st hst
    cases st with
    | value v => exact valRefsOkB_of_ok h1
    | object ob => exact oelemsRefsOkB_of h1
    | objectSet s => exact objSetRefsOkB_of h1
    | _ => rfl
  | _ => rfl

theorem oelemsFieldsOkB_of {cls : ClassRef} : ∀ {e : OElems},
    (∀ o, OElemsWrites e o → objFieldsOkB E n sc cls o = true) → oelemsFieldsOkB E n sc cls e = true
  | .obj o, h => by simp only [oelemsFieldsOkB]; exact h o .obj
  | .set (.spec (some r) _ (some a)), h => by
    simp only [oelemsFieldsOkB, Bool.and_eq_true]
    exact ⟨oelemsFieldsOkB_of fun o ho => h o (.root ho), oelemsFieldsOkB_of fun o ho => h o (.addition ho)⟩
  | .set (.spec (some r) _ none), h => by
    simp only [oelemsFieldsOkB]; exact oelemsFieldsOkB_of fun o ho => h o (.root ho)
  | .set (.spec none _ (some a)), h => by
    simp only [oelemsFieldsOkB]; exact oelemsFieldsOkB_of fun o ho => h o (.addition ho)
  | .set (.spec none _ none), _ | .set (.ref ..), _ | .fromObjects .., _ => by simp [oelemsFieldsOkB]
  | .union a b, h => by
    simp only [oelemsFieldsOkB, Bool.and_eq_true]
    exact ⟨oelemsFieldsOkB_of fun o ho => h o (.unionL ho), oelemsFieldsOkB_of fun o ho => h o (.unionR ho)⟩
  | .inter a b, h => by
    simp only [oelemsFieldsOkB, Bool.and_eq_true]
    exact ⟨oelemsFieldsOkB_of fun o ho => h o (.interL ho), oelemsFieldsOkB_of fun o ho => h o (.interR ho)⟩
  | .except a b, h => by
    simp only [oelemsFieldsOkB, Bool.and_eq_true]
    exact ⟨oelemsFieldsOkB_of fun o ho => h o (.exceptL ho), oelemsFieldsOkB_of fun o ho => h o (.exceptR ho)⟩

theorem oelemsValRefsOkB_of {cls : ClassRef} : ∀ {e : OElems},
    (∀ o, OElemsWrites e o → objValRefsOkB E n sc cls o = true) → oelemsValRefsOkB E n sc cls e = true
  | .obj o, h => by simp only [oelemsValRefsOkB]; exact h o .obj
  | .set (.spec (some r) _ (some a)), h => by
    simp only [oelemsValRefsOkB, Bool.and_eq_true]
    exact ⟨oelemsValRefsOkB_of fun o ho => h o (.root ho), oelemsValRefsOkB_of fun o ho => h o (.addition ho)⟩
  | .set (.spec (some r) _ none), h => by
    simp only [oelemsValRefsOkB]; exact oelemsValRefsOkB_of fun o ho => h o (.root ho)
  | .set (.spec none _ (some a)), h => by
    simp only [oelemsValRefsOkB]; exact oelemsValRefsOkB_of fun o ho => h o (.addition ho)
  | .set (.spec none _ none), _ | .set (.ref ..), _ | .fromObjects .., _ => by simp [oelemsValRefsOkB]
  | .union a b, h => by
    simp only [oelemsValRefsOkB, Bool.and_eq_true]
    exact ⟨oelemsValRefsOkB_of fun o ho => h o (.unionL ho), oelemsValRefsOkB_of fun o ho => h o (.unionR ho)⟩
  | .inter a b, h => by
    simp only [oelemsValRefsOkB, Bool.and_eq_true]
    exact ⟨oelemsValRefsOkB_of fun o ho => h o (.interL ho), oelemsValRefsOkB_of fun o ho => h o (.interR ho)⟩
  | .except a b, h => by
    simp only [oelemsValRefsOkB, Bool.and_eq_true]
    exact ⟨oelemsValRefsOkB_of fun o ho => h o (.exceptL ho), oelemsValRefsOkB_of fun o ho => h o (.exceptR ho)⟩

/-! ## UNIQUE (X.681 9.7) -/

theorem pairsOk_false {key : Scope × List (String × Setting) → String → Option VKey}
    {differ : Scope × List (String × Setting) → Scope × List (String × Setting) → Bool} {f : String} :
    ∀ {objs : List (Scope × List (String × Setting))}, uniqueOkB.pairsOk key differ f objs = false →
      ∃ a ∈ objs, ∃ b ∈ objs, ∃ x, key a f = some x ∧ key b f = some x ∧ differ a b = true
  | [], h => by simp [uniqueOkB.pairsOk] at h
  | a :: rest, h => by
    rw [uniqueOkB.pairsOk, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · rw [List.all_eq_false] at h
      obtain ⟨b, hb, hab⟩ := h
      split at hab
      · rename_i x y hx hy
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, Decidable.not_not,
          Bool.not_eq_false] at hab
        obtain ⟨rfl, hd⟩ := hab
        exact ⟨a, by simp, b, by simp [hb], x, hx, hy, hd⟩
      · simp at hab
    · obtain ⟨a', ha', b', hb', x, h1, h2, h3⟩ := pairsOk_false h
      exact ⟨a', by simp [ha'], b', by simp [hb'], x, h1, h2, h3⟩

theorem evalVal_of_valKey : ∀ {k : Nat} {sc : Scope} {v : Val} {key : VKey},
    valKey E n sc k v = some key → ∀ M, n + k + 1 ≤ M → ∀ w, evalVal E M sc v w ↔ w = key.toVal
  | k, sc, .int j, key, h, M + 1, hM, w => by simp [valKey] at h; subst h; simp [evalVal, VKey.toVal]
  | k, sc, .oid j, key, h, M + 1, hM, w => by simp [valKey] at h; subst h; simp [evalVal, VKey.toVal]
  | k, sc, .bool j, key, h, M + 1, hM, w => by simp [valKey] at h; subst h; simp [evalVal, VKey.toVal]
  | k, sc, .enum j, key, h, M + 1, hM, w => by simp [valKey] at h; subst h; simp [evalVal, VKey.toVal]
  | k + 1, sc, .ref mn nm args, key, h, M + 1, hM, w => by
    simp only [valKey] at h
    split at h
    · rename_i s v' hr
      simp only [evalVal, resolveVal_mono hr (by omega : n ≤ M)]
      exact evalVal_of_valKey h M (by omega) w
    · simp at h
  | 0, sc, .ref .., _, h, _, _, _ => by simp [valKey] at h
  | _, _, .real _, _, h, _, _, _ | _, _, .bits _, _, h, _, _, _ | _, _, .octets _, _, h, _, _, _
  | _, _, .null, _, h, _, _, _ | _, _, .seq _, _, h, _, _, _ | _, _, .seqOf _, _, h, _, _, _
  | _, _, .setOf _, _, h, _, _, _ | _, _, .choice .., _, h, _, _, _ | _, _, .iri _, _, h, _, _, _
  | _, _, .chars _, _, h, _, _, _ | _, _, .regChars _, _, h, _, _, _ | _, _, .time _, _, h, _, _, _
  | _, _, .open_ .., _, h, _, _, _ | _, _, .fromObject .., _, h, _, _, _ | _, _, .raw _, _, h, _, _, _ => by
    simp [valKey] at h
  | _, _, .int _, _, _, 0, hM, _ | _, _, .oid _, _, _, 0, hM, _ | _, _, .bool _, _, _, 0, hM, _
  | _, _, .enum _, _, _, 0, hM, _ => by omega

theorem VKey.toVal_inj {x y : VKey} (h : x.toVal = y.toVal) : x = y := by
  cases x <;> cases y <;> simp_all [VKey.toVal]

/-- The objects `setObjs` and `objSetObjs` list are objects of the set, with their scopes and
settings, at enough fuel. -/
theorem objs_mem (k : Nat) :
    (∀ (e : OElems) (sc : Scope) (objs : List (Scope × List (String × Setting))),
      setObjs E n k sc e = some objs → ∀ o ∈ objs, ∀ cf N, n + 2 * k + 2 ≤ N →
        ∃ x, (oelems E N sc cf e).a x ∧ x.sc = o.1 ∧ x.settings = o.2) ∧
    (∀ (os : ObjSet) (sc : Scope) (objs : List (Scope × List (String × Setting))),
      objSetObjs E n k sc os = some objs → ∀ o ∈ objs, ∀ cf N, n + 2 * k + 3 ≤ N →
        ∃ x, (evalObjSet E N sc cf os).a x ∧ x.sc = o.1 ∧ x.settings = o.2) := by
    induction k with
    | zero =>
      have hset : ∀ (e : OElems) (sc : Scope) objs, setObjs E n 0 sc e = some objs → False := by
        intro e sc objs h; cases e <;> simp [setObjs] at h
      refine ⟨fun e sc objs h => (hset e sc objs h).elim, fun os sc objs h o ho cf N hN => ?_⟩
      cases os with
      | spec r ext a =>
        cases r <;> cases a <;> simp [objSetObjs] at h
        · subst h; simp at ho
        · exact (hset _ sc objs h).elim
        · exact (hset _ sc objs h).elim
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨x, hx, -⟩ := h; exact (hset _ sc x hx).elim
      | ref mn nm args => simp [objSetObjs] at h
    | succ k ih =>
      obtain ⟨ihs, iho⟩ := ih
      have hset : ∀ (e : OElems) (sc : Scope) (objs : List (Scope × List (String × Setting))),
          setObjs E n (k + 1) sc e = some objs → ∀ o ∈ objs, ∀ cf N, n + 2 * (k + 1) + 2 ≤ N →
            ∃ x, (oelems E N sc cf e).a x ∧ x.sc = o.1 ∧ x.settings = o.2 := by
        intro e sc objs h o ho cf N hN
        obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
        cases e with
        | obj ob =>
          cases ob with
          | defn ss =>
            simp only [setObjs, Option.some.injEq] at h; subst h
            simp only [List.mem_singleton] at ho; subst ho
            obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
            simp only [oelems, evalObj]
            exact ⟨_, rfl, rfl, rfl⟩
          | ref mn nm args =>
            simp only [setObjs] at h
            split at h
            · rename_i s c ss hr
              simp only [Option.some.injEq] at h; subst h
              simp only [List.mem_singleton] at ho; subst ho
              obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
              obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
              simp only [oelems, evalObj, resolveObj_mono hr (by omega : n ≤ N + 1)]
              exact ⟨_, rfl, rfl, rfl⟩
            · simp only [Option.some.injEq] at h; subst h; simp at ho
          | _ => simp [setObjs] at h
        | set os =>
          simp only [setObjs] at h
          obtain ⟨x, hx, hxs⟩ := iho os sc objs h o ho cf N (by omega)
          exact ⟨x, by simpa [oelems] using hx, hxs⟩
        | union a b =>
          simp [setObjs, Option.bind_eq_some_iff] at h
          obtain ⟨xa, ha, xb, hb, rfl⟩ := h
          rcases List.mem_append.mp ho with ho | ho
          · obtain ⟨x, hx, hxs⟩ := ihs a sc xa ha o ho cf N (by omega)
            exact ⟨x, by simp only [oelems, OSet.union]; exact .inr (.inr (.inl hx)), hxs⟩
          · obtain ⟨x, hx, hxs⟩ := ihs b sc xb hb o ho cf N (by omega)
            exact ⟨x, by simp only [oelems, OSet.union]; exact .inr (.inr (.inr hx)), hxs⟩
        | _ => simp [setObjs] at h
      refine ⟨hset, fun os sc objs h o ho cf N hN => ?_⟩
      cases os with
      | spec r ext a =>
        obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
        have key : ∀ (e : OElems), (∃ xs, setObjs E n (k + 1) sc e = some xs ∧ o ∈ xs) →
            ∃ x, (oelems E N sc cf e).a x ∧ x.sc = o.1 ∧ x.settings = o.2 := by
          rintro e ⟨xs, hxs, ho⟩; exact hset e sc xs hxs o ho cf N (by omega)
        simp only [evalObjSet, OSet.ofSpecs]
        cases r <;> cases a <;> simp [objSetObjs] at h
        · subst h; simp at ho
        · obtain ⟨x, hx, hxs⟩ := key _ ⟨_, h, ho⟩
          exact ⟨x, .inr ⟨_, rfl, hx⟩, hxs⟩
        · obtain ⟨x, hx, hxs⟩ := key _ ⟨_, h, ho⟩
          exact ⟨x, .inl (by simpa using hx), hxs⟩
        · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨xr, hr, xa, ha, rfl⟩ := h
          rcases List.mem_append.mp ho with ho | ho
          · obtain ⟨x, hx, hxs⟩ := key _ ⟨_, hr, ho⟩
            exact ⟨x, .inl (by simpa using hx), hxs⟩
          · obtain ⟨x, hx, hxs⟩ := key _ ⟨_, ha, ho⟩
            exact ⟨x, .inr ⟨_, rfl, hx⟩, hxs⟩
      | ref mn nm args =>
        obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
        simp only [objSetObjs] at h
        split at h
        · rename_i s c os' hr
          obtain ⟨x, hx, hxs⟩ := iho os' s objs h o ho _ N (by omega)
          refine ⟨x, ?_, hxs⟩
          simp only [evalObjSet, resolveObjSet_mono hr (by omega : n ≤ N)]
          exact hx
        · simp only [Option.some.injEq] at h; subst h; simp at ho


theorem find_name {α : Type} {l : List (String × α)} {g : String} {p : String × α}
    (h : l.find? (·.1 == g) = some p) : p.1 = g ∧ p ∈ l := by
  have h1 := List.find?_some h
  exact ⟨by simpa using h1, List.mem_of_find?_eq_some h⟩

theorem uniqueOkB_of {cls : ClassRef} {os : ObjSet}
    (h : ∀ N, n ≤ N → UniqueOk E N sc cls os) : uniqueOkB E n sc cls os = true := by
  unfold uniqueOkB
  split
  · rename_i csc fs objs hcf hobjs
    simp only [List.all_eq_true]
    intro f hf
    by_contra hp
    simp only [Bool.not_eq_true] at hp
    obtain ⟨a, ha, b, hb, x, hka, hkb, hd⟩ := pairsOk_false hp
    have hU := h (n + 30) (by omega)
    have hcfN := classFields_mono hcf (by omega : n ≤ n + 30)
    obtain ⟨xa, hxa, hxasc, hxaset⟩ := (objs_mem 8).2 os sc objs hobjs a ha (some (csc, fs)) (n + 30) (by omega)
    obtain ⟨xb, hxb, hxbsc, hxbset⟩ := (objs_mem 8).2 os sc objs hobjs b hb (some (csc, fs)) (n + 30) (by omega)
    -- `f` is a UNIQUE field
    obtain ⟨t, ht⟩ : ∃ t, (f, t) ∈ uniqueFields fs := by
      simp only [List.mem_filterMap] at hf
      obtain ⟨fd, hfd, hfd'⟩ := hf
      cases fd with
      | fixedValue nm t u o =>
        cases u <;> simp at hfd'
        subst hfd'
        exact ⟨t, List.mem_filterMap.mpr ⟨_, hfd, rfl⟩⟩
      | _ => simp at hfd'
    -- the settings the keys come from
    have hset : ∀ (o : Scope × List (String × Setting)) (g : String) (y : VKey),
        ((List.find? (fun x => x.1 == g) o.2).bind fun x => match x with
          | (_, st) => match st with
            | Setting.value v => valKey E n o.1 8 v
            | _ => none) = some y →
        ∃ v, (g, Setting.value v) ∈ o.2 ∧ valKey E n o.1 8 v = some y := by
      intro o g y hk
      simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨⟨g', st⟩, hfind, hst⟩ := hk
      obtain ⟨rfl, hmem⟩ := find_name hfind
      cases st with
      | value v => exact ⟨v, hmem, hst⟩
      | _ => simp at hst
    obtain ⟨va, hva, hka'⟩ := hset a f x hka
    obtain ⟨vb, hvb, hkb'⟩ := hset b f x hkb
    have hev : ∀ (o : Scope × List (String × Setting)) v y, valKey E n o.1 8 v = some y →
        ∀ w, evalVal E (n + 30) o.1 v w ↔ w = y.toVal :=
      fun o v y hk => evalVal_of_valKey hk (n + 30) (by omega)
    have hsame := hU (csc, fs) hcfN f t ht xa xb hxa hxb
      ⟨va, vb, x.toVal, by rw [hxaset]; exact hva, by rw [hxbset]; exact hvb,
        by rw [hxasc]; exact (hev a va x hka' _).mpr rfl, by rw [hxbsc]; exact (hev b vb x hkb' _).mpr rfl⟩
    obtain ⟨hnames, hsettings⟩ := hsame
    rw [hxaset, hxbset] at hnames
    rw [hxaset, hxbset, hxasc, hxbsc] at hsettings
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq,
      List.mem_map] at hd
    rcases hd with (⟨g, ⟨p, hp, rfl⟩, hno⟩ | ⟨g, ⟨p, hp, rfl⟩, hno⟩) | ⟨g, ⟨p, hp, rfl⟩, hdiff⟩
    · have := (hnames p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp this
      exact hno q hq (by simp [hq1])
    · have := (hnames p.1).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp this
      exact hno q hq (by simp [hq1])
    · rcases hdiff with hdiff | hdiff
      · split at hdiff
        · rename_i x' y' hx' hy'
          obtain ⟨va', hva', hk1⟩ := hset a p.1 x' hx'
          obtain ⟨vb', hvb', hk2⟩ := hset b p.1 y' hy'
          have hss := hsettings p.1 _ _ hva' hvb'
          simp only [SettingSame] at hss
          obtain ⟨z, hz1, hz2⟩ := hss
          rw [(hev a va' x' hk1 z).mp hz1] at hz2
          have := VKey.toVal_inj ((hev b vb' y' hk2 _).mp hz2)
          simp [this] at hdiff
        · simp at hdiff
      · split at hdiff
        · rename_i s1 t1 s2 u1 hfa hfb
          obtain ⟨hn1, hm1⟩ := find_name hfa
          obtain ⟨hn2, hm2⟩ := find_name hfb
          simp only at hn1 hn2
          rw [hn1] at hm1; rw [hn2] at hm2
          have hss := hsettings p.1 _ _ hm1 hm2
          simp only [SettingSame] at hss
          split at hdiff
          · rename_i y1 y2 hy1 hy2
            have e1 : ((builtin E (n + 30) a.1 t1).bind fun x => builtinName x.2) = some y1 := by
              simp only [Option.bind_eq_some_iff] at hy1 ⊢
              obtain ⟨r, hr, hr'⟩ := hy1; exact ⟨r, builtin_mono hr (by omega), hr'⟩
            have e2 : ((builtin E (n + 30) b.1 u1).bind fun x => builtinName x.2) = some y2 := by
              simp only [Option.bind_eq_some_iff] at hy2 ⊢
              obtain ⟨r, hr, hr'⟩ := hy2; exact ⟨r, builtin_mono hr (by omega), hr'⟩
            rw [e1, e2] at hss
            simp at hss; simp [hss] at hdiff
          · simp at hdiff
        · simp at hdiff
  · rfl

end Objects

theorem objSetChecks_nil {m : Module} {nm : String} {cls : ClassRef} {os : ObjSet}
    (h : ObjSetOk E n (.ofModule m) cls os) (hup : ∀ n', n ≤ n' → UniqueOk E n' (.ofModule m) cls os)
    (hm : sizeOf m < n) : objSetChecks E n m nm cls os = [] := by
  have hn : 0 < n := by omega
  have h2 : uniqueOkB E n (.ofModule m) cls os = true := uniqueOkB_of hup
  have h3 : oelemsRefsOkB.objSetRefsOkB E n (.ofModule m) os = true := objSetRefsOkB_of h.refs
  have hc := h.clsResolves
  simp only [objSetChecks, h2, h3, ↓reduceIte, List.append_nil, List.nil_append]
  cases os with
  | ref mn' nm' args' => cases cls <;> simp_all [ClassResolves]
  | spec r x a =>
    have hf : ∀ e, (r = some e ∨ a = some e) → oelemsFieldsOkB E n (.ofModule m) cls e = true := by
      rintro e he
      exact oelemsFieldsOkB_of fun o ho => objFieldsOkB_of (h.fields o (by
        rcases he with rfl | rfl
        · exact ⟨_, x, a, rfl, .inl ⟨e, rfl, ho⟩⟩
        · exact ⟨r, x, _, rfl, .inr ⟨e, rfl, ho⟩⟩)) hn
    have hv : ∀ e, (r = some e ∨ a = some e) → oelemsValRefsOkB E n (.ofModule m) cls e = true := by
      rintro e he
      exact oelemsValRefsOkB_of fun o ho => objValRefsOkB_of (h.settingRefs o (by
        rcases he with rfl | rfl
        · exact ⟨_, x, a, rfl, .inl ⟨e, rfl, ho⟩⟩
        · exact ⟨r, x, _, rfl, .inr ⟨e, rfl, ho⟩⟩)) hn
    have hrf : (r.map (oelemsFieldsOkB E n (.ofModule m) cls)).getD true = true := by
      cases r with | none => rfl | some e => exact hf e (.inl rfl)
    have haf : (a.map (oelemsFieldsOkB E n (.ofModule m) cls)).getD true = true := by
      cases a with | none => rfl | some e => exact hf e (.inr rfl)
    have hrv : (r.map (oelemsValRefsOkB E n (.ofModule m) cls)).getD true = true := by
      cases r with | none => rfl | some e => exact hv e (.inl rfl)
    have hav : (a.map (oelemsValRefsOkB E n (.ofModule m) cls)).getD true = true := by
      cases a with | none => rfl | some e => exact hv e (.inr rfl)
    simp only [hrf, haf, hrv, hav, Bool.and_self, ↓reduceIte, List.append_nil]
    cases cls <;> simp_all [ClassResolves]

theorem objChecks_nil {m : Module} {nm : String} {cls : ClassRef} {o : Obj}
    (h : ObjOk E n (.ofModule m) cls o) (hm : sizeOf m < n) : objChecks E n m nm cls o = [] := by
  have hn : 0 < n := by omega
  have h1 : oelemsRefsOkB E n (.ofModule m) (.obj o) = true := oelemsRefsOkB_of h.ref
  have h3 : objFieldsOkB E n (.ofModule m) cls o = true := objFieldsOkB_of h.fields hn
  have h4 : objValRefsOkB E n (.ofModule m) cls o = true := objValRefsOkB_of h.settingRefs hn
  have hc := h.clsResolves
  simp only [objChecks, h1, h3, h4, ↓reduceIte, List.append_nil, List.nil_append]
  cases cls <;> simp_all [ClassResolves]

theorem typeAssignChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String}
    {t : Ty} (hV : m.ValidAt E H n) (hm : sizeOf m < n) (h : (nm, t) ∈ m.types) :
    typeAssignChecks E n m nm t = [] := by
  have hsite : m.Site nm t := .type h
  have hne := ((hV.types nm t hsite).types t (.self t)).nonEmpty
  simp [typeAssignChecks, tyChainB_of (hV.typeChains nm t h)]

theorem valueChecks_nil {E : Env} {H : ContentsHook} {n : Nat} {m : Module} {nm : String} {t : Ty}
    {v : Val} (hV' : ∀ n', n ≤ n' → m.ValidAt E H n') (hm : sizeOf m < n) (h : (nm, t, v) ∈ m.values) :
    valueChecks E n m nm t v = [] := by
  have hV := hV' n (Nat.le_refl n)
  obtain ⟨⟨w, hev, hsem⟩, hmaps⟩ := hV.values nm t v h
  have hsz : sizeOf t + sizeOf v < n := by
    have h1 := List.sizeOf_lt_of_mem h; cases m; simp at h1 hm ⊢; omega
  have h1 : valRefsOkB E n (.ofModule m) v = true := valRefsOkB_of_eval hev (Nat.le_refl n)
  have h2 : valOkB E n (.ofModule m) t v = true :=
    valOkB_of (ValIn.of_eventually fun M hM => ((hV' M hM).values nm t v h).1) hmaps (by omega)
  have h3 : valChainB E n n (.ofModule m) v = true := valChainB_of hev (Nat.le_refl n)
  simp [valueChecks, h1, h2, h3]

/-! ## The theorem -/

/-- At fuel `n`, if every module is valid from `n` on, and `n` is larger than the specification,
the checker reports only notation rules. (The spec looks through a constrained type at less fuel
than the checker does; above `n` it looks at the checker's.) -/
theorem checkEnv_sound_at {E : Env} {H : ContentsHook} {n : Nat}
    (hV : ∀ n', n ≤ n' → ∀ m ∈ E, m.ValidAt E H n')
    (hP : ∀ m ∈ E, ∀ pa ∈ m.params, ∃ args, ∀ n', n ≤ n' → ParamBodyOk E H n' m pa args)
    (hE : sizeOf E < n) :
    ∀ v ∈ checkEnv E n, v.IsNotation := by
  intro v hv
  simp only [checkEnv, List.mem_flatMap, List.mem_append] at hv
  obtain ⟨m, hm, hv⟩ := hv
  have hVm := hV n (Nat.le_refl n) m hm
  have hsz : sizeOf m < n := Nat.lt_trans (List.sizeOf_lt_of_mem hm) hE
  rcases hv with ((((((hv | hv) | hv) | hv) | hv) | hv) | hv) | hv
  · exact moduleChecks_sound hVm v hv
  · obtain ⟨⟨nm, sc, t⟩, hmem, hv⟩ := hv
    rcases mem_moduleTypes hmem with ⟨rfl, hs⟩ | ⟨pa, hpa, rfl, rfl, hhas⟩
    · rw [siteChecks_nil (fun n' hn' => (hV n' hn' m hm).types nm t hs) (Nat.lt_trans hs.sizeOf_lt hsz)] at hv
      simp at hv
    · obtain ⟨args, hargs⟩ := hP m hm pa hpa
      have ht : sizeOf t < n := by
        have := hhas.sizeOf_lt; have := sizeOf_param_lt hpa; omega
      rw [siteChecks_param_nil hargs hhas ht] at hv; simp at hv
  · rw [paramChecks_nil hVm (fun pa hpa => by
      obtain ⟨args, hargs⟩ := hP m hm pa hpa; exact ⟨args, hargs n (Nat.le_refl n)⟩) hsz] at hv; simp at hv
  · rw [classChecks_nil (fun n' hn' => hV n' hn' m hm) hsz] at hv; simp at hv
  · obtain ⟨⟨nm, cls, os⟩, hmem, hv⟩ := hv
    rw [objSetChecks_nil (hVm.objectSets nm cls os hmem)
      (fun n' hn' => ((hV n' hn' m hm).objectSets nm cls os hmem).unique) hsz] at hv; simp at hv
  · obtain ⟨⟨nm, cls, o⟩, hmem, hv⟩ := hv
    rw [objChecks_nil (hVm.objects nm cls o hmem) hsz] at hv; simp at hv
  · obtain ⟨⟨nm, t⟩, hmem, hv⟩ := hv
    rw [typeAssignChecks_nil hVm hsz hmem] at hv; simp at hv
  · obtain ⟨⟨nm, t, w⟩, hmem, hv⟩ := hv
    rw [valueChecks_nil (fun n' hn' => hV n' hn' m hm) hsz hmem] at hv; simp at hv

/-- Finitely many facts that each hold from some point on hold together from some point on. -/
theorem List.bound_all {α : Type} {Q : α → Nat → Prop} (hQ : ∀ x N N', Q x N → N ≤ N' → Q x N') :
    ∀ {l : List α}, (∀ x ∈ l, ∃ N, Q x N) → ∃ N, ∀ x ∈ l, Q x N
  | [], _ => ⟨0, by simp⟩
  | x :: l, h => by
    obtain ⟨N1, h1⟩ := h x (by simp)
    obtain ⟨N2, h2⟩ := List.bound_all hQ (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨max N1 N2, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hQ _ _ _ h1 (by omega)
    · exact hQ _ _ _ (h2 y hy) (by omega)

/-- **The checker rejects only what the spec rejects.** For a valid specification, from some fuel
on, `checkEnv` reports only rules about the notation. -/
theorem checkEnv_sound {E : Env} {H : ContentsHook} (h : Env.Valid E H) :
    ∃ N, ∀ n ≥ N, ∀ v ∈ checkEnv E n, v.IsNotation := by
  obtain ⟨N, hN⟩ := h.modules
  -- the actual parameters of each parameterized body, and a fuel from which they make it valid
  obtain ⟨N2, hN2⟩ : ∃ N2, ∀ m ∈ E, ∀ pa ∈ m.params, ∃ args, ∀ n, N2 ≤ n → ParamBodyOk E H n m pa args := by
    refine List.bound_all (Q := fun m N2 => ∀ pa ∈ m.params, ∃ args, ∀ n, N2 ≤ n → ParamBodyOk E H n m pa args)
      (fun m N N' h hN pa hpa => by
        obtain ⟨args, ha⟩ := h pa hpa; exact ⟨args, fun n hn => ha n (by omega)⟩) fun m hm => ?_
    exact List.bound_all (Q := fun pa N2 => ∃ args, ∀ n, N2 ≤ n → ParamBodyOk E H n m pa args)
      (fun pa N N' h hN => by obtain ⟨args, ha⟩ := h; exact ⟨args, fun n hn => ha n (by omega)⟩)
      fun pa hpa => by obtain ⟨args, N3, h3⟩ := h.params m hm pa hpa; exact ⟨N3, args, h3⟩
  exact ⟨max (max N N2) (sizeOf E + 1), fun n hn =>
    checkEnv_sound_at (fun n' hn' => hN n' (by omega))
      (fun m hm pa hpa => by
        obtain ⟨args, ha⟩ := hN2 m hm pa hpa; exact ⟨args, fun n' hn' => ha n' (by omega)⟩)
      (by omega)⟩

/-- X.680 13.7, 13.10: what `asn1check` checks for each file. The modules of a file are among the
specification's, so two of them that share a name without distinct identifiers break
`ModuleNamesOk`. -/
theorem moduleNamesTwice_sound {E ms : Env} (hsub : ms.Sublist E)
    (h : moduleNamesTwice (ms.map fun m => (m.name, m.oid)) ≠ []) : ¬ ModuleNamesOk E := by
  intro hE
  have hp : ms.Pairwise fun a b => a.name = b.name → ∃ x y, a.oid = some x ∧ b.oid = some y ∧ x ≠ y :=
    hE.sublist hsub
  apply h; clear h hsub hE
  induction ms with
  | nil => rfl
  | cons a rest ih =>
    rw [List.pairwise_cons] at hp
    simp only [List.map_cons, moduleNamesTwice, ih hp.2, List.append_nil, List.filterMap_eq_nil_iff,
      List.mem_map]
    rintro ⟨b, y⟩ ⟨b', hb', he⟩
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    by_cases hn : a.name = b'.name
    · obtain ⟨x, y, hx, hy, hxy⟩ := hp.1 b' hb' hn
      simp [hx, hy, hxy]
    · simp [hn]

end Asn1.X680
