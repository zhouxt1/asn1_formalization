import Asn1.X680.SoundValues

/-!
# A parameterized body: the checker knows less than the spec

The checker reads a parameterized body with its dummies bound to nothing (`Scope.withDummies`), the
spec with actual parameters (`bindParams`). `ScLess sc1 sc2` relates the two scopes, and the
scopes reached from them. What the first resolves, the second resolves alike; so each rule the
checker decides on the first, it decides alike on the second, or does not decide.
-/

namespace Asn1.X680

/-! ## A scope that knows less -/

/-- The kind of actual parameter a governor allows (X.683 8.3, `ArgFits` without the values). -/
def ArgKindOk : Option ParamGov → Arg → Prop
  | none, .type _ | none, .cls _ => True
  | some (.type _), .value _ | some (.type _), .valueSet _ => True
  | some (.cls _), .obj _ | some (.cls _), .objSet _ => True
  | some (.dummy _), .value _ | some (.dummy _), .valueSet _
  | some (.dummy _), .obj _ | some (.dummy _), .objSet _ => True
  | _, _ => False

mutual
/-- `sc1` reads the names `sc2` reads, except that dummies of `sc1` may be bound to nothing
(`.raw []`) where `sc2` binds them to actual parameters: a parameterized body read as the checker
reads it (`Scope.withDummies`) and as the spec does (`bindParams`). -/
inductive ScLess : Scope → Scope → Prop
  | mk {m : Module} {bs1 bs2 : List (String × Arg × Option ParamGov × Scope)} :
      BindsLess bs1 bs2 → ScLess (.mk m bs1) (.mk m bs2)
inductive BindsLess : List (String × Arg × Option ParamGov × Scope) →
    List (String × Arg × Option ParamGov × Scope) → Prop
  | nil : BindsLess [] []
  | dummy {nm : String} {g : Option ParamGov} {c1 c2 : Scope} {a : Arg} {bs1 bs2} :
      ArgKindOk g a → BindsLess bs1 bs2 → BindsLess ((nm, .raw [], g, c1) :: bs1) ((nm, a, g, c2) :: bs2)
  | same {nm : String} {a : Arg} {g : Option ParamGov} {c1 c2 : Scope} {bs1 bs2} :
      ScLess c1 c2 → BindsLess bs1 bs2 → BindsLess ((nm, a, g, c1) :: bs1) ((nm, a, g, c2) :: bs2)
end

theorem ScLess.refl : ∀ (sc : Scope), ScLess sc sc
  | .mk m bs => .mk (BindsLess.refl' bs)
where
  BindsLess.refl' : ∀ bs : List (String × Arg × Option ParamGov × Scope), BindsLess bs bs
    | [] => .nil
    | (nm, a, g, c) :: bs => .same (ScLess.refl c) (BindsLess.refl' bs)

theorem ScLess.mod {sc1 sc2 : Scope} (h : ScLess sc1 sc2) : sc1.mod = sc2.mod := by
  cases h; rfl

theorem ScLess.ofModule (m : Module) : ScLess (.ofModule m) (.ofModule m) := ScLess.refl _

/-- What a scope that knows less binds a name to. -/
theorem BindsLess.find {name : String} : ∀ {bs1 bs2 : List (String × Arg × Option ParamGov × Scope)},
    BindsLess bs1 bs2 →
      ((bs1.find? (·.1 == name)).isNone ↔ (bs2.find? (·.1 == name)).isNone) ∧
      ∀ a1 g1 c1, (bs1.find? (·.1 == name)).map (·.2) = some (a1, g1, c1) →
        ∃ a2 c2, (bs2.find? (·.1 == name)).map (·.2) = some (a2, g1, c2) ∧
          ((a1 = .raw [] ∧ ArgKindOk g1 a2) ∨ (a1 = a2 ∧ ScLess c1 c2))
  | [], [], .nil => by simp
  | _, _, .dummy (nm := nm) (g := g) (c1 := c1) (c2 := c2) (a := a) hk h => by
    by_cases hn : nm = name
    · subst hn
      simp only [List.find?_cons, beq_self_eq_true, Option.isNone_some, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      rintro a1 g1 c1' ⟨rfl, rfl, rfl⟩
      exact ⟨a, c2, ⟨rfl, rfl, rfl⟩, .inl ⟨rfl, hk⟩⟩
    · have ih := BindsLess.find (name := name) h
      have hne : (nm == name) = false := by simp [hn]
      simp only [List.find?_cons, hne]
      exact ih
  | _, _, .same (nm := nm) (a := a) (g := g) (c1 := c1) (c2 := c2) hc h => by
    by_cases hn : nm = name
    · subst hn
      simp only [List.find?_cons, beq_self_eq_true, Option.isNone_some, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      rintro a1 g1 c1' ⟨rfl, rfl, rfl⟩
      exact ⟨a, c2, ⟨rfl, rfl, rfl⟩, .inr ⟨rfl, hc⟩⟩
    · have ih := BindsLess.find (name := name) h
      have hne : (nm == name) = false := by simp [hn]
      simp only [List.find?_cons, hne]
      exact ih

theorem ScLess.bound {sc1 sc2 : Scope} (h : ScLess sc1 sc2) (name : String) :
    ((sc1.bound name).isNone ↔ (sc2.bound name).isNone) ∧
      ∀ a1 g1 c1, sc1.bound name = some (a1, g1, c1) →
        ∃ a2 c2, sc2.bound name = some (a2, g1, c2) ∧
          ((a1 = .raw [] ∧ ArgKindOk g1 a2) ∨ (a1 = a2 ∧ ScLess c1 c2)) := by
  cases h with
  | mk hb =>
    have := BindsLess.find (name := name) hb
    simp only [Scope.bound, Scope.binds, Option.isNone_map] at this ⊢
    exact this

theorem bindParams_less {m : Module} {ps : List Param} {args : List Arg} {sc1 sc2 : Scope}
    (h : ScLess sc1 sc2) : ScLess (bindParams m ps args sc1) (bindParams m ps args sc2) := by
  unfold bindParams
  refine .mk ?_
  induction (ps.zip args) with
  | nil => exact .nil
  | cons x xs ih => exact .same h ih

/-- What a scope that knows less resolves, a scope that knows more resolves alike, when a dummy
bound to nothing resolves to nothing. -/
theorem resolveIn_less {α : Type} {E : Env} {n : Nat} {sc1 sc2 : Scope} {mn : Option String}
    {name : String} {args : List Arg} {G : Arg → Option ParamGov → Option α}
    {fromModule : Module → Option α} {fromParam : ParamAssign → Option (List Param × α)}
    (hraw : ∀ g, G (.raw []) g = none) (hsc : ScLess sc1 sc2) {s1 : Scope} {x0 : α}
    (h : resolveIn E n sc1 mn name args (fun a g c => (G a g).map fun x => (c, x)) fromModule fromParam =
      some (s1, x0)) :
    ∃ s2, resolveIn E n sc2 mn name args (fun a g c => (G a g).map fun x => (c, x)) fromModule fromParam =
      some (s2, x0) ∧ ScLess s1 s2 := by
  obtain ⟨hnone, hsome⟩ := hsc.bound name
  have hmod := hsc.mod
  unfold resolveIn at h ⊢
  rw [hmod] at h
  cases mn with
  | none =>
    cases args with
    | nil =>
      cases hb1 : sc1.bound name with
      | none =>
        have hb2 : sc2.bound name = none := by
          have := hnone.mp (by simp [hb1]); simpa using this
        rw [hb1] at h; rw [hb2]
        simp only [Option.map_eq_some_iff] at h ⊢
        obtain ⟨⟨m', x'⟩, hm, he⟩ := h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, ⟨(m', _), hm, rfl⟩, ScLess.ofModule m'⟩
      | some b =>
        obtain ⟨a1, g1, c1⟩ := b
        obtain ⟨a2, c2, hb2, hrel⟩ := hsome a1 g1 c1 hb1
        rw [hb1] at h; rw [hb2]
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
        obtain ⟨x', hx, rfl, rfl⟩ := h
        rcases hrel with ⟨rfl, -⟩ | ⟨rfl, hc⟩
        · rw [hraw] at hx; cases hx
        · exact ⟨c2, ⟨x', hx, rfl, rfl⟩, hc⟩
    | cons a as =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨⟨m', ps, x'⟩, hm, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, ⟨(m', ps, _), hm, rfl⟩, bindParams_less hsc⟩
  | some mn' =>
    cases args with
    | nil =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨⟨m', x'⟩, hm, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, ⟨(m', _), hm, rfl⟩, ScLess.ofModule m'⟩
    | cons a as =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨⟨m', ps, x'⟩, hm, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, ⟨(m', ps, _), hm, rfl⟩, bindParams_less hsc⟩


section Less

variable {E : Env} {n : Nat} {sc1 sc2 : Scope}

def tyArg : Arg → Option ParamGov → Option Ty
  | .type t, _ => some t
  | .valueSet c, some (.type gt) => some (.constrained gt c)
  | _, _ => none

theorem resolveTy_eq (sc : Scope) (mn : Option String) (name : String) (args : List Arg) :
    resolveTy E n sc mn name args = resolveIn E n sc mn name args (fun a g c => (tyArg a g).map fun x => (c, x))
      (·.lookup name)
      (fun | .type _ ps body => some (ps, body)
           | .valueSet _ ps t c => some (ps, .constrained t c)
           | _ => none) := by
  unfold resolveTy
  congr 1
  funext a g c
  cases a <;> (try cases g) <;> simp [tyArg]
  all_goals rename_i x; cases x <;> simp [tyArg]

theorem resolveTy_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope} {t : Ty}
    (hsc : ScLess sc1 sc2) (h : resolveTy E n sc1 mn name args = some (s1, t)) :
    ∃ s2, resolveTy E n sc2 mn name args = some (s2, t) ∧ ScLess s1 s2 := by
  rw [resolveTy_eq] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h

def valArg : Arg → Option ParamGov → Option Val
  | .value v, _ => some v
  | _, _ => none

theorem resolveVal_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope} {v : Val}
    (hsc : ScLess sc1 sc2) (h : resolveVal E n sc1 mn name args = some (s1, v)) :
    ∃ s2, resolveVal E n sc2 mn name args = some (s2, v) ∧ ScLess s1 s2 := by
  have e : ∀ sc, resolveVal E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (valArg a g).map fun x => (c, x))
      (fun m => (m.values.find? (·.1 == name)).map (·.2.2))
      (fun | .value _ ps _ v => some (ps, v) | _ => none) := by
    intro sc; unfold resolveVal; congr 1; funext a g c; cases a <;> simp [valArg]
  rw [e] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h

def clsArg : Arg → Option ParamGov → Option ClassRef
  | .cls c, _ => some c
  | _, _ => none

theorem resolveClass_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope} {c : ClassRef}
    (hsc : ScLess sc1 sc2) (h : resolveClass E n sc1 mn name args = some (s1, c)) :
    ∃ s2, resolveClass E n sc2 mn name args = some (s2, c) ∧ ScLess s1 s2 := by
  have e : ∀ sc, resolveClass E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (clsArg a g).map fun x => (c, x))
      (fun m => (m.classes.find? (·.1 == name)).map (·.2))
      (fun | .cls _ ps c => some (ps, c) | _ => none) := by
    intro sc; unfold resolveClass; congr 1; funext a g c; cases a <;> simp [clsArg]
  rw [e] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h

def objArg : Arg → Option ParamGov → Option (Option ClassRef × Obj)
  | .obj o, _ => some (none, o)
  | _, _ => none

theorem resolveObj_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope}
    {x : Option ClassRef × Obj}
    (hsc : ScLess sc1 sc2) (h : resolveObj E n sc1 mn name args = some (s1, x)) :
    ∃ s2, resolveObj E n sc2 mn name args = some (s2, x) ∧ ScLess s1 s2 := by
  have e : ∀ sc, resolveObj E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (objArg a g).map fun x => (c, x))
      (fun m => (m.objects.find? (·.1 == name)).map fun (_, c, o) => (some c, o))
      (fun | .obj _ ps c o => some (ps, some c, o) | _ => none) := by
    intro sc; unfold resolveObj; congr 1; funext a g c; cases a <;> simp [objArg]
  rw [e] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h

def objSetArg : Arg → Option ParamGov → Option (Option ClassRef × ObjSet)
  | .objSet s, _ => some (none, s)
  | _, _ => none

theorem resolveObjSet_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope}
    {x : Option ClassRef × ObjSet}
    (hsc : ScLess sc1 sc2) (h : resolveObjSet E n sc1 mn name args = some (s1, x)) :
    ∃ s2, resolveObjSet E n sc2 mn name args = some (s2, x) ∧ ScLess s1 s2 := by
  have e : ∀ sc, resolveObjSet E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (objSetArg a g).map fun x => (c, x))
      (fun m => (m.objectSets.find? (·.1 == name)).map fun (_, c, s) => (some c, s))
      (fun | .objSet _ ps c s => some (ps, some c, s) | _ => none) := by
    intro sc; unfold resolveObjSet; congr 1; funext a g c; cases a <;> simp [objSetArg]
  rw [e] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h

theorem resolveValTy_less {mn : Option String} {name : String} {args : List Arg} {s1 : Scope} {t : Ty}
    (hsc : ScLess sc1 sc2) (h : resolveValTy E n sc1 mn name args = some (s1, t)) :
    ∃ s2, resolveValTy E n sc2 mn name args = some (s2, t) ∧ ScLess s1 s2 := by
  have e : ∀ sc, resolveValTy E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => ((fun _ _ => none : Arg → Option ParamGov → Option Ty) a g).map fun x => (c, x))
      (fun m => (m.values.find? (·.1 == name)).map (·.2.1))
      (fun | .value _ ps t _ => some (ps, t) | _ => none) := by
    intro sc; unfold resolveValTy; congr 1
  rw [e] at h ⊢
  exact resolveIn_less (fun g => rfl) hsc h



theorem classFields_less : ∀ {n : Nat} {sc1 sc2 : Scope} {c : ClassRef} {s1 : Scope} {fs : List FieldSpec},
    ScLess sc1 sc2 → classFields E n sc1 c = some (s1, fs) →
      ∃ s2, classFields E n sc2 c = some (s2, fs) ∧ ScLess s1 s2
  | 0, _, _, _, _, _, _, h => by simp [classFields] at h
  | n + 1, sc1, sc2, c, s1, fs, hsc, h => by
    cases c with
    | defn fs' syn => simp [classFields] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩
    | typeIdentifier => simp [classFields] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, ScLess.refl _⟩
    | abstractSyntax => simp [classFields] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, ScLess.refl _⟩
    | ref mn name args =>
      simp only [classFields] at h ⊢
      split at h
      · rename_i s c' hr
        obtain ⟨s2, hr2, hs⟩ := resolveClass_less hsc hr
        rw [hr2]
        exact classFields_less hs h
      · simp at h

theorem fieldAt_less : ∀ {n : Nat} {s1 s2 : Scope} {fs : List FieldSpec} {p : List String} {r1 : Scope}
    {f : FieldSpec}, ScLess s1 s2 → fieldAt E n (s1, fs) p = some (r1, f) →
      ∃ r2, fieldAt E n (s2, fs) p = some (r2, f) ∧ ScLess r1 r2
  | 0, _, _, _, _, _, _, _, h => by simp [fieldAt] at h
  | n + 1, s1, s2, fs, [], r1, f, _, h => by simp [fieldAt] at h
  | n + 1, s1, s2, fs, [g], r1, f, hs, h => by
    simp only [fieldAt, Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
    obtain ⟨f', hf, rfl, rfl⟩ := h
    exact ⟨s2, ⟨f', hf, rfl, rfl⟩, hs⟩
  | n + 1, s1, s2, fs, g :: g' :: rest, r1, f, hs, h => by
    simp only [fieldAt] at h ⊢
    split at h
    · rename_i nm c o hf
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨cs, cfs⟩, hc, hr⟩ := h
      obtain ⟨cs2, hc2, hcs⟩ := classFields_less hs hc
      obtain ⟨r2, hr2, hrs⟩ := fieldAt_less hcs hr
      exact ⟨r2, ⟨(cs2, cfs), hc2, hr2⟩, hrs⟩
    · rename_i nm c o hf
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨cs, cfs⟩, hc, hr⟩ := h
      obtain ⟨cs2, hc2, hcs⟩ := classFields_less hs hc
      obtain ⟨r2, hr2, hrs⟩ := fieldAt_less hcs hr
      exact ⟨r2, ⟨(cs2, cfs), hc2, hr2⟩, hrs⟩
    · simp at h

theorem fields_bind_less {n : Nat} {sc1 sc2 : Scope} {cls : ClassRef} {path : List String} {r1 : Scope}
    {f : FieldSpec} (hsc : ScLess sc1 sc2)
    (h : (classFields E n sc1 cls).bind (fun cf => fieldAt E n cf path) = some (r1, f)) :
    ∃ r2, (classFields E n sc2 cls).bind (fun cf => fieldAt E n cf path) = some (r2, f) ∧ ScLess r1 r2 := by
  simp only [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨⟨cs, cfs⟩, hc, hr⟩ := h
  obtain ⟨cs2, hc2, hcs⟩ := classFields_less hsc hc
  obtain ⟨r2, hr2, hrs⟩ := fieldAt_less hcs hr
  exact ⟨r2, ⟨(cs2, cfs), hc2, hr2⟩, hrs⟩

theorem objSetClass_less {n : Nat} {sc1 sc2 : Scope} {os : ObjSet} {s1 : Scope} {c : ClassRef}
    (hsc : ScLess sc1 sc2) (h : objSetClass E n sc1 os = some (s1, c)) :
    ∃ s2, objSetClass E n sc2 os = some (s2, c) ∧ ScLess s1 s2 := by
  unfold objSetClass at h ⊢
  split at h
  · rename_i mn name args
    split at h
    · rename_i s c' x hr
      obtain ⟨s2, hr2, hs⟩ := resolveObjSet_less hsc hr
      rw [hr2]; simp at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hs⟩
    · simp at h
  · rename_i mn name args
    split at h
    · rename_i s c' x hr
      obtain ⟨s2, hr2, hs⟩ := resolveObj_less hsc hr
      rw [hr2]; simp at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hs⟩
    · simp at h
  · simp at h

theorem builtin_less : ∀ {n : Nat} {sc1 sc2 : Scope} {t : Ty} {s1 : Scope} {b : Ty},
    ScLess sc1 sc2 → builtin E n sc1 t = some (s1, b) → ∃ s2, builtin E n sc2 t = some (s2, b) ∧ ScLess s1 s2
  | 0, _, _, _, _, _, _, h => by simp [builtin] at h
  | n + 1, sc1, sc2, t, s1, b, hsc, h => by
    cases t with
    | ref name =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtin_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | extRef mn name =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtin_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | paramRef mn name args =>
      simp only [builtin, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtin_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | tagged tg k t => simp only [builtin] at h ⊢; exact builtin_less hsc h
    | constrained t c => simp only [builtin] at h ⊢; exact builtin_less hsc h
    | instanceOf cls => simp only [builtin] at h ⊢; exact builtin_less hsc h
    | selection nm t =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i s root ext hb
        obtain ⟨s', hb', hs⟩ := builtin_less hsc hb
        rw [hb']; simp only
        split at h
        · rename_i a ha; exact builtin_less hs h
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i s nm u un o hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; exact builtin_less hs h
      · rename_i s nm u o hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; exact builtin_less hs h
      · rename_i s nm o hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; simp at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩
      · rename_i s nm o u hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; simp at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩
      · rename_i s nm o u hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; simp at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩
      · simp at h
    | fromObjects src path =>
      simp only [builtin] at h ⊢
      split at h
      · rename_i csc cls hc
        obtain ⟨csc2, hc2, hcs⟩ := objSetClass_less hsc hc
        rw [hc2]; simp only
        split at h
        · rename_i s nm u un o hf
          obtain ⟨s', hf', hs⟩ := fields_bind_less hcs hf
          rw [hf']; exact builtin_less hs h
        · rename_i s nm u o hf
          obtain ⟨s', hf', hs⟩ := fields_bind_less hcs hf
          rw [hf']; exact builtin_less hs h
        · simp at h
      · simp at h
    | _ => simp [builtin] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩



theorem builtinV_less : ∀ {n : Nat} {sc1 sc2 : Scope} {t : Ty} {s1 : Scope} {b : Ty},
    ScLess sc1 sc2 → builtinV E n sc1 t = some (s1, b) → ∃ s2, builtinV E n sc2 t = some (s2, b) ∧ ScLess s1 s2
  | 0, _, _, _, _, _, _, h => by simp [builtinV] at h
  | n + 1, sc1, sc2, t, s1, b, hsc, h => by
    cases t with
    | ref name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtinV_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | extRef mn name =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtinV_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | paramRef mn name args =>
      simp only [builtinV, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less hsc h1
      obtain ⟨s2, h2', hs2⟩ := builtinV_less hs h2
      exact ⟨s2, ⟨(s', u), h1', h2'⟩, hs2⟩
    | tagged tg k t => simp only [builtinV] at h ⊢; exact builtinV_less hsc h
    | constrained t c => simp only [builtinV] at h ⊢; exact builtinV_less hsc h
    | instanceOf cls => simp only [builtinV] at h ⊢; exact builtinV_less hsc h
    | selection nm t =>
      simp only [builtinV] at h ⊢
      split at h
      · rename_i s root ext hb
        obtain ⟨s', hb', hs⟩ := builtin_less hsc hb
        rw [hb']; simp only
        split at h
        · exact builtinV_less hs h
        · simp at h
      · simp at h
    | classField cls path =>
      simp only [builtinV] at h ⊢
      split at h
      · rename_i s nm u un o hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; exact builtinV_less hs h
      · rename_i s nm u o hf
        obtain ⟨s', hf', hs⟩ := fields_bind_less hsc hf
        rw [hf']; exact builtinV_less hs h
      · simp at h
    | fromObjects src path => simp [builtinV] at h
    | _ => simp [builtinV] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hsc⟩

/-! ### Components -/

theorem forall₂_append {α β} {R : α → β → Prop} : ∀ {a : List α} {b : List β} {c : List α} {d : List β},
    List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall₂_append h2 h)

/-- Two expanded components alike, read in scopes the first knowing less. -/
def ExpLess (x y : Scope × String × Ty × Presence) : Prop := ScLess x.1 y.1 ∧ x.2 = y.2

/-- A scope that knows less expands fewer components (COMPONENTS OF a type it does not see), the
others alike. With `expandKnown`, all alike. -/
theorem expand_less : ∀ {n : Nat} {sc1 sc2 : Scope} {cs : List Comp}, ScLess sc1 sc2 →
    (∃ l, l.Sublist (expand E n sc2 cs) ∧ List.Forall₂ ExpLess (expand E n sc1 cs) l) ∧
    (expandKnown E n sc1 cs = true → List.Forall₂ ExpLess (expand E n sc1 cs) (expand E n sc2 cs))
  | 0, _, _, _, _ => by simp [expand, expandKnown]
  | n + 1, sc1, sc2, [], _ => by simp [expand]
  | n + 1, sc1, sc2, .mk nm t p :: rest, hsc => by
    obtain ⟨⟨l, hl, hf⟩, hk⟩ := expand_less (n := n) (cs := rest) hsc
    refine ⟨⟨(sc2, nm, t, p) :: l, by simp [expand]; exact hl, ?_⟩, fun h => ?_⟩
    · simp only [expand]; exact .cons ⟨hsc, rfl⟩ hf
    · simp only [expandKnown] at h
      simp only [expand]; exact .cons ⟨hsc, rfl⟩ (hk h)
  | n + 1, sc1, sc2, .componentsOf t :: rest, hsc => by
    obtain ⟨⟨l, hl, hf⟩, hk⟩ := expand_less (n := n) (cs := rest) hsc
    have head : (∃ l', l'.Sublist (match builtin E n sc2 t with
          | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expand E n sc' (r ++ r2)
          | _ => []) ∧
        List.Forall₂ ExpLess (match builtin E n sc1 t with
          | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expand E n sc' (r ++ r2)
          | _ => []) l') ∧
        ((match builtin E n sc1 t with
          | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expandKnown E n sc' (r ++ r2)
          | _ => false) = true →
          List.Forall₂ ExpLess (match builtin E n sc1 t with
            | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expand E n sc' (r ++ r2)
            | _ => []) (match builtin E n sc2 t with
            | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expand E n sc' (r ++ r2)
            | _ => [])) := by
      cases hb : builtin E n sc1 t with
      | none => simp
      | some p =>
        obtain ⟨s1, b⟩ := p
        obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
        rw [hb2]
        cases b with
        | sequence r e r2 =>
          obtain ⟨⟨l', hl', hf'⟩, hk'⟩ := expand_less (n := n) (cs := r ++ r2) hs
          exact ⟨⟨l', hl', hf'⟩, hk'⟩
        | set r e r2 =>
          obtain ⟨⟨l', hl', hf'⟩, hk'⟩ := expand_less (n := n) (cs := r ++ r2) hs
          exact ⟨⟨l', hl', hf'⟩, hk'⟩
        | _ => simp
    obtain ⟨⟨l', hl', hf'⟩, hk'⟩ := head
    refine ⟨⟨l' ++ l, by simp only [expand]; exact hl'.append hl, ?_⟩, fun h => ?_⟩
    · simp only [expand]; exact forall₂_append hf' hf
    · simp only [expandKnown, Bool.and_eq_true] at h
      simp only [expand]; exact forall₂_append (hk' h.1) (hk h.2)



theorem forall₂_map {α β γ δ} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hfg : ∀ x y, R x y → S (f x) (g y)) : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ S (l1.map f) (l2.map g)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (hfg _ _ h1) (forall₂_map hfg h2)

/-- Two components alike, read in scopes the first knowing less. -/
def EntLess (a b : Entry) : Prop :=
  ScLess a.scope b.scope ∧ a.name = b.name ∧ a.ty = b.ty ∧ a.presence = b.presence ∧
    a.addition = b.addition ∧ a.group = b.group

theorem entries_less {n : Nat} {sc1 sc2 : Scope} {r r2 : List Comp} {e : Option (List ExtAdd)}
    (hsc : ScLess sc1 sc2) :
    (∃ l, l.Sublist (entries E n sc2 r e r2) ∧ List.Forall₂ EntLess (entries E n sc1 r e r2) l) ∧
    (entriesKnown E n sc1 r e r2 = true →
      List.Forall₂ EntLess (entries E n sc1 r e r2) (entries E n sc2 r e r2)) := by
  have mk : ∀ (a : Option Nat) (g : Bool) (x y : Scope × String × Ty × Presence), ExpLess x y →
      EntLess ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, a, g⟩ ⟨y.1, y.2.1, y.2.2.1, y.2.2.2, a, g⟩ := by
    rintro a g x y ⟨h1, h2⟩
    exact ⟨h1, by rw [h2], by rw [h2], by rw [h2], rfl, rfl⟩
  obtain ⟨⟨l1, hl1, hf1⟩, hk1⟩ := expand_less (E := E) (n := n) (cs := r) hsc
  obtain ⟨⟨l3, hl3, hf3⟩, hk3⟩ := expand_less (E := E) (n := n) (cs := r2) hsc
  have mid : ∀ (xs : List (ExtAdd × Nat)),
      (∃ l, l.Sublist (xs.flatMap fun (e, i) => (expand E n sc2 e.comps).map
          (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, some i, e.isGroup⟩ : Entry))) ∧
        List.Forall₂ EntLess (xs.flatMap fun (e, i) => (expand E n sc1 e.comps).map
          (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, some i, e.isGroup⟩ : Entry))) l) ∧
      ((∀ p ∈ xs, expandKnown E n sc1 p.1.comps = true) →
        List.Forall₂ EntLess (xs.flatMap fun (e, i) => (expand E n sc1 e.comps).map
          (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, some i, e.isGroup⟩ : Entry)))
          (xs.flatMap fun (e, i) => (expand E n sc2 e.comps).map
          (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, some i, e.isGroup⟩ : Entry)))) := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih =>
      obtain ⟨⟨l, hl, hf⟩, hk⟩ := ih
      obtain ⟨⟨lp, hlp, hfp⟩, hkp⟩ := expand_less (E := E) (n := n) (cs := p.1.comps) hsc
      refine ⟨⟨lp.map (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, some p.2, p.1.isGroup⟩ : Entry)) ++ l,
        ?_, ?_⟩, fun h => ?_⟩
      · simp only [List.flatMap_cons]; exact (hlp.map _).append hl
      · simp only [List.flatMap_cons]; exact forall₂_append (forall₂_map (mk _ _) hfp) hf
      · simp only [List.flatMap_cons]
        exact forall₂_append (forall₂_map (mk _ _) (hkp (h p (by simp))))
          (hk fun q hq => h q (by simp [hq]))
  obtain ⟨⟨l2, hl2, hf2⟩, hk2⟩ := mid ((e.getD []).zipIdx)
  refine ⟨⟨l1.map (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, none, false⟩ : Entry)) ++ l2 ++
      l3.map (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2, none, false⟩ : Entry)), ?_, ?_⟩, fun h => ?_⟩
  · simp only [entries]; exact ((hl1.map _).append hl2).append (hl3.map _)
  · simp only [entries]
    exact forall₂_append (forall₂_append (forall₂_map (mk _ _) hf1) hf2) (forall₂_map (mk _ _) hf3)
  · simp only [entriesKnown, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [entries]
    exact forall₂_append (forall₂_append (forall₂_map (mk _ _) (hk1 h1))
      (hk2 fun q hq => h2 q.1 (List.fst_mem_of_mem_zipIdx hq))) (forall₂_map (mk _ _) (hk3 h3))

end Less

section Tags

variable {E : Env}

/-- Resolving in a scope that knows less, and at less fuel: what resolves, resolves alike. -/
theorem resolveTy_less_mono {n N : Nat} {sc1 sc2 : Scope} {mn : Option String} {name : String}
    {args : List Arg} {s1 : Scope} {t : Ty} (hsc : ScLess sc1 sc2) (hN : n ≤ N)
    (h : resolveTy E n sc1 mn name args = some (s1, t)) :
    ∃ s2, resolveTy E N sc2 mn name args = some (s2, t) ∧ ScLess s1 s2 := by
  obtain ⟨s2, h2, hs⟩ := resolveTy_less hsc h
  exact ⟨s2, resolveTy_mono h2 hN, hs⟩

theorem builtin_less_mono {n N : Nat} {sc1 sc2 : Scope} {t : Ty} {s1 : Scope} {b : Ty}
    (hsc : ScLess sc1 sc2) (hN : n ≤ N) (h : builtin E n sc1 t = some (s1, b)) :
    ∃ s2, builtin E N sc2 t = some (s2, b) ∧ ScLess s1 s2 := by
  obtain ⟨s2, h2, hs⟩ := builtin_less hsc h
  exact ⟨s2, builtin_mono h2 hN, hs⟩

theorem fields_bind_less_mono {n N : Nat} {sc1 sc2 : Scope} {cls : ClassRef} {path : List String}
    {r1 : Scope} {f : FieldSpec} (hsc : ScLess sc1 sc2) (hN : n ≤ N)
    (h : (classFields E n sc1 cls).bind (fun cf => fieldAt E n cf path) = some (r1, f)) :
    ∃ r2, (classFields E N sc2 cls).bind (fun cf => fieldAt E N cf path) = some (r2, f) ∧ ScLess r1 r2 := by
  obtain ⟨r2, h2, hs⟩ := fields_bind_less hsc h
  exact ⟨r2, bind_fields_mono h2 hN, hs⟩

theorem objSetClass_less_mono {n N : Nat} {sc1 sc2 : Scope} {os : ObjSet} {s1 : Scope} {c : ClassRef}
    (hsc : ScLess sc1 sc2) (hN : n ≤ N) (h : objSetClass E n sc1 os = some (s1, c)) :
    ∃ s2, objSetClass E N sc2 os = some (s2, c) ∧ ScLess s1 s2 := by
  obtain ⟨s2, h2, hs⟩ := objSetClass_less hsc h
  exact ⟨s2, objSetClass_mono h2 hN, hs⟩

/-- Where `builtin` resolves, `hasTag` has followed the same references. -/
theorem hasTag_less : ∀ {n N : Nat} {sc1 sc2 : Scope} {t : Ty} {s1 : Scope} {b : Ty},
    ScLess sc1 sc2 → n ≤ N → builtin E n sc1 t = some (s1, b) → hasTag E n sc1 t = hasTag E N sc2 t
  | 0, _, _, _, _, _, _, _, _, h => by simp [builtin] at h
  | _ + 1, 0, _, _, _, _, _, _, hN, _ => by omega
  | n + 1, N + 1, sc1, sc2, t, s1, b, hsc, hN, h => by
    cases t with
    | ref name =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [hasTag, h1, h1']
      exact hasTag_less hs (by omega) h2
    | extRef mn name =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [hasTag, h1, h1']
      exact hasTag_less hs (by omega) h2
    | paramRef mn name args =>
      simp only [builtin, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [hasTag, h1, h1']
      exact hasTag_less hs (by omega) h2
    | constrained u c => simp only [builtin] at h; simp only [hasTag]; exact hasTag_less hsc (by omega) h
    | selection nm u =>
      simp only [builtin] at h
      split at h
      · rename_i s root ext hb
        obtain ⟨s', hb', hs⟩ := builtin_less_mono hsc (by omega : n ≤ N) hb
        split at h
        · rename_i a ha
          simp only [hasTag, hb, hb', ha]
          exact hasTag_less hs (by omega) h
        · simp at h
      · simp at h
    | tagged tg k u => simp [hasTag]
    | _ => simp [hasTag]

theorem carriesConceptual_less : ∀ {n N : Nat} {sc1 sc2 : Scope} {t : Ty},
    ScLess sc1 sc2 → n ≤ N → carriesConceptual E n sc1 t = true → carriesConceptual E N sc2 t = true
  | 0, _, _, _, _, _, _, h => by simp [carriesConceptual] at h
  | _ + 1, 0, _, _, _, _, hN, _ => by omega
  | n + 1, N + 1, sc1, sc2, t, hsc, hN, h => by
    unfold carriesConceptual at h ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    obtain ⟨hnt, h⟩ := h
    split at h
    · rename_i s r e hb
      obtain ⟨s', hb', hs⟩ := builtin_less_mono hsc (by omega : n ≤ N) hb
      refine ⟨by rw [← hasTag_less hsc (by omega) hb]; exact hnt, ?_⟩
      rw [hb']; simp only
      rw [← hs.mod]
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
      rcases h with (h | h) | ⟨ha, a, hal, hc⟩
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr ⟨ha, a, hal, carriesConceptual_less hs (by omega) hc⟩
    · simp at h

theorem untaggedChoiceOrOpen_less {n N : Nat} {sc1 sc2 : Scope} {t : Ty} (hsc : ScLess sc1 sc2)
    (hN : n ≤ N) (h : untaggedChoiceOrOpen E n sc1 t = true) : untaggedChoiceOrOpen E N sc2 t = true := by
  have hco : (!hasTag E n sc1 t && match builtin E n sc1 t with
      | some (_, .choice _ _) | some (_, .openType) => true
      | _ => false) = true →
      (!hasTag E N sc2 t && match builtin E N sc2 t with
      | some (_, .choice _ _) | some (_, .openType) => true
      | _ => false) = true := by
    intro hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc ⊢
    obtain ⟨hnt, hc⟩ := hc
    split at hc
    · rename_i s r e hb
      obtain ⟨s', hb', hs⟩ := builtin_less_mono hsc hN hb
      exact ⟨by rw [← hasTag_less hsc hN hb]; exact hnt, by rw [hb']⟩
    · rename_i s hb
      obtain ⟨s', hb', hs⟩ := builtin_less_mono hsc hN hb
      exact ⟨by rw [← hasTag_less hsc hN hb]; exact hnt, by rw [hb']⟩
    · simp at hc
  unfold untaggedChoiceOrOpen at h ⊢
  cases t with
  | ref name =>
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · left
      have := (hsc.bound name).1
      cases h1 : sc1.bound name with
      | none => simp [h1] at h
      | some x => cases h2 : sc2.bound name with
        | none => simp [h1, h2] at this
        | some y => rfl
    · exact .inr (hco h)
  | _ => exact hco h


/-- The choice combination of `tagsOfB` and of `tagsOf`: known alternatives combine as in the spec. -/
theorem combine_known : ∀ {l1 : List (Option (Option (List Tag)))} {l2 : List (Option (List Tag))},
    List.Forall₂ (fun ob o => ∀ x, ob = some x → x = o) l1 l2 → ∀ {x},
    l1.foldr (fun ts acc => match ts, acc with
      | some x, some y => some (match x, y with
        | some a, some b => some (a ++ b)
        | _, _ => none)
      | _, _ => none) (some (some [])) = some x →
    l2.foldr (fun ts acc => match ts, acc with
      | some a, some b => some (a ++ b)
      | _, _ => none) (some []) = x
  | [], [], .nil, x, h => by simp at h; simp [h]
  | ob :: l1, o :: l2, .cons hob hrest, x, h => by
    simp only [List.foldr_cons] at h ⊢
    cases ob with
    | none => simp at h
    | some y =>
      have hy := hob y rfl; subst hy
      cases hf : l1.foldr (fun ts acc => match ts, acc with
          | some x, some y => some (match x, y with
            | some a, some b => some (a ++ b)
            | _, _ => none)
          | _, _ => none) (some (some [])) with
      | none => rw [hf] at h; simp at h
      | some z =>
        rw [hf] at h
        have hz := combine_known hrest hf
        simp only [Option.some.injEq] at h
        rw [hz]
        cases y <;> cases z <;> (simp only [Option.some.injEq] at h ⊢; try exact h)

theorem tagsOfB_less : ∀ {n N : Nat} {sc1 sc2 : Scope} {t : Ty} {o : Option (List Tag)},
    ScLess sc1 sc2 → n ≤ N → tagsOfB E n sc1 t = some o → tagsOf E N sc2 t = o
  | 0, _, _, _, _, _, _, _, h => by simp [tagsOfB] at h
  | _ + 1, 0, _, _, _, _, _, hN, _ => by omega
  | n + 1, N + 1, sc1, sc2, t, o, hsc, hN, h => by
    cases t with
    | tagged tg k u => simp [tagsOfB] at h; simp [tagsOf, h]
    | ref name =>
      simp only [tagsOfB, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [tagsOf, h1']
      exact tagsOfB_less hs (by omega) h2
    | extRef mn name =>
      simp only [tagsOfB, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [tagsOf, h1']
      exact tagsOfB_less hs (by omega) h2
    | paramRef mn name args =>
      simp only [tagsOfB, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s, u⟩, h1, h2⟩ := h
      obtain ⟨s', h1', hs⟩ := resolveTy_less_mono hsc (by omega : n ≤ N) h1
      simp only [tagsOf, h1']
      exact tagsOfB_less hs (by omega) h2
    | constrained u c => simp only [tagsOfB] at h; simp only [tagsOf]; exact tagsOfB_less hsc (by omega) h
    | selection nm u =>
      simp only [tagsOfB] at h
      split at h
      · rename_i s root ext hb
        obtain ⟨s', hb', hs⟩ := builtin_less_mono hsc (by omega : n ≤ N) hb
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨a, ha, h⟩ := h
        simp only [tagsOf, hb', ha]
        exact tagsOfB_less hs (by omega) h
      · simp at h
    | choice r e =>
      simp only [tagsOfB] at h
      simp only [tagsOf]
      refine combine_known ?_ h
      cases n with
      | zero =>
        cases hr : choiceAlts r e with
        | nil =>
          have : altTags E N sc2 r e = [] := by
            cases N with
            | zero => simp [altTags]
            | succ N => simp only [altTags, hr]; split <;> simp
          simp [altTagsB, hr, this]
        | cons a rest =>
          exfalso
          simp [altTagsB, hr] at h
      | succ k =>
        obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
        simp only [altTagsB, altTags, ← hsc.mod]
        split
        · rw [List.map_map, List.map_map]
          apply List.forall₂_iff_get.mpr
          refine ⟨by simp, fun i h1 h2 => ?_⟩
          simp
        · rw [List.map_map, List.map_map]
          apply List.forall₂_iff_get.mpr
          refine ⟨by simp, fun i h1 h2 => ?_⟩
          simp only [List.get_eq_getElem, List.getElem_map, Function.comp]
          intro x hx
          exact (tagsOfB_less hsc (by omega) hx).symm
    | openType => simp [tagsOfB] at h; simp [tagsOf, ← h]
    | classField cls path =>
      simp only [tagsOfB] at h
      simp only [tagsOf]
      cases hb : (classFields E n sc1 cls).bind (fun cf => fieldAt E n cf path) with
      | none => rw [hb] at h; simp at h
      | some p =>
        obtain ⟨s, f⟩ := p
        obtain ⟨s', hb', hs⟩ := fields_bind_less_mono hsc (by omega : n ≤ N) hb
        rw [hb']; rw [hb] at h
        cases f with
        | fixedValue nm u un o' => exact tagsOfB_less hs (by omega) h
        | fixedValueSet nm u o' => exact tagsOfB_less hs (by omega) h
        | _ => simp at h; simp [h]
    | instanceOf cls => simp [tagsOfB] at h; simp [tagsOf, ← h]
    | fromObjects src path =>
      simp only [tagsOfB] at h
      simp only [tagsOf]
      cases hc : objSetClass E n sc1 src with
      | none => rw [hc] at h; simp at h
      | some q =>
        obtain ⟨csc, cls⟩ := q
        obtain ⟨csc', hc', hcs⟩ := objSetClass_less_mono hsc (by omega : n ≤ N) hc
        rw [hc']; rw [hc] at h
        simp only at h ⊢
        cases hb : (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
        | none => rw [hb] at h; simp at h
        | some p =>
          obtain ⟨s, f⟩ := p
          obtain ⟨s', hb', hs⟩ := fields_bind_less_mono hcs (by omega : n ≤ N) hb
          rw [hb']; rw [hb] at h
          cases f with
          | fixedValue nm u un o' => exact tagsOfB_less hs (by omega) h
          | fixedValueSet nm u o' => exact tagsOfB_less hs (by omega) h
          | _ => simp at h; simp [h]
    | _ => simp [tagsOfB] at h; simp [tagsOf, ← h]


theorem expandKnown_less : ∀ {n : Nat} {sc1 sc2 : Scope} {l : List Comp}, ScLess sc1 sc2 →
    expandKnown E n sc1 l = true → expandKnown E n sc2 l = true
  | 0, _, _, _, _, h => by simp [expandKnown] at h
  | _ + 1, _, _, [], _, _ => by simp [expandKnown]
  | n + 1, sc1, sc2, .mk .. :: rest, hsc, h => by
    simp only [expandKnown] at h ⊢; exact expandKnown_less hsc h
  | n + 1, sc1, sc2, .componentsOf t :: rest, hsc, h => by
    simp only [expandKnown, Bool.and_eq_true] at h ⊢
    refine ⟨?_, expandKnown_less hsc h.2⟩
    obtain ⟨h1, -⟩ := h
    split at h1
    · rename_i s r e r2 hb
      obtain ⟨s', hb', hs⟩ := builtin_less hsc hb
      rw [hb']; exact expandKnown_less hs h1
    · rename_i s r e r2 hb
      obtain ⟨s', hb', hs⟩ := builtin_less hsc hb
      rw [hb']; exact expandKnown_less hs h1
    · simp at h1

theorem entriesKnown_less {n : Nat} {sc1 sc2 : Scope} {r r2 : List Comp} {e : Option (List ExtAdd)}
    (hsc : ScLess sc1 sc2) (h : entriesKnown E n sc1 r e r2 = true) : entriesKnown E n sc2 r e r2 = true := by
  simp only [entriesKnown, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨expandKnown_less hsc h.1.1, fun x hx => expandKnown_less hsc (h.1.2 x hx)⟩,
    expandKnown_less hsc h.2⟩

/-! ### Lists that relate place by place -/

theorem forall₂_getElem? {α β} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → ∀ (i : Nat), (∀ x, l1[i]? = some x → ∃ y, l2[i]? = some y ∧ R x y) ∧
      (l1[i]? = none ↔ l2[i]? = none)
  | [], [], .nil, i => by simp
  | x :: xs, y :: ys, .cons h hr, 0 => by simp [h]
  | x :: xs, y :: ys, .cons h hr, i + 1 => by simpa using forall₂_getElem? hr i

theorem forall₂_filter {α β} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ x y, R x y → p x = q y) : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R (l1.filter p) (l2.filter q)
  | [], [], .nil => .nil
  | x :: xs, y :: ys, .cons h hr => by
    simp only [List.filter_cons, hpq x y h]
    split
    · exact .cons h (forall₂_filter hpq hr)
    · exact forall₂_filter hpq hr

theorem forall₂_take {α β} {R : α → β → Prop} : ∀ (k : Nat) {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R (l1.take k) (l2.take k)
  | 0, _, _, _ => by simp
  | _ + 1, [], [], .nil => .nil
  | k + 1, _ :: _, _ :: _, .cons h hr => .cons h (forall₂_take k hr)

theorem forall₂_drop {α β} {R : α → β → Prop} : ∀ (k : Nat) {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R (l1.drop k) (l2.drop k)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], .nil => .nil
  | k + 1, _ :: _, _ :: _, .cons _ hr => forall₂_drop k hr

theorem forall₂_zip {α β γ} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β} (ns : List γ),
    List.Forall₂ R l1 l2 → List.Forall₂ (fun a b => R a.1 b.1 ∧ a.2 = b.2) (l1.zip ns) (l2.zip ns)
  | [], [], _, .nil => by simp
  | _ :: _, _ :: _, [], .cons _ _ => by simp
  | _ :: _, _ :: _, _ :: ns, .cons h hr => .cons ⟨h, rfl⟩ (forall₂_zip ns hr)

theorem sublist_flatMap {α β γ} {f : α → List γ} {g : β → List γ} : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ (fun x y => (f x).Sublist (g y)) l1 l2 → (l1.flatMap f).Sublist (l2.flatMap g)
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons h hr => by simp only [List.flatMap_cons]; exact h.append (sublist_flatMap hr)

theorem sublist_filterMap {α β γ} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ x y, R x y → ∀ t, f x = some t → g y = some t) : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → (l1.filterMap f).Sublist (l2.filterMap g)
  | [], [], .nil => by simp
  | x :: xs, y :: ys, .cons h hr => by
    simp only [List.filterMap_cons]
    cases hx : f x with
    | none =>
      simp only
      split
      · exact sublist_filterMap hfg hr
      · exact (sublist_filterMap hfg hr).cons _
    | some t =>
      rw [hfg x y h t hx]
      exact (sublist_filterMap hfg hr).cons_cons t

theorem RunsDistinct.of_sublist {s1 s2 : List (List CTag × Bool)}
    (h : List.Forall₂ (fun a b => a.1.Sublist b.1 ∧ a.2 = b.2) s1 s2) (h2 : RunsDistinct s2) :
    RunsDistinct s1 := by
  intro i j hij hrun x y hx hy t ht u hu
  obtain ⟨x2, hx2, hxs, -⟩ := (forall₂_getElem? h i).1 x hx
  obtain ⟨y2, hy2, hys, -⟩ := (forall₂_getElem? h j).1 y hy
  refine h2 i j hij (fun k hk1 hk2 => ?_) x2 y2 hx2 hy2 t (hxs.subset ht) u (hys.subset hu)
  obtain ⟨z, hz, hz2⟩ := hrun k hk1 hk2
  obtain ⟨z2, hz2', -, hzz⟩ := (forall₂_getElem? h k).1 z hz
  exact ⟨z2, hz2', by rw [← hzz]; exact hz2⟩

end Tags


section RulesLess

variable {E : Env} {n : Nat} {sc1 sc2 : Scope}

theorem entLess_names : ∀ {l1 l2 : List Entry}, List.Forall₂ EntLess l1 l2 →
    l1.map (·.name) = l2.map (·.name)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hr => by simp [h.2.1, entLess_names hr]

theorem namesOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : namesOkB E n sc2 s = true) :
    namesOkB E n sc1 s = true := by
  cases s with
  | sequence r e r2 =>
    simp only [namesOkB, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨l, hl, hf⟩, -⟩ := entries_less (E := E) (n := n) (r := r) (e := e) (r2 := r2) hsc
    rw [entLess_names hf]
    exact h.sublist (hl.map _)
  | set r e r2 =>
    simp only [namesOkB, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨l, hl, hf⟩, -⟩ := entries_less (E := E) (n := n) (r := r) (e := e) (r2 := r2) hsc
    rw [entLess_names hf]
    exact h.sublist (hl.map _)
  | _ => simp_all [namesOkB]

theorem autoAdditionsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : autoAdditionsOkB sc2 s = true) :
    autoAdditionsOkB sc1 s = true := by
  cases s <;> simp_all [autoAdditionsOkB, hsc.mod]

/-- A name that is not a dummy resolves alike in the two scopes. -/
theorem resolveIn_isSome_less {α : Type} {mn : Option String} {name : String} {args : List Arg}
    {F : Arg → Option ParamGov → Scope → Option (Scope × α)} {fromModule : Module → Option α}
    {fromParam : ParamAssign → Option (List Param × α)} (hsc : ScLess sc1 sc2)
    (hb : mn ≠ none ∨ args ≠ [] ∨ sc2.bound name = none) :
    (resolveIn E n sc1 mn name args F fromModule fromParam).isSome =
      (resolveIn E n sc2 mn name args F fromModule fromParam).isSome := by
  have hmod := hsc.mod
  have hb1 : (sc1.bound name).isNone ↔ (sc2.bound name).isNone := (hsc.bound name).1
  unfold resolveIn
  rw [hmod]
  cases mn with
  | some m => cases args <;> simp
  | none =>
    cases args with
    | cons a as => simp
    | nil =>
      have h2 : sc2.bound name = none := by simpa using hb
      have h1 : sc1.bound name = none := by
        have := hb1.mpr (by simp [h2]); simpa using this
      simp [h1, h2]

theorem ScLess.bound_isSome (hsc : ScLess sc1 sc2) (name : String) :
    (sc1.bound name).isSome = (sc2.bound name).isSome := by
  have := (hsc.bound name).1
  cases h1 : sc1.bound name <;> cases h2 : sc2.bound name <;> simp_all

theorem refsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : refsOkB E n sc2 s = true) :
    refsOkB E n sc1 s = true := by
  have hb := fun name => (hsc.bound name).1
  cases s with
  | ref name =>
    simp only [refsOkB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · left; rw [hsc.bound_isSome]; exact h
    · by_cases hbd : (sc2.bound name).isSome
      · left; rw [hsc.bound_isSome]; exact hbd
      · right
        unfold resolveTy at h ⊢
        rw [resolveIn_isSome_less hsc (.inr (.inr (by simpa using hbd)))]; exact h
  | extRef mn name =>
    simp only [refsOkB] at h ⊢
    unfold resolveTy at h ⊢
    rw [resolveIn_isSome_less hsc (.inl (by simp))]; exact h
  | paramRef mn name args =>
    cases mn with
    | none =>
      simp only [refsOkB, Bool.and_eq_true] at h ⊢
      have hn2 : sc2.bound name = none := by simpa using h.1
      refine ⟨by have := (hb name).mpr h.1; exact this, ?_⟩
      unfold resolveTy at h ⊢
      rw [resolveIn_isSome_less hsc (.inr (.inr hn2))]; exact h.2
    | some m =>
      simp only [refsOkB] at h ⊢
      unfold resolveTy at h ⊢
      rw [resolveIn_isSome_less hsc (.inl (by simp))]; exact h
  | selection nm t =>
    simp only [refsOkB] at h ⊢
    split
    · rename_i s r e hb1
      obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb1
      rw [hb2] at h; exact h
    · rename_i s b hne hb1
      obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb1
      rw [hb2] at h
      cases b <;> simp_all
    · rfl
  | _ => simpa [refsOkB] using h

theorem mayBe_less (hsc : ScLess sc1 sc2) {gov : Option ParamGov → Bool} {mn : Option String} {nm : String}
    (h : sc2.mayBe gov mn nm = true) : sc1.mayBe gov mn nm = true := by
  cases mn with
  | some _ => simp [Scope.mayBe] at h
  | none =>
    simp only [Scope.mayBe] at h ⊢
    cases h2 : sc2.bound nm with
    | none =>
      rw [h2] at h
      have h1 : sc1.bound nm = none := by
        have := (hsc.bound nm).1.mpr (by simp [h2]); simpa using this
      rw [h1, hsc.mod]; exact h
    | some x =>
      obtain ⟨a2, g2, c2⟩ := x
      rw [h2] at h
      cases h1 : sc1.bound nm with
      | none => have := (hsc.bound nm).1.mp (by simp [h1]); simp [h2] at this
      | some y =>
        obtain ⟨a1, g1, c1⟩ := y
        obtain ⟨a2', c2', h2', -⟩ := (hsc.bound nm).2 a1 g1 c1 h1
        rw [h2] at h2'; simp at h2'; obtain ⟨-, rfl, -⟩ := h2'
        exact h

/-- A dummy that resolves to an object or object set in the scope that knows more is one its
governor allows: the scope that knows less may take it for one. -/
theorem bound_objects {mn : Option String} {nm : String} {args : List Arg} (hsc : ScLess sc1 sc2)
    (G : Arg → Option ParamGov → Option α) (hG : ∀ a g x, G a g = some x → ∃ o, a = .obj o ∨ ∃ s, a = .objSet s)
    {F : Module → Option α} {P : ParamAssign → Option (List Param × α)}
    (h : (resolveIn E n sc2 mn nm args (fun a g c => (G a g).map fun x => (c, x)) F P).isSome) :
    (resolveIn E n sc1 mn nm args (fun a g c => (G a g).map fun x => (c, x)) F P).isSome ∨
      sc1.mayBe govObjects mn nm = true := by
  by_cases hb : mn ≠ none ∨ args ≠ [] ∨ sc2.bound nm = none
  · left; rw [resolveIn_isSome_less hsc hb]; exact h
  · push Not at hb
    obtain ⟨rfl, rfl, hb2⟩ := hb
    obtain ⟨⟨a2, g2, c2⟩, hb2'⟩ := Option.ne_none_iff_exists'.mp hb2
    obtain ⟨⟨a1, g1, c1⟩, hb1⟩ : ∃ y, sc1.bound nm = some y := by
      have := (hsc.bound nm).1.not.mpr (by simp [hb2']); exact Option.ne_none_iff_exists'.mp (by simpa using this)
    obtain ⟨a2', c2', hb2'', hrel⟩ := (hsc.bound nm).2 a1 g1 c1 hb1
    rw [hb2'] at hb2''; simp at hb2''; obtain ⟨rfl, rfl, rfl⟩ := hb2''
    rcases hrel with ⟨rfl, hk⟩ | ⟨rfl, hc⟩
    · right
      simp only [Scope.mayBe, hb1]
      unfold resolveIn at h; simp only [hb2'] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      simp only [Option.map_eq_some_iff] at hx
      obtain ⟨y, hy, -⟩ := hx
      obtain ⟨o, rfl | ⟨s, rfl⟩⟩ := hG _ _ _ hy <;> (cases g2 with
        | none => simp [ArgKindOk] at hk
        | some g => cases g <;> simp_all [ArgKindOk, govObjects])
    · left
      unfold resolveIn at h ⊢; simp only [hb2', hb1, Option.isSome_map] at h ⊢; exact h



theorem resolveObj_eq (sc : Scope) (mn : Option String) (name : String) (args : List Arg) :
    resolveObj E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (objArg a g).map fun x => (c, x))
      (fun m => (m.objects.find? (·.1 == name)).map fun (_, c, o) => (some c, o))
      (fun | .obj _ ps c o => some (ps, some c, o) | _ => none) := by
  unfold resolveObj; congr 1; funext a g c; cases a <;> simp [objArg]

theorem resolveObjSet_eq (sc : Scope) (mn : Option String) (name : String) (args : List Arg) :
    resolveObjSet E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (objSetArg a g).map fun x => (c, x))
      (fun m => (m.objectSets.find? (·.1 == name)).map fun (_, c, s) => (some c, s))
      (fun | .objSet _ ps c s => some (ps, some c, s) | _ => none) := by
  unfold resolveObjSet; congr 1; funext a g c; cases a <;> simp [objSetArg]

theorem resolveClass_eq (sc : Scope) (mn : Option String) (name : String) (args : List Arg) :
    resolveClass E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (clsArg a g).map fun x => (c, x))
      (fun m => (m.classes.find? (·.1 == name)).map (·.2))
      (fun | .cls _ ps c => some (ps, c) | _ => none) := by
  unfold resolveClass; congr 1; funext a g c; cases a <;> simp [clsArg]

theorem resolveVal_eq (sc : Scope) (mn : Option String) (name : String) (args : List Arg) :
    resolveVal E n sc mn name args = resolveIn E n sc mn name args
      (fun a g c => (valArg a g).map fun x => (c, x))
      (fun m => (m.values.find? (·.1 == name)).map (·.2.2))
      (fun | .value _ ps _ v => some (ps, v) | _ => none) := by
  unfold resolveVal; congr 1; funext a g c; cases a <;> simp [valArg]

/-- A dummy that resolves to a class in the scope that knows more is one its governor allows. -/
theorem bound_class {mn : Option String} {nm : String} {args : List Arg} (hsc : ScLess sc1 sc2)
    (h : (resolveClass E n sc2 mn nm args).isSome) :
    (resolveClass E n sc1 mn nm args).isSome ∨ sc1.mayBe govClass mn nm = true := by
  rw [resolveClass_eq] at h ⊢
  by_cases hb : mn ≠ none ∨ args ≠ [] ∨ sc2.bound nm = none
  · left; rw [resolveIn_isSome_less hsc hb]; exact h
  · push Not at hb
    obtain ⟨rfl, rfl, hb2⟩ := hb
    obtain ⟨⟨a2, g2, c2⟩, hb2'⟩ := Option.ne_none_iff_exists'.mp hb2
    obtain ⟨⟨a1, g1, c1⟩, hb1⟩ : ∃ y, sc1.bound nm = some y := by
      have := (hsc.bound nm).1.not.mpr (by simp [hb2']); exact Option.ne_none_iff_exists'.mp (by simpa using this)
    obtain ⟨a2', c2', hb2'', hrel⟩ := (hsc.bound nm).2 a1 g1 c1 hb1
    rw [hb2'] at hb2''; simp at hb2''; obtain ⟨rfl, rfl, rfl⟩ := hb2''
    rcases hrel with ⟨rfl, hk⟩ | ⟨rfl, hc⟩
    · right
      simp only [Scope.mayBe, hb1]
      unfold resolveIn at h; simp only [hb2'] at h
      cases a2 <;> simp [clsArg] at h
      cases g2 with
      | none => rfl
      | some g => cases g <;> simp [ArgKindOk] at hk
    · left
      unfold resolveIn at h ⊢; simp only [hb2', hb1, Option.isSome_map] at h ⊢; exact h

mutual
theorem oelemsRefsOkB_less (hsc : ScLess sc1 sc2) : ∀ {e : OElems},
    oelemsRefsOkB E n sc2 e = true → oelemsRefsOkB E n sc1 e = true
  | .obj (.ref mn nm args), h => by
    simp only [oelemsRefsOkB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rw [resolveObj_eq] at h ⊢
      rcases bound_objects hsc objArg (fun a g x hx => by
        cases a <;> simp [objArg] at hx; exact ⟨_, .inl rfl⟩) h with h1 | h1
      · exact .inl h1
      · exact .inr h1
    · exact .inr (mayBe_less hsc h)
  | .obj (.defn _), _ | .obj (.fromObject ..), _ | .obj (.raw _), _ => by simp [oelemsRefsOkB]
  | .set s, h => by simp only [oelemsRefsOkB] at h ⊢; exact objSetRefsOkB_less hsc h
  | .fromObjects s _, h => by simp only [oelemsRefsOkB] at h ⊢; exact objSetRefsOkB_less hsc h
  | .union a b, h | .inter a b, h | .except a b, h => by
    simp only [oelemsRefsOkB, Bool.and_eq_true] at h ⊢
    exact ⟨oelemsRefsOkB_less hsc h.1, oelemsRefsOkB_less hsc h.2⟩
theorem objSetRefsOkB_less (hsc : ScLess sc1 sc2) : ∀ {os : ObjSet},
    oelemsRefsOkB.objSetRefsOkB E n sc2 os = true → oelemsRefsOkB.objSetRefsOkB E n sc1 os = true
  | .ref mn nm args, h => by
    simp only [oelemsRefsOkB.objSetRefsOkB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rw [resolveObjSet_eq] at h ⊢
      rcases bound_objects hsc objSetArg (fun a g x hx => by
        cases a <;> simp [objSetArg] at hx; exact ⟨.raw [], .inr ⟨_, rfl⟩⟩) h with h1 | h1
      · exact .inl h1
      · exact .inr h1
    · exact .inr (mayBe_less hsc h)
  | .spec (some r) _ (some a), h => by
    simp only [oelemsRefsOkB.objSetRefsOkB, Bool.and_eq_true] at h ⊢
    exact ⟨oelemsRefsOkB_less hsc h.1, oelemsRefsOkB_less hsc h.2⟩
  | .spec (some r) _ none, h => by
    simp only [oelemsRefsOkB.objSetRefsOkB] at h ⊢; exact oelemsRefsOkB_less hsc h
  | .spec none _ (some a), h => by
    simp only [oelemsRefsOkB.objSetRefsOkB] at h ⊢; exact oelemsRefsOkB_less hsc h
  | .spec none _ none, _ => by simp [oelemsRefsOkB.objSetRefsOkB]
end

theorem valRefsOkB_less (hsc : ScLess sc1 sc2) {v : Val} (h : valRefsOkB E n sc2 v = true) :
    valRefsOkB E n sc1 v = true := by
  simp only [valRefsOkB, List.all_eq_true] at h ⊢
  rintro ⟨mn, nm, args⟩ hr
  have h' := h _ hr
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h' ⊢
  rcases h' with ⟨⟨hmn, hargs⟩, hb⟩ | h'
  · left; exact ⟨⟨hmn, hargs⟩, by rw [hsc.bound_isSome]; exact hb⟩
  · by_cases hb : mn ≠ none ∨ args ≠ [] ∨ sc2.bound nm = none
    · right; rw [resolveVal_eq] at h' ⊢; rw [resolveIn_isSome_less hsc hb]; exact h'
    · push Not at hb
      obtain ⟨rfl, rfl, hb2⟩ := hb
      left
      refine ⟨⟨rfl, rfl⟩, ?_⟩
      rw [hsc.bound_isSome]; exact Option.isSome_iff_ne_none.mpr hb2

theorem consRefsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : consRefsOkB E n sc2 s = true) :
    consRefsOkB E n sc1 s = true := by
  cases s with
  | constrained t c =>
    simp only [consRefsOkB, Bool.or_eq_true, Option.isNone_iff_eq_none, List.all_eq_true] at h ⊢
    cases hb : builtin E n sc1 t with
    | none => exact .inl rfl
    | some p =>
      obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
      rcases h with h | h
      · rw [hb2] at h; cases h
      · exact .inr fun v hv => valRefsOkB_less hsc (h v hv)
  | _ => rfl

theorem defaultRefsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : defaultRefsOkB E n sc2 s = true) :
    defaultRefsOkB E n sc1 s = true := by
  have key : ∀ (c : Comp), (match c with
      | .mk _ t (.default_ v) => (builtin E n sc2 t).isNone || valRefsOkB E n sc2 v
      | _ => true) = true → (match c with
      | .mk _ t (.default_ v) => (builtin E n sc1 t).isNone || valRefsOkB E n sc1 v
      | _ => true) = true := by
    intro c hc
    split
    · rename_i nm t v
      simp only at hc
      simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hc ⊢
      cases hb : builtin E n sc1 t with
      | none => exact .inl rfl
      | some p =>
        obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
        rcases hc with hc | hc
        · rw [hb2] at hc; cases hc
        · exact .inr (valRefsOkB_less hsc hc)
    · rfl
  cases s with
  | sequence r e r2 =>
    simp only [defaultRefsOkB, List.all_eq_true] at h ⊢; exact fun c hc => key c (h c hc)
  | set r e r2 =>
    simp only [defaultRefsOkB, List.all_eq_true] at h ⊢; exact fun c hc => key c (h c hc)
  | _ => rfl

theorem fieldMissingB_less : ∀ {n : Nat} {s1 s2 : Scope} {fs : List FieldSpec} {path : List String},
    ScLess s1 s2 → fieldMissingB E n (s1, fs) path = true → fieldMissingB E n (s2, fs) path = true
  | 0, _, _, _, _, _, h => by simp [fieldMissingB] at h
  | _ + 1, _, _, _, [], _, h => by simp [fieldMissingB]
  | _ + 1, _, _, _, [f], _, h => by simpa [fieldMissingB] using h
  | n + 1, s1, s2, fs, f :: g :: rest, hs, h => by
    simp only [fieldMissingB] at h ⊢
    split at h
    · rename_i nm c o hf
      cases hc : classFields E n s1 c with
      | none => rw [hc] at h; cases h
      | some cf =>
        rw [hc] at h
        obtain ⟨cs2, hc2, hcs⟩ := classFields_less hs hc
        rw [hc2]; exact fieldMissingB_less hcs h
    · rename_i nm c o hf
      cases hc : classFields E n s1 c with
      | none => rw [hc] at h; cases h
      | some cf =>
        rw [hc] at h
        obtain ⟨cs2, hc2, hcs⟩ := classFields_less hs hc
        rw [hc2]; exact fieldMissingB_less hcs h
    · rfl

theorem classRefsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : classRefsOkB E n sc2 s = true) :
    classRefsOkB E n sc1 s = true := by
  have hcls : ∀ {mn : Option String} {name : String} {args : List Arg},
      ((resolveClass E n sc2 mn name args).isSome || sc2.mayBe govClass mn name) = true →
      ((resolveClass E n sc1 mn name args).isSome || sc1.mayBe govClass mn name) = true := by
    intro mn name args h
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact bound_class hsc h
    · exact .inr (mayBe_less hsc h)
  cases s with
  | instanceOf c =>
    cases c with
    | ref mn name args => simp only [classRefsOkB] at h ⊢; exact hcls h
    | _ => simp [classRefsOkB]
  | classField cls path =>
    simp only [classRefsOkB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · cases cls with
      | ref mn name args => exact hcls h.1
      | _ => rfl
    · cases hc : classFields E n sc1 cls with
      | none => rfl
      | some cf =>
        obtain ⟨s1, fs⟩ := cf
        obtain ⟨s2, hc2, hs⟩ := classFields_less hsc hc
        have h2 := h.2; rw [hc2] at h2
        simp only [Bool.not_eq_true'] at h2 ⊢
        cases hm : fieldMissingB E n (s1, fs) path with
        | false => rfl
        | true => rw [fieldMissingB_less hs hm] at h2; cases h2
  | _ => rfl



theorem argsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : argsOkB E n sc2 s = true) :
    argsOkB E n sc1 s = true := by
  cases s with
  | paramRef mn name args =>
    simp only [argsOkB, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [List.all_eq_true] at h1 ⊢
      intro a ha
      have := h1 a ha
      split
      · rename_i o; simp only at this; exact oelemsRefsOkB_less hsc this
      · rename_i os; simp only at this; exact objSetRefsOkB_less hsc this
      · rfl
    · cases mn with
      | some _ => rfl
      | none =>
        simp only at h2 ⊢
        rw [hsc.mod] at ⊢
        split
        · rename_i pa hpa
          rw [hpa] at h2
          simp only [List.all_eq_true] at h2 ⊢
          intro ⟨a, p⟩ hap
          have := h2 ⟨a, p⟩ hap
          simp only at this ⊢
          cases a with
          | value v =>
            cases hg : p.governor with
            | none => rfl
            | some g =>
              cases g with
              | type t =>
                rw [hg] at this
                simp only at this ⊢
                cases hb : builtin E n sc1 t with
                | none => rfl
                | some q =>
                  obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
                  rw [hb2] at this
                  obtain ⟨s', bt⟩ := q
                  cases bt with
                  | enumerated => rfl
                  | integer nm =>
                    cases nm with
                    | nil => exact valRefsOkB_less hsc this
                    | cons _ _ => rfl
                  | _ => exact valRefsOkB_less hsc this
              | _ => rfl
          | _ => rfl
        · rfl
  | _ => rfl

theorem typeFromObjectsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : typeFromObjectsOkB E n sc2 s = true) :
    typeFromObjectsOkB E n sc1 s = true := by
  cases s with
  | fromObjects os p => simp only [typeFromObjectsOkB] at h ⊢; exact objSetRefsOkB_less hsc h
  | _ => rfl

theorem tableRefsOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : tableRefsOkB E n sc2 s = true) :
    tableRefsOkB E n sc1 s = true := by
  unfold tableRefsOkB at h ⊢
  split
  · rename_i t os refs; simp only at h; exact objSetRefsOkB_less hsc h
  · rfl

theorem tableTargetB_less : ∀ {n : Nat} {sc1 sc2 : Scope} {t : Ty}, ScLess sc1 sc2 →
    tableTargetB E n sc2 t = true → tableTargetB E n sc1 t = true
  | 0, _, _, _, _, _ => by simp [tableTargetB]
  | n + 1, sc1, sc2, t, hsc, h => by
    cases t with
    | ref name =>
      simp only [tableTargetB] at h ⊢
      cases hr : resolveTy E n sc1 none name [] with
      | none => rfl
      | some p =>
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2] at h; exact tableTargetB_less hs h
    | extRef mn name =>
      simp only [tableTargetB] at h ⊢
      cases hr : resolveTy E n sc1 (some mn) name [] with
      | none => rfl
      | some p =>
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2] at h; exact tableTargetB_less hs h
    | paramRef mn name args =>
      simp only [tableTargetB] at h ⊢
      cases hr : resolveTy E n sc1 mn name args with
      | none => rfl
      | some p =>
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2] at h; exact tableTargetB_less hs h
    | tagged tg k u => simp only [tableTargetB] at h ⊢; exact tableTargetB_less hsc h
    | constrained u c => simp only [tableTargetB] at h ⊢; exact tableTargetB_less hsc h
    | _ => simpa [tableTargetB] using h

theorem tableOnFieldB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : tableOnFieldB E n sc2 s = true) :
    tableOnFieldB E n sc1 s = true := by
  unfold tableOnFieldB at h ⊢
  split
  · rename_i t os refs; simp only at h; exact tableTargetB_less hsc h
  · rfl

theorem classKey_less : ∀ {n : Nat} {sc1 sc2 : Scope} {c : ClassRef} {k : String}, ScLess sc1 sc2 →
    classKey E n sc1 c = some k → classKey E n sc2 c = some k
  | 0, _, _, _, _, _, h => by simp [classKey] at h
  | n + 1, sc1, sc2, c, k, hsc, h => by
    cases c with
    | ref mn nm args =>
      cases args with
      | cons a as => simp [classKey] at h
      | nil =>
        simp only [classKey] at h ⊢
        cases hr : resolveClass E n sc1 mn nm [] with
        | none => rw [hr] at h; cases h
        | some p =>
          obtain ⟨s1, c'⟩ := p
          obtain ⟨s2, hr2, hs⟩ := resolveClass_less hsc hr
          rw [hr] at h; rw [hr2]
          cases c' with
          | ref mn' nm' args' => exact classKey_less hs h
          | defn fs syn => simp only at h ⊢; rw [← hsc.mod, ← hs.mod]; exact h
          | _ => exact classKey_less hsc h
    | _ => simpa [classKey] using h

theorem tableClassB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : tableClassB E n sc2 s = true) :
    tableClassB E n sc1 s = true := by
  unfold tableClassB at h ⊢
  split
  · rename_i cls path os refs
    simp only at h ⊢
    cases ho : objSetClass E n sc1 os.unwrap with
    | none => rfl
    | some p =>
      obtain ⟨osc, c'⟩ := p
      obtain ⟨osc2, ho2, hos⟩ := objSetClass_less hsc ho
      rw [ho2] at h; simp only at h ⊢
      cases hk1 : classKey E n sc1 cls with
      | none => rfl
      | some a =>
        cases hk2 : classKey E n osc c' with
        | none => rfl
        | some b =>
          rw [classKey_less hsc hk1, classKey_less hos hk2] at h
          exact h
  · rfl

theorem fieldAt_prefix : ∀ {n : Nat} {cf : Scope × List FieldSpec} {path : List String} {x},
    fieldAt E n cf path = some x → ∀ k, 1 ≤ k → k ≤ path.length → (fieldAt E n cf (path.take k)).isSome
  | 0, _, _, _, h, _, _, _ => by simp [fieldAt] at h
  | _ + 1, _, [], _, h, _, _, _ => by simp [fieldAt] at h
  | n + 1, (sc, fs), [f], x, h, k, hk1, hk2 => by
    obtain rfl : k = 1 := by simp at hk2; omega
    simp [h]
  | n + 1, (sc, fs), f :: g :: rest, x, h, k, hk1, hk2 => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      simp only [fieldAt] at h
      simp only [List.take_succ_cons, List.take_zero, fieldAt, Option.isSome_map]
      split at h
      · rename_i nm c o hf; rw [hf]; rfl
      · rename_i nm c o hf; rw [hf]; rfl
      · simp at h
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.take_succ_cons]
      simp only [fieldAt] at h ⊢
      split at h
      · rename_i nm c o hf
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨cf, hc, hr⟩ := h
        rw [hc]; simp only [Option.bind_some]
        have := fieldAt_prefix hr (k + 1) (by omega) (by simp at hk2 ⊢; omega)
        simpa using this
      · rename_i nm c o hf
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨cf, hc, hr⟩ := h
        rw [hc]; simp only [Option.bind_some]
        have := fieldAt_prefix hr (k + 1) (by omega) (by simp at hk2 ⊢; omega)
        simpa using this
      · simp at h

theorem typeFromObjectsTableB_less (hsc : ScLess sc1 sc2) {s : Ty}
    (h : typeFromObjectsTableB E n sc2 s = true) : typeFromObjectsTableB E n sc1 s = true := by
  cases s with
  | fromObjects src path =>
    simp only [typeFromObjectsTableB] at h ⊢
    cases ho : objSetClass E n sc1 src with
    | none => rfl
    | some p =>
      obtain ⟨csc, cls⟩ := p
      obtain ⟨csc2, ho2, hcs⟩ := objSetClass_less hsc ho
      rw [ho2] at h; simp only at h ⊢
      cases hc : classFields E n csc cls with
      | none => rfl
      | some cf =>
        obtain ⟨fsc, fs⟩ := cf
        obtain ⟨fsc2, hc2, hfs⟩ := classFields_less hcs hc
        rw [hc2] at h; simp only at h ⊢
        cases hf : fieldAt E n (fsc, fs) path with
        | none => rfl
        | some q =>
          obtain ⟨r1, f⟩ := q
          obtain ⟨r2, hf2, -⟩ := fieldAt_less hfs hf
          rw [hf2] at h
          have hvia : ∀ i ∈ List.range (path.length - 1), ∃ y1 y2 g,
              fieldAt E n (fsc, fs) (path.take (i + 1)) = some (y1, g) ∧
              fieldAt E n (fsc2, fs) (path.take (i + 1)) = some (y2, g) := by
            intro i hi
            simp only [List.mem_range] at hi
            obtain ⟨⟨y1, g⟩, hp⟩ := Option.isSome_iff_exists.mp (fieldAt_prefix hf (i + 1) (by omega) (by omega))
            obtain ⟨y2, hp2, -⟩ := fieldAt_less hfs hp
            exact ⟨y1, y2, g, hp, hp2⟩
          have hany : ∀ (F1 F2 : Nat → Bool),
              (∀ i ∈ List.range (path.length - 1), F1 i = F2 i) →
              (List.range (path.length - 1)).any F1 = (List.range (path.length - 1)).any F2 := by
            intro F1 F2 hF
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true]
            constructor
            · rintro ⟨i, hi, hm⟩; exact ⟨i, hi, by rw [← hF i hi]; exact hm⟩
            · rintro ⟨i, hi, hm⟩; exact ⟨i, hi, by rw [hF i hi]; exact hm⟩
          cases f <;> simp only at h ⊢
          all_goals first
            | exact h
            | (convert h using 2
               refine hany _ _ fun i hi => ?_
               obtain ⟨y1, y2, g, hp1, hp2⟩ := hvia i hi
               rw [hp1, hp2]; cases g <;> rfl)
            | (convert h using 3
               refine hany _ _ fun i hi => ?_
               obtain ⟨y1, y2, g, hp1, hp2⟩ := hvia i hi
               rw [hp1, hp2]; cases g <;> rfl)
  | _ => rfl



theorem entLess_presence : ∀ {l1 l2 : List Entry}, List.Forall₂ EntLess l1 l2 →
    l1.map (fun en => (en.name, en.presence)) = l2.map (fun en => (en.name, en.presence))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hr => by simp [h.2.1, h.2.2.2.1, entLess_presence hr]

theorem innerNamesOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : innerNamesOkB E n sc2 s = true) :
    innerNamesOkB E n sc1 s = true := by
  cases s with
  | constrained t c =>
    cases c with
    | mk r x a =>
      simp only [innerNamesOkB] at h ⊢
      split
      · rfl
      · rename_i hne
        simp only [hne, ↓reduceIte] at h
        cases hb : builtin E n sc1 t with
        | none => rfl
        | some p =>
          obtain ⟨s1, b⟩ := p
          obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
          rw [hb2] at h
          cases b with
          | sequence ro e r2 =>
            simp only at h ⊢
            cases hk : entriesKnown E n s1 ro e r2 with
            | false => rfl
            | true =>
              rw [entriesKnown_less hs hk] at h
              simp only [Bool.not_true, Bool.false_or] at h ⊢
              rw [entLess_names ((entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk)]
              exact h
          | set ro e r2 =>
            simp only at h ⊢
            cases hk : entriesKnown E n s1 ro e r2 with
            | false => rfl
            | true =>
              rw [entriesKnown_less hs hk] at h
              simp only [Bool.not_true, Bool.false_or] at h ⊢
              rw [entLess_names ((entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk)]
              exact h
          | _ => exact h
    | _ => rfl
  | _ => rfl

theorem componentsOfOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : componentsOfOkB E n sc2 s = true) :
    componentsOfOkB E n sc1 s = true := by
  have key : ∀ (good : Ty → Bool) (c : Comp), (match c with
      | .componentsOf t => match builtin E n sc2 t with
        | some (_, b) => good b
        | none => true
      | _ => true) = true → (match c with
      | .componentsOf t => match builtin E n sc1 t with
        | some (_, b) => good b
        | none => true
      | _ => true) = true := by
    intro good c hc
    cases c with
    | componentsOf t =>
      simp only at hc ⊢
      cases hb : builtin E n sc1 t with
      | none => rfl
      | some p =>
        obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
        rw [hb2] at hc; exact hc
    | mk => rfl
  cases s with
  | sequence r e r2 =>
    simp only [componentsOfOkB, List.all_eq_true] at h ⊢
    intro c hc
    have := key (fun b => match b with | .sequence .. => true | _ => false) c
    revert this
    cases c with
    | componentsOf t =>
      intro this
      have h' := h _ hc
      simp only at h' this ⊢
      cases hb : builtin E n sc1 t with
      | none => rfl
      | some p =>
        obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
        rw [hb2] at h'
        obtain ⟨s1, b⟩ := p
        cases b <;> simp_all
    | mk => intro _; rfl
  | set r e r2 =>
    simp only [componentsOfOkB, List.all_eq_true] at h ⊢
    intro c hc
    cases c with
    | componentsOf t =>
      have h' := h _ hc
      simp only at h' ⊢
      cases hb : builtin E n sc1 t with
      | none => rfl
      | some p =>
        obtain ⟨s2, hb2, -⟩ := builtin_less hsc hb
        rw [hb2] at h'
        obtain ⟨s1, b⟩ := p
        cases b <;> simp_all
    | mk => rfl
  | _ => rfl

theorem presenceOkB_less (hsc : ScLess sc1 sc2) {s : Ty} (h : presenceOkB E n sc2 s = true) :
    presenceOkB E n sc1 s = true := by
  cases s with
  | constrained t c =>
    cases c with
    | mk r x a =>
      simp only [presenceOkB] at h ⊢
      cases hb : builtin E n sc1 t with
      | none => rfl
      | some p =>
        obtain ⟨s1, b⟩ := p
        obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
        rw [hb2] at h
        have common : ∀ (ro r2 : List Comp) (e : Option (List ExtAdd)),
            (!entriesKnown E n s2 ro e r2 || ((esWithPres r ++ (a.map esWithPres).getD []).all fun l =>
              l.all fun (nm, p) => (match p with | .present | .absent => false | _ => true) ||
                (entries E n s2 ro e r2).any (fun en => en.name == nm && !en.presence.isMandatory) ||
                !(entries E n s2 ro e r2).any (·.name == nm))) = true →
            (!entriesKnown E n s1 ro e r2 || ((esWithPres r ++ (a.map esWithPres).getD []).all fun l =>
              l.all fun (nm, p) => (match p with | .present | .absent => false | _ => true) ||
                (entries E n s1 ro e r2).any (fun en => en.name == nm && !en.presence.isMandatory) ||
                !(entries E n s1 ro e r2).any (·.name == nm))) = true := by
          intro ro r2 e hh
          cases hk : entriesKnown E n s1 ro e r2 with
          | false => rfl
          | true =>
            rw [entriesKnown_less hs hk] at hh
            have hes := (entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk
            have hnp := entLess_presence hes
            have h1 : ∀ nm, ((entries E n s1 ro e r2).any fun en => en.name == nm && !en.presence.isMandatory) =
                ((entries E n s2 ro e r2).any fun en => en.name == nm && !en.presence.isMandatory) := by
              intro nm
              have := congrArg (fun l => l.any fun (x : String × Presence) => x.1 == nm && !x.2.isMandatory) hnp
              simp only [List.any_map] at this; exact this
            have h2 : ∀ nm, ((entries E n s1 ro e r2).any fun en => en.name == nm) =
                ((entries E n s2 ro e r2).any fun en => en.name == nm) := by
              intro nm
              have := congrArg (fun l => l.any fun (x : String × Presence) => x.1 == nm) hnp
              simp only [List.any_map] at this; exact this
            simp only [h1, h2]; exact hh
        cases b with
        | sequence ro e r2 => exact common ro r2 e h
        | set ro e r2 => exact common ro r2 e h
        | _ => rfl
    | _ => rfl
  | _ => rfl

theorem tableOn_less : ∀ {k : Nat} {sc1 sc2 : Scope} {t : Ty} {r : Option ObjSet}, ScLess sc1 sc2 →
    tableOn E n k sc1 t = some r → tableOn E n k sc2 t = some r
  | 0, _, _, _, _, _, h => by simp [tableOn] at h
  | k + 1, sc1, sc2, t, r, hsc, h => by
    cases t with
    | ref nm =>
      simp only [tableOn] at h ⊢
      cases hr : resolveTy E n sc1 none nm [] with
      | none => rw [hr] at h; cases h
      | some p =>
        rw [hr] at h
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2]; exact tableOn_less hs h
    | tagged tg kk u => simp only [tableOn] at h ⊢; exact tableOn_less hsc h
    | constrained u c =>
      simp only [tableOn] at h ⊢
      cases c with
      | table os refs => exact h
      | _ => exact tableOn_less hsc h
    | _ => simpa [tableOn] using h



theorem forall₂_refl' {α} {R : α → α → Prop} (hr : ∀ x, R x x) : ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | x :: xs => .cons (hr x) (forall₂_refl' hr xs)

/-- Components alike: same names and types, scopes the first knowing less. -/
def CompLess (a b : String × Scope × Ty) : Prop := a.1 = b.1 ∧ ScLess a.2.1 b.2.1 ∧ a.2.2 = b.2.2

theorem compsOf_less {t : Ty} {cs1 : List (String × Scope × Ty)} (hsc : ScLess sc1 sc2)
    (h : compsOf E n sc1 t = some cs1) (hk : structKnown E n sc1 t = true) :
    ∃ cs2, compsOf E n sc2 t = some cs2 ∧ List.Forall₂ CompLess cs1 cs2 ∧ structKnown E n sc2 t = true := by
  unfold compsOf at h ⊢
  unfold structKnown at hk ⊢
  cases hb : builtin E n sc1 t with
  | none => rw [hb] at h; cases h
  | some p =>
    obtain ⟨s1, b⟩ := p
    obtain ⟨s2, hb2, hs⟩ := builtin_less hsc hb
    rw [hb] at h hk; rw [hb2]
    have entr : ∀ (ro r2 : List Comp) (e : Option (List ExtAdd)), entriesKnown E n s1 ro e r2 = true →
        List.Forall₂ CompLess ((entries E n s1 ro e r2).map fun en => (en.name, en.scope, en.ty))
          ((entries E n s2 ro e r2).map fun en => (en.name, en.scope, en.ty)) := by
      intro ro r2 e hk'
      exact forall₂_map (fun x y hxy => ⟨hxy.2.1, hxy.1, hxy.2.2.1⟩)
        ((entries_less (E := E) (n := n) (r := ro) (e := e) (r2 := r2) hs).2 hk')
    cases b with
    | sequence ro e r2 =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, entr ro r2 e hk, entriesKnown_less hs hk⟩
    | set ro e r2 =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, entr ro r2 e hk, entriesKnown_less hs hk⟩
    | choice ro e =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, forall₂_map (R := fun a b => a = b) (fun x y hxy => by subst hxy; exact ⟨rfl, hs, rfl⟩)
        (forall₂_refl' (fun _ => rfl) _), rfl⟩
    | _ => cases h

theorem find_compLess {id : String} : ∀ {cs1 cs2 : List (String × Scope × Ty)}, List.Forall₂ CompLess cs1 cs2 →
    (cs1.find? (·.1 == id) = none ∧ cs2.find? (·.1 == id) = none) ∨
      ∃ x1 x2, cs1.find? (·.1 == id) = some x1 ∧ cs2.find? (·.1 == id) = some x2 ∧ CompLess x1 x2
  | [], [], .nil => .inl ⟨rfl, rfl⟩
  | x1 :: r1, x2 :: r2, .cons h hr => by
    by_cases hx : x1.1 = id
    · right
      have hx2 : x2.1 = id := h.1 ▸ hx
      exact ⟨x1, x2, by simp [hx], by simp [hx2], h⟩
    · have hx2 : ¬ x2.1 = id := h.1 ▸ hx
      have hb1 : (x1.1 == id) = false := by simpa using hx
      have hb2 : (x2.1 == id) = false := by simpa using hx2
      simp only [List.find?_cons, hb1, hb2]
      exact find_compLess hr

theorem atWalk_less {os : ObjSet} : ∀ {sc1 sc2 : Scope} {t : Ty} {path : List String}, ScLess sc1 sc2 →
    atRefOkB.walk E n os sc2 t path = true → atRefOkB.walk E n os sc1 t path = true
  | _, _, _, [], _, _ => by simp [atRefOkB.walk]
  | sc1, sc2, t, [id], hsc, h => by
    simp only [atRefOkB.walk] at h ⊢
    cases hc : compsOf E n sc1 t with
    | none => rfl
    | some cs1 =>
      simp only
      cases hk : structKnown E n sc1 t with
      | false => rfl
      | true =>
        obtain ⟨cs2, hc2, hrel, hk2⟩ := compsOf_less hsc hc hk
        rw [hc2] at h; simp only [hk2, Bool.not_true, Bool.false_or] at h
        simp only [Bool.not_true, Bool.false_or]
        rcases find_compLess (id := id) hrel with ⟨h1, h2⟩ | ⟨x1, x2, h1, h2, hx⟩
        · rw [h2] at h; cases h
        · rw [h1]; rw [h2] at h
          obtain ⟨_, csc1, ct⟩ := x1
          obtain ⟨_, csc2, ct2⟩ := x2
          obtain ⟨-, hs, rfl⟩ := hx
          simp only at h ⊢
          cases ht : tableOn E n n csc1 ct with
          | none => rfl
          | some r => rw [tableOn_less hs ht] at h; exact h
  | sc1, sc2, t, id :: id2 :: rest, hsc, h => by
    simp only [atRefOkB.walk] at h ⊢
    cases hc : compsOf E n sc1 t with
    | none => rfl
    | some cs1 =>
      simp only
      cases hk : structKnown E n sc1 t with
      | false => rfl
      | true =>
        obtain ⟨cs2, hc2, hrel, hk2⟩ := compsOf_less hsc hc hk
        rw [hc2] at h; simp only [hk2, Bool.not_true, Bool.false_or] at h
        simp only [Bool.not_true, Bool.false_or]
        rcases find_compLess (id := id) hrel with ⟨h1, h2⟩ | ⟨x1, x2, h1, h2, hx⟩
        · rw [h2] at h; cases h
        · rw [h1]; rw [h2] at h
          obtain ⟨_, csc1, ct⟩ := x1
          obtain ⟨_, csc2, ct2⟩ := x2
          obtain ⟨-, hs, rfl⟩ := hx
          exact atWalk_less hs h

theorem atRefOkB_less {anc : List Ty} {os : ObjSet} {a : AtRef} (hsc : ScLess sc1 sc2)
    (h : atRefOkB E n sc2 anc os a = true) : atRefOkB E n sc1 anc os a = true := by
  unfold atRefOkB at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hp; simp only [hp] at h; cases h
  · rename_i p hp; simp only [hp] at h; exact atWalk_less hsc h

theorem atPathsOkB_less (hsc : ScLess sc1 sc2) (t : Ty) : ∀ (anc : List Ty),
    atPathsOkB E n sc2 anc t = true → atPathsOkB E n sc1 anc t = true := by
  induction t using WellFounded.induction (measure (sizeOf : Ty → Nat)).wf with
  | _ t ih =>
  intro anc h
  rw [atPathsOkB.eq_def] at h ⊢
  cases t with
  | sequence r e r2 =>
    simp only [List.all_eq_true] at h ⊢
    rintro ⟨c, hc⟩ hm
    have := h ⟨c, hc⟩ hm
    cases c with
    | mk nm ct p =>
      simp only at this ⊢
      exact ih ct (by have := Comp.sizeOf_lt hc; show sizeOf ct < _; simp at this ⊢; omega) _ this
    | componentsOf u => rfl
  | set r e r2 =>
    simp only [List.all_eq_true] at h ⊢
    rintro ⟨c, hc⟩ hm
    have := h ⟨c, hc⟩ hm
    cases c with
    | mk nm ct p =>
      simp only at this ⊢
      exact ih ct (by have := Comp.sizeOf_lt hc; show sizeOf ct < _; simp at this ⊢; omega) _ this
    | componentsOf u => rfl
  | choice r e =>
    simp only [List.all_eq_true] at h ⊢
    rintro ⟨a, ha⟩ hm
    have := h ⟨a, ha⟩ hm
    cases a with
    | mk nm at' =>
      simp only at this ⊢
      exact ih at' (by have := Alt.sizeOf_lt ha; show sizeOf at' < _; simp at this ⊢; omega) _ this
  | sequenceOf et => exact ih et (by show sizeOf et < _; simp) _ h
  | setOf et => exact ih et (by show sizeOf et < _; simp) _ h
  | tagged tg k u => exact ih u (by show sizeOf u < _; simp) _ h
  | constrained u c =>
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨?_, ih u (by show sizeOf u < _; simp; omega) _ h.2⟩
    have h1 := h.1
    cases c with
    | table os refs =>
      simp only [List.all_eq_true] at h1 ⊢
      exact fun a ha => atRefOkB_less hsc (h1 a ha)
    | _ => rfl
  | _ => rfl



/-! ### Decisions: what the scope that knows less decides, the other decides alike -/

/-- `o1` decides nothing `o2` does not decide alike. -/
def OLe (o1 o2 : Option Bool) : Prop := ∀ b, o1 = some b → o2 = some b

theorem OLe.refl (o : Option Bool) : OLe o o := fun _ h => h
theorem OLe.none' (o : Option Bool) : OLe none o := fun _ h => by cases h

theorem OLe.orB {x1 x2 y1 y2 : Option Bool} (hx : OLe x1 x2) (hy : OLe y1 y2) : OLe (orB x1 y1) (orB x2 y2) := by
  unfold OLe at hx hy ⊢
  rcases x1 with _ | ⟨_ | _⟩ <;> rcases y1 with _ | ⟨_ | _⟩ <;> rcases x2 with _ | ⟨_ | _⟩ <;>
    rcases y2 with _ | ⟨_ | _⟩ <;> simp_all [Asn1.X680.orB]

theorem OLe.andB {x1 x2 y1 y2 : Option Bool} (hx : OLe x1 x2) (hy : OLe y1 y2) : OLe (andB x1 y1) (andB x2 y2) := by
  unfold OLe at hx hy ⊢
  rcases x1 with _ | ⟨_ | _⟩ <;> rcases y1 with _ | ⟨_ | _⟩ <;> rcases x2 with _ | ⟨_ | _⟩ <;>
    rcases y2 with _ | ⟨_ | _⟩ <;> simp_all [Asn1.X680.andB]

theorem OLe.not {x1 x2 : Option Bool} (hx : OLe x1 x2) : OLe (x1.map (!·)) (x2.map (!·)) := by
  intro b hb
  cases x1 with
  | none => cases hb
  | some c => rw [hx c rfl]; exact hb

def DLe (d1 d2 : Dec) : Prop := OLe d1.1 d2.1 ∧ OLe d1.2 d2.2

theorem DLe.union {a1 a2 b1 b2 : Dec} (ha : DLe a1 a2) (hb : DLe b1 b2) : DLe (a1.union b1) (a2.union b2) :=
  ⟨ha.1.orB hb.1, (ha.1.orB hb.1).orB (ha.2.orB hb.2)⟩
theorem DLe.inter {a1 a2 b1 b2 : Dec} (ha : DLe a1 a2) (hb : DLe b1 b2) : DLe (a1.inter b1) (a2.inter b2) :=
  ⟨ha.1.andB hb.1, (ha.1.andB hb.1).orB (ha.2.andB hb.2)⟩
theorem DLe.except {a1 a2 b1 b2 : Dec} (ha : DLe a1 a2) (hb : DLe b1 b2) : DLe (a1.except b1) (a2.except b2) :=
  ⟨ha.1.andB hb.1.not, (ha.1.andB hb.1.not).orB (ha.2.andB hb.2.not)⟩
theorem DLe.allExcept {b1 b2 : Dec} (hb : DLe b1 b2) : DLe b1.allExcept b2.allExcept :=
  ⟨hb.1.not, hb.1.not⟩

theorem decES_le {el1 el2 : Elem → Dec} (h : ∀ e, DLe (el1 e) (el2 e)) :
    ∀ es : ElemSet, DLe (decES el1 es) (decES el2 es)
  | .elem e => h e
  | .union a b => (decES_le h a).union (decES_le h b)
  | .inter a b => (decES_le h a).inter (decES_le h b)
  | .except a b => (decES_le h a).except (decES_le h b)
  | .allExcept b => (decES_le h b).allExcept

theorem decCons_le {es1 es2 : ElemSet → Dec} (h : ∀ es, DLe (es1 es) (es2 es)) :
    ∀ c : Constraint, DLe (decCons es1 c) (decCons es2 c)
  | .mk r x a => by
    simp only [decCons, Dec.ofSpecs, DLe]
    refine ⟨(h r).1, ?_⟩
    cases a with
    | none => exact (h r).2
    | some a' => exact (h r).2.orB (h a').2
  | .table .. | .contents .. | .userDefined => ⟨OLe.refl _, OLe.refl _⟩

theorem intOfV_less : ∀ {k : Nat} {sc1 sc2 : Scope} {v : Val} {i : Int}, ScLess sc1 sc2 →
    intOfV E n sc1 k v = some i → intOfV E n sc2 k v = some i
  | _, _, _, .int j, _, _, h => by simpa [intOfV] using h
  | k + 1, sc1, sc2, .ref mn nm args, i, hsc, h => by
    simp only [intOfV] at h ⊢
    cases hr : resolveVal E n sc1 mn nm args with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr] at h
      obtain ⟨s2, hr2, hs⟩ := resolveVal_less hsc hr
      rw [hr2]; exact intOfV_less hs h
  | 0, _, _, .ref .., _, _, h => by simp [intOfV] at h
  | _, _, _, .bool _, _, _, h | _, _, _, .enum _, _, _, h | _, _, _, .real _, _, _, h
  | _, _, _, .bits _, _, _, h | _, _, _, .octets _, _, _, h | _, _, _, .null, _, _, h
  | _, _, _, .seq _, _, _, h | _, _, _, .seqOf _, _, _, h | _, _, _, .setOf _, _, _, h
  | _, _, _, .choice .., _, _, h | _, _, _, .oid _, _, _, h | _, _, _, .iri _, _, _, h
  | _, _, _, .chars _, _, _, h | _, _, _, .regChars _, _, _, h | _, _, _, .time _, _, _, h
  | _, _, _, .open_ .., _, _, h | _, _, _, .fromObject .., _, _, h | _, _, _, .raw _, _, _, h => by
    simp [intOfV] at h

theorem charsOfV_less : ∀ {k : Nat} {sc1 sc2 : Scope} {v : Val} {cs : List Nat}, ScLess sc1 sc2 →
    charsOfV E n sc1 k v = some cs → charsOfV E n sc2 k v = some cs
  | _, _, _, .chars j, _, _, h => by simpa [charsOfV] using h
  | k + 1, sc1, sc2, .ref mn nm args, i, hsc, h => by
    simp only [charsOfV] at h ⊢
    cases hr : resolveVal E n sc1 mn nm args with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr] at h
      obtain ⟨s2, hr2, hs⟩ := resolveVal_less hsc hr
      rw [hr2]; exact charsOfV_less hs h
  | 0, _, _, .ref .., _, _, h => by simp [charsOfV] at h
  | _, _, _, .bool _, _, _, h | _, _, _, .enum _, _, _, h | _, _, _, .real _, _, _, h
  | _, _, _, .bits _, _, _, h | _, _, _, .octets _, _, _, h | _, _, _, .null, _, _, h
  | _, _, _, .seq _, _, _, h | _, _, _, .seqOf _, _, _, h | _, _, _, .setOf _, _, _, h
  | _, _, _, .choice .., _, _, h | _, _, _, .oid _, _, _, h | _, _, _, .iri _, _, _, h
  | _, _, _, .int _, _, _, h | _, _, _, .regChars _, _, _, h | _, _, _, .time _, _, _, h
  | _, _, _, .open_ .., _, _, h | _, _, _, .fromObject .., _, _, h | _, _, _, .raw _, _, _, h => by
    simp [charsOfV] at h

theorem OLe.map_of {α} {o1 o2 : Option α} (f : α → Bool) (h : ∀ x, o1 = some x → o2 = some x) :
    OLe (o1.map f) (o2.map f) := by
  intro b hb
  cases o1 with
  | none => cases hb
  | some x => rw [h x rfl]; exact hb

theorem intInElem_le (hsc : ScLess sc1 sc2) (i : Int) (e : Elem) :
    OLe (intInElem E n sc1 i e) (intInElem E n sc2 i e) := by
  cases e with
  | single v => exact OLe.map_of _ fun x hx => intOfV_less hsc hx
  | range lo lo' hi hi' =>
    simp only [intInElem]
    refine OLe.andB ?_ ?_
    · cases lo with
      | val v => exact OLe.map_of _ fun x hx => intOfV_less hsc hx
      | _ => exact OLe.refl _
    · cases hi with
      | val v => exact OLe.map_of _ fun x hx => intOfV_less hsc hx
      | _ => exact OLe.refl _
  | _ => exact OLe.refl _

theorem intInES_le (hsc : ScLess sc1 sc2) (i : Int) (es : ElemSet) :
    DLe (intInES E n sc1 i es) (intInES E n sc2 i es) :=
  decES_le (fun e => ⟨intInElem_le hsc i e, intInElem_le hsc i e⟩) es

theorem sizeInES_le (hsc : ScLess sc1 sc2) (len : Nat) (es : ElemSet) :
    DLe (sizeInES E n sc1 len es) (sizeInES E n sc2 len es) := by
  refine decES_le (fun e => ?_) es
  cases e with
  | size c => exact decCons_le (intInES_le hsc len) c
  | _ => exact ⟨OLe.refl _, OLe.refl _⟩

theorem alphaNo_less (hsc : ScLess sc1 sc2) (c : Nat) : ∀ es : ElemSet,
    alphaNo E n sc1 c es = true → alphaNo E n sc2 c es = true
  | .elem (.single v), h => by
    simp only [alphaNo] at h ⊢
    split at h
    · rename_i cs hcs; rw [charsOfV_less hsc hcs]; exact h
    · cases h
  | .elem (.range lo loOpen hi hiOpen), h => by
    have one : ∀ (b : Bound) (x : Option Nat), charBound E n sc1 b = some x → charBound E n sc2 b = some x := by
      intro b x hb
      cases b with
      | val v =>
        simp only [charBound] at hb ⊢
        cases hv : charsOfV E n sc1 8 v with
        | none => rw [hv] at hb; cases hb
        | some cs => rw [hv] at hb; rw [charsOfV_less hsc hv]; exact hb
      | _ => exact hb
    simp only [alphaNo] at h ⊢
    split at h
    · rename_i l hh hl hhh
      rw [one _ _ hl, one _ _ hhh]; exact h
    · cases h
  | .union a b, h => by
    simp only [alphaNo, Bool.and_eq_true] at h ⊢
    exact ⟨alphaNo_less hsc c a h.1, alphaNo_less hsc c b h.2⟩
  | .inter a b, h => by
    simp only [alphaNo, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact .inl (alphaNo_less hsc c a h)
    · exact .inr (alphaNo_less hsc c b h)
  | .except a b, h => by simp only [alphaNo] at h ⊢; exact alphaNo_less hsc c a h
  | .allExcept _, h => by simp [alphaNo] at h
  | .elem (.contained ..), h | .elem (.size _), h | .elem (.typeC _), h | .elem (.from_ _), h
  | .elem (.withComponent _), h | .elem (.withComponents ..), h | .elem (.pattern _), h
  | .elem (.settings _), h => by simp [alphaNo] at h

theorem charsInES_le (hsc : ScLess sc1 sc2) (cs : List Nat) (es : ElemSet) :
    DLe (charsInES E n sc1 cs es) (charsInES E n sc2 cs es) := by
  refine decES_le (fun e => ?_) es
  cases e with
  | single v =>
    have := OLe.map_of (· == cs) fun x hx => charsOfV_less (E := E) (n := n) (k := 8) (v := v) hsc hx
    exact ⟨this, this⟩
  | pattern re => exact ⟨OLe.refl _, OLe.refl _⟩
  | size c => exact decCons_le (intInES_le hsc cs.length) c
  | from_ c =>
    cases c with
    | mk r x a =>
      simp only [DLe]
      constructor
      · intro b hb
        split at hb
        · rename_i hany
          rw [if_pos]; exact hb
          simp only [List.any_eq_true] at hany ⊢
          obtain ⟨ch, hch, hno⟩ := hany
          exact ⟨ch, hch, alphaNo_less hsc ch r hno⟩
        · cases hb
      · intro b hb
        split at hb
        · rename_i hany
          rw [if_pos]; exact hb
          simp only [List.any_eq_true, Bool.and_eq_true] at hany ⊢
          obtain ⟨ch, hch, hno, hnoa⟩ := hany
          refine ⟨ch, hch, alphaNo_less hsc ch r hno, ?_⟩
          cases a with
          | none => rfl
          | some a' => simp at hnoa ⊢; exact alphaNo_less hsc ch a' hnoa
        · cases hb
    | _ => exact ⟨OLe.refl _, OLe.refl _⟩
  | _ => exact ⟨OLe.refl _, OLe.refl _⟩

/-- What the walk of `notInTy` decides in the scope that knows less, it decides in the other. -/
theorem notInTy_less {dec1 dec2 : Scope → Bool → Constraint → Option Bool}
    (hdec : ∀ s1 s2 w c, ScLess s1 s2 → OLe (dec1 s1 w c) (dec2 s2 w c)) :
    ∀ (k : Nat) {sc1 sc2 : Scope} (t : Ty) (w : Bool), ScLess sc1 sc2 →
      notInTy E n dec1 k sc1 t w = true → notInTy E n dec2 k sc2 t w = true
  | 0, _, _, _, _, _, h => by simp [notInTy] at h
  | k + 1, sc1, sc2, t, w, hsc, h => by
    cases t with
    | constrained t c =>
      simp only [notInTy, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | h
      · exact .inl (hdec _ _ _ _ hsc _ h)
      · exact .inr (notInTy_less hdec k t false hsc h)
    | tagged tg kk t => simp only [notInTy] at h ⊢; exact notInTy_less hdec k t w hsc h
    | ref nm =>
      simp only [notInTy] at h ⊢
      cases hr : resolveTy E n sc1 none nm [] with
      | none => rw [hr] at h; cases h
      | some p =>
        rw [hr] at h
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2]; exact notInTy_less hdec k _ w hs h
    | extRef mn nm =>
      simp only [notInTy] at h ⊢
      cases hr : resolveTy E n sc1 (some mn) nm [] with
      | none => rw [hr] at h; cases h
      | some p =>
        rw [hr] at h
        obtain ⟨s2, hr2, hs⟩ := resolveTy_less hsc hr
        rw [hr2]; exact notInTy_less hdec k _ w hs h
    | _ => simp [notInTy] at h

theorem intNotInTy_less (hsc : ScLess sc1 sc2) {t : Ty} {i : Int} {w : Bool}
    (h : intNotInTy E n 16 sc1 t i w = true) : intNotInTy E n 16 sc2 t i w = true :=
  notInTy_less (fun s1 s2 w c hs => by
    simp only [intInCons]; cases w
    · exact (decCons_le (intInES_le hs i) c).1
    · exact (decCons_le (intInES_le hs i) c).2) 16 t w hsc h

theorem sizeNotInTy_less (hsc : ScLess sc1 sc2) {t : Ty} {len : Nat} {w : Bool}
    (h : sizeNotInTy E n 16 sc1 t len w = true) : sizeNotInTy E n 16 sc2 t len w = true :=
  notInTy_less (fun s1 s2 w c hs => by
    simp only [sizeInCons]; cases w
    · exact (decCons_le (sizeInES_le hs len) c).1
    · exact (decCons_le (sizeInES_le hs len) c).2) 16 t w hsc h

theorem charsNotInTy_less (hsc : ScLess sc1 sc2) {t : Ty} {cs : List Nat} {w : Bool}
    (h : charsNotInTy E n 16 sc1 t cs w = true) : charsNotInTy E n 16 sc2 t cs w = true :=
  notInTy_less (fun s1 s2 w c hs => by
    simp only [charsInCons]; cases w
    · exact (decCons_le (charsInES_le hs cs) c).1
    · exact (decCons_le (charsInES_le hs cs) c).2) 16 t w hsc h

end RulesLess

end Asn1.X680
