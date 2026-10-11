import Asn1.X680.Semantics

/-!
# More fuel resolves the same

A reference that resolves at some fuel resolves to the same thing with more. The checker and the
spec sometimes resolve one reference at different fuel (the spec's `classFields` at `n - 1`, the
checker's `resolveClass` at `n`); these lemmas connect them.
-/

namespace Asn1.X680

theorem Env.resolveWith_succ {α : Type} {E : Env} {get : Module → Option α} {name : String} :
    ∀ {n : Nat} {m : Module} {r}, E.resolveWith get name n m = some r →
      E.resolveWith get name (n + 1) m = some r
  | 0, _, _, h => by simp [Env.resolveWith] at h
  | n + 1, m, r, h => by
    unfold Env.resolveWith at h ⊢
    rcases hi : ((m.imports.filter (·.1 == name)).map (·.2)).eraseDups with _ | ⟨mn, _ | ⟨mn2, rest⟩⟩ <;>
      cases hg : get m <;> simp only [hi, hg] at h ⊢ <;> try exact h
    cases hf : E.findFrom m mn <;> simp only [hf] at h ⊢
    · simp at h
    · exact Env.resolveWith_succ h

theorem Env.resolveWith_mono {α : Type} {E : Env} {get : Module → Option α} {name : String}
    {n n' : Nat} {m : Module} {r} (h : E.resolveWith get name n m = some r) (hn : n ≤ n') :
    E.resolveWith get name n' m = some r := by
  induction hn with
  | refl => exact h
  | step _ ih => exact Env.resolveWith_succ ih

theorem Env.resolveExtWith_mono {α : Type} {E : Env} {get : Module → Option α} {name : String}
    {n n' : Nat} {m : Module} {mn : String} {r} (h : E.resolveExtWith get name n m mn = some r)
    (hn : n ≤ n') : E.resolveExtWith get name n' m mn = some r := by
  unfold Env.resolveExtWith at h ⊢
  cases hf : E.findFrom m mn with
  | none => simp [hf] at h
  | some m' =>
    simp only [hf] at h ⊢
    cases hg : get m' with
    | some a => simpa [hg] using h
    | none =>
      simp only [hg] at h ⊢
      rcases hi : m'.imports.filter (·.1 == name) with _ | ⟨⟨s1, mn'⟩, _ | ⟨x, rest⟩⟩ <;> simp only [hi] at h ⊢ <;> try exact h
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨m'', h1, h2⟩ := h
      exact ⟨m'', h1, Env.resolveWith_mono h2 hn⟩

theorem resolveIn_mono {α : Type} {E : Env} {n n' : Nat} {sc : Scope} {mn : Option String}
    {name : String} {args : List Arg} {fromArg : Arg → Option ParamGov → Scope → Option (Scope × α)}
    {fromModule : Module → Option α} {fromParam : ParamAssign → Option (List Param × α)} {r}
    (h : resolveIn E n sc mn name args fromArg fromModule fromParam = some r) (hn : n ≤ n') :
    resolveIn E n' sc mn name args fromArg fromModule fromParam = some r := by
  unfold resolveIn at h ⊢
  cases mn <;> cases args <;> cases hb : sc.bound name <;> simp only [hb, Option.map_eq_some_iff] at h ⊢ <;>
    first
    | exact h
    | (obtain ⟨x, hx, rfl⟩ := h; exact ⟨x, Env.resolveWith_mono hx hn, rfl⟩)
    | (obtain ⟨x, hx, rfl⟩ := h; exact ⟨x, Env.resolveExtWith_mono hx hn, rfl⟩)
    | skip

theorem resolveTy_mono {E n n' sc mn name args r} (h : resolveTy E n sc mn name args = some r)
    (hn : n ≤ n') : resolveTy E n' sc mn name args = some r := resolveIn_mono h hn
theorem resolveClass_mono {E n n' sc mn name args r} (h : resolveClass E n sc mn name args = some r)
    (hn : n ≤ n') : resolveClass E n' sc mn name args = some r := resolveIn_mono h hn
theorem resolveObj_mono {E n n' sc mn name args r} (h : resolveObj E n sc mn name args = some r)
    (hn : n ≤ n') : resolveObj E n' sc mn name args = some r := resolveIn_mono h hn
theorem resolveObjSet_mono {E n n' sc mn name args r} (h : resolveObjSet E n sc mn name args = some r)
    (hn : n ≤ n') : resolveObjSet E n' sc mn name args = some r := resolveIn_mono h hn
theorem resolveVal_mono {E n n' sc mn name args r} (h : resolveVal E n sc mn name args = some r)
    (hn : n ≤ n') : resolveVal E n' sc mn name args = some r := resolveIn_mono h hn

end Asn1.X680
