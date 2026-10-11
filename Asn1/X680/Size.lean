import Asn1.X680.Validity

/-!
# Sizes, for recursion over the syntax

The checker's functions recurse into the parts of a node: the components of a SEQUENCE, the
alternatives of a CHOICE, the types a constraint mentions. These say that each such part is
smaller than the node, which is what their termination proofs need.
-/

namespace Asn1.X680

theorem sizeOf_mem_append3 {α} [SizeOf α] {x : α} {a b c : List α} (h : x ∈ a ++ b ++ c) :
    sizeOf x < sizeOf a + sizeOf b + sizeOf c := by
  simp only [List.mem_append] at h
  rcases h with (h | h) | h <;> have := List.sizeOf_lt_of_mem h <;> omega

theorem ExtAdd.sizeOf_comps {c : Comp} {e : List ExtAdd} (h : c ∈ e.flatMap ExtAdd.comps) :
    sizeOf c < sizeOf e := by
  induction e with
  | nil => simp at h
  | cons a e ih =>
    simp only [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases a with
      | one c' => simp [ExtAdd.comps] at h; subst h; simp <;> omega
      | group v cs => simp [ExtAdd.comps] at h; have := List.sizeOf_lt_of_mem h; simp; omega
    · have := ih h; simp; omega

theorem Comp.sizeOf_lt {c : Comp} {r r2 : List Comp} {e : Option (List ExtAdd)}
    (h : c ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2) :
    sizeOf c < 1 + sizeOf r + sizeOf e + sizeOf r2 := by
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · have := List.sizeOf_lt_of_mem h; omega
  · cases e with
    | none => simp at h
    | some e => simp only [Option.getD_some] at h; have := ExtAdd.sizeOf_comps h; simp; omega
  · have := List.sizeOf_lt_of_mem h; omega

theorem Alt.sizeOf_lt {a : Alt} {r : List Alt} {e : Option (List AltAdd)} (h : a ∈ choiceAlts r e) :
    sizeOf a < 1 + sizeOf r + sizeOf e := by
  simp only [choiceAlts, List.mem_append] at h
  rcases h with h | h
  · have := List.sizeOf_lt_of_mem h; omega
  · cases e with
    | none => simp at h
    | some e =>
      simp only [Option.getD_some, List.mem_flatMap] at h
      obtain ⟨x, hx, ha⟩ := h
      have h1 := List.sizeOf_lt_of_mem hx
      cases x with
      | one a' => simp [AltAdd.alts] at ha; subst ha; simp at h1 ⊢; omega
      | group v as => simp [AltAdd.alts] at ha; have h2 := List.sizeOf_lt_of_mem ha; simp at h1 ⊢; omega

mutual
  theorem consTypes_sizeOf : ∀ {c : Constraint} {u : Ty}, u ∈ consTypes c → sizeOf u < sizeOf c
    | .mk r x (some a), u, h => by
      simp only [consTypes, List.mem_append] at h
      rcases h with h | h
      · have := esTypes_sizeOf h; simp; omega
      · have := esTypes_sizeOf h; simp; omega
    | .mk r x none, u, h => by simp only [consTypes] at h; have := esTypes_sizeOf h; simp; omega
    | .contents (some t) _, u, h => by simp [consTypes] at h; subst h; simp <;> omega
    | .contents none _, u, h => by simp [consTypes] at h
    | .table .., u, h => by simp [consTypes] at h
    | .userDefined, u, h => by simp [consTypes] at h
  theorem esTypes_sizeOf : ∀ {s : ElemSet} {u : Ty}, u ∈ esTypes s → sizeOf u < sizeOf s
    | .elem e, u, h => by simp only [esTypes] at h; have := elTypes_sizeOf h; simp; omega
    | .union a b, u, h | .inter a b, u, h | .except a b, u, h => by
      simp only [esTypes, List.mem_append] at h
      rcases h with h | h
      · have := esTypes_sizeOf h; simp; omega
      · have := esTypes_sizeOf h; simp; omega
    | .allExcept b, u, h => by simp only [esTypes] at h; have := esTypes_sizeOf h; simp; omega
  theorem elTypes_sizeOf : ∀ {e : Elem} {u : Ty}, u ∈ elTypes e → sizeOf u < sizeOf e
    | .contained t _, u, h | .typeC t, u, h => by simp [elTypes] at h; subst h; simp <;> omega
    | .size c, u, h | .from_ c, u, h | .withComponent c, u, h => by
      simp only [elTypes] at h; have := consTypes_sizeOf h; simp; omega
    | .withComponents _ cs, u, h => by simp only [elTypes] at h; have := ncTypes_sizeOf h; simp; omega
    | .single _, u, h | .range .., u, h | .pattern _, u, h | .settings _, u, h => by simp [elTypes] at h
  theorem ncTypes_sizeOf : ∀ {cs : List (String × Option Constraint × PresenceC)} {u : Ty},
      u ∈ ncTypes cs → sizeOf u < sizeOf cs
    | [], u, h => by simp [ncTypes] at h
    | (_, some c, _) :: r, u, h => by
      simp only [ncTypes, List.mem_append] at h
      rcases h with h | h
      · have := consTypes_sizeOf h; simp; omega
      · have := ncTypes_sizeOf h; simp; omega
    | (_, none, _) :: r, u, h => by simp only [ncTypes] at h; have := ncTypes_sizeOf h; simp; omega
end

end Asn1.X680

namespace Asn1.X680

/-- Termination of the recursions over the syntax: the argument of the recursive call is a part of
the node, found through a membership `h`. -/
macro "decr_syntax" : tactic => `(tactic| (
  simp_wf <;> first
    | omega
    | (have := Comp.sizeOf_lt ‹_ ∈ _›; simp_all; omega)
    | (have := Alt.sizeOf_lt ‹_ ∈ _›; simp_all; omega)
    | (have := consTypes_sizeOf ‹_ ∈ _›; simp_all; omega)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (simp_all; omega)))

end Asn1.X680
