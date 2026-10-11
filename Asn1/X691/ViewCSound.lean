import Asn1.X691.ViewC

/-!
# The computed PER view is the PER view

`ViewC.lean` computes the PER view of a type (`pIntC`, `pSizeC`, `pStrC`) as finite unions of
intervals. This file proves that, whenever it computes one, it is the spec's view (`pInt`, `pSize`,
`pStr` of `Visible.lean`): each set has the same members, and the same extensibility
(`pIntC_sound`, `pSizeC_sound`, `pStrC_sound`); and that the bounds and alphabets computed from it
are the spec's "lb", "ub" and effective permitted alphabet (`least?_eq`, `natLeast?_eq`, …,
`effAlphabet_eq`).

Both views are instances of the one function `view`, so the proof is `view_rel`: related
arguments give related views, by induction on fuel; and `evalC_rel`: related algebras and atoms
give related constraints. What is left is one lemma per atom.
-/

open Asn1 Asn1.X680

namespace Asn1.X691
namespace Ivs

theorem memI_iff (p : Option Int × Option Int) (i : Int) :
    memI p i = true ↔ (∀ a, p.1 = some a → a ≤ i) ∧ (∀ b, p.2 = some b → i ≤ b) := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp [memI]

theorem mem_iff (s : Ivs) (i : Int) : s.mem i = true ↔ ∃ p ∈ s, memI p i = true := by
  simp [mem]

@[simp] theorem mem_append (s t : Ivs) (i : Int) : (s ++ t).mem i = (s.mem i || t.mem i) := by
  simp [mem, List.any_append]

@[simp] theorem mem_nil (i : Int) : Ivs.mem [] i = false := rfl

theorem memI_inter (p q : Option Int × Option Int) (i : Int) :
    memI (maxLo p.1 q.1, minHi p.2 q.2) i = (memI p i && memI q i) := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> cases c <;> cases d <;> simp [memI, maxLo, minHi] <;> omega

@[simp] theorem mem_inter (s t : Ivs) (i : Int) : (s.inter t).mem i = (s.mem i && t.mem i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [inter, mem, List.any_flatMap, List.any_map, Bool.and_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    rw [Function.comp_apply, memI_inter, Bool.and_eq_true] at h
    exact ⟨⟨p, hp, h.1⟩, ⟨q, hq, h.2⟩⟩
  · rintro ⟨⟨p, hp, h1⟩, ⟨q, hq, h2⟩⟩
    exact ⟨p, hp, q, hq, by rw [Function.comp_apply, memI_inter, h1, h2]; rfl⟩

@[simp] theorem mem_point (i j : Int) : (point i).mem j = decide (j = i) := by
  apply Bool.eq_iff_iff.mpr; simp [point, mem, memI]; omega

@[simp] theorem mem_univ (i : Int) : univ.mem i = true := by simp [univ, mem, memI]

theorem nonempty_of_memI {p : Option Int × Option Int} {i : Int} (h : memI p i = true) :
    nonempty p = true := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp_all [memI, nonempty]; omega

theorem mem_filter_ne (s : Ivs) (i : Int) : Ivs.mem (s.filter nonempty) i = s.mem i := by
  apply Bool.eq_iff_iff.mpr
  simp only [mem, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, _⟩, h⟩; exact ⟨p, hp, h⟩
  · rintro ⟨p, hp, h⟩; exact ⟨p, ⟨hp, nonempty_of_memI h⟩, h⟩

/-- An interval that is nonempty has its lower end in it. -/
theorem memI_lo {a : Int} {b : Option Int} (h : nonempty (some a, b) = true) : memI (some a, b) a = true := by
  cases b <;> simp_all [memI, nonempty]

theorem memI_hi {a : Option Int} {b : Int} (h : nonempty (a, some b) = true) : memI (a, some b) b = true := by
  cases a <;> simp_all [memI, nonempty]

theorem least?_spec (s : Ivs) (l : Int) : s.least? = some l ↔ IsLeast {x | s.mem x = true} l := by
  have hm : ∀ x, s.mem x = Ivs.mem (s.filter nonempty) x := fun x => (mem_filter_ne s x).symm
  simp only [hm]
  generalize hs : s.filter nonempty = s'
  have hne : ∀ p ∈ s', nonempty p = true := by
    intro p hp; rw [← hs] at hp; exact (List.mem_filter.mp hp).2
  unfold least?; rw [hs]
  by_cases hn : s'.any (·.1.isNone) = true
  · simp only [hn, ite_true, reduceCtorEq, false_iff]
    rintro ⟨h1, h2⟩
    obtain ⟨p, hp, hpn⟩ := List.any_eq_true.mp hn
    obtain ⟨a, b⟩ := p
    simp only [Option.isNone_iff_eq_none] at hpn; subst hpn
    have : (min (l - 1) (b.getD (l - 1))) ∈ {x | Ivs.mem s' x = true} := by
      simp only [Set.mem_ofPred_eq, mem_iff]
      refine ⟨(none, b), hp, ?_⟩
      have := hne _ hp
      cases b <;> simp_all [memI, nonempty]
    have := h2 this; omega
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Bool.false_eq_true, ite_false]
    have hlo : ∀ p ∈ s', ∃ a, p.1 = some a := by
      intro p hp
      have := List.any_eq_false.mp hn p hp
      simp only [Option.isNone_iff_eq_none] at this
      exact Option.ne_none_iff_exists'.mp this
    constructor
    · intro hmin
      have hmem := List.min?_mem hmin
      obtain ⟨p, hp, hpa⟩ := List.mem_filterMap.mp hmem
      obtain ⟨a, b⟩ := p; simp only at hpa; subst hpa
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, mem_iff]; exact ⟨_, hp, memI_lo (hne _ hp)⟩
      · intro x hx
        simp only [Set.mem_ofPred_eq, mem_iff] at hx
        obtain ⟨q, hq, hqx⟩ := hx
        obtain ⟨c, hc⟩ := hlo q hq
        have hle := (List.min?_eq_some_iff .. |>.mp hmin).2 c (List.mem_filterMap.mpr ⟨q, hq, hc⟩)
        rw [memI_iff] at hqx
        exact le_trans hle (hqx.1 c hc)
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq, mem_iff] at h1
      obtain ⟨q, hq, hql⟩ := h1
      apply (List.min?_eq_some_iff ..).mpr
      obtain ⟨c, hc⟩ := hlo q hq
      have hcl : c ≤ l := (memI_iff _ _ |>.mp hql).1 c hc
      have hcm : c ∈ {x | Ivs.mem s' x = true} := by
        simp only [Set.mem_ofPred_eq, mem_iff]
        obtain ⟨c', d⟩ := q; simp only at hc; subst hc
        exact ⟨_, hq, memI_lo (hne _ hq)⟩
      have := h2 hcm
      have hcl' : c = l := le_antisymm hcl this
      subst hcl'
      refine ⟨List.mem_filterMap.mpr ⟨q, hq, hc⟩, ?_⟩
      intro b hb
      obtain ⟨p, hp, hpb⟩ := List.mem_filterMap.mp hb
      apply h2
      simp only [Set.mem_ofPred_eq, mem_iff]
      obtain ⟨b', d⟩ := p; simp only at hpb; subst hpb
      exact ⟨_, hp, memI_lo (hne _ hp)⟩

theorem greatest?_spec (s : Ivs) (l : Int) : s.greatest? = some l ↔ IsGreatest {x | s.mem x = true} l := by
  have hm : ∀ x, s.mem x = Ivs.mem (s.filter nonempty) x := fun x => (mem_filter_ne s x).symm
  simp only [hm]
  generalize hs : s.filter nonempty = s'
  have hne : ∀ p ∈ s', nonempty p = true := by
    intro p hp; rw [← hs] at hp; exact (List.mem_filter.mp hp).2
  unfold greatest?; rw [hs]
  by_cases hn : s'.any (·.2.isNone) = true
  · simp only [hn, ite_true, reduceCtorEq, false_iff]
    rintro ⟨h1, h2⟩
    obtain ⟨p, hp, hpn⟩ := List.any_eq_true.mp hn
    obtain ⟨a, b⟩ := p
    simp only [Option.isNone_iff_eq_none] at hpn; subst hpn
    have : (max (l + 1) (a.getD (l + 1))) ∈ {x | Ivs.mem s' x = true} := by
      show Ivs.mem s' _ = true
      rw [mem_iff]
      refine ⟨(a, none), hp, ?_⟩
      have := hne _ hp
      cases a <;> simp_all [memI, nonempty]
    have := h2 this; omega
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Bool.false_eq_true, ite_false]
    have hhi : ∀ p ∈ s', ∃ b, p.2 = some b := by
      intro p hp
      have := List.any_eq_false.mp hn p hp
      simp only [Option.isNone_iff_eq_none] at this
      exact Option.ne_none_iff_exists'.mp this
    constructor
    · intro hmax
      have hmem := List.max?_mem hmax
      obtain ⟨p, hp, hpa⟩ := List.mem_filterMap.mp hmem
      obtain ⟨a, b⟩ := p; simp only at hpa; subst hpa
      refine ⟨?_, ?_⟩
      · show Ivs.mem s' _ = true
        rw [mem_iff]; exact ⟨_, hp, memI_hi (hne _ hp)⟩
      · intro x hx
        have hx : Ivs.mem s' x = true := hx
        rw [mem_iff] at hx
        obtain ⟨q, hq, hqx⟩ := hx
        obtain ⟨c, hc⟩ := hhi q hq
        have hle := (List.max?_eq_some_iff.mp hmax).2 c (List.mem_filterMap.mpr ⟨q, hq, hc⟩)
        rw [memI_iff] at hqx
        exact le_trans (hqx.2 c hc) hle
    · rintro ⟨h1, h2⟩
      have h1 : Ivs.mem s' l = true := h1
      rw [mem_iff] at h1
      obtain ⟨q, hq, hql⟩ := h1
      apply List.max?_eq_some_iff.mpr
      obtain ⟨c, hc⟩ := hhi q hq
      have hcl : l ≤ c := (memI_iff _ _ |>.mp hql).2 c hc
      have hcm : c ∈ {x | Ivs.mem s' x = true} := by
        show Ivs.mem s' c = true
        rw [mem_iff]
        obtain ⟨d, c'⟩ := q; simp only at hc; subst hc
        exact ⟨_, hq, memI_hi (hne _ hq)⟩
      have := h2 hcm
      have hcl' : c = l := le_antisymm this hcl
      subst hcl'
      refine ⟨List.mem_filterMap.mpr ⟨q, hq, hc⟩, ?_⟩
      intro b hb
      obtain ⟨p, hp, hpb⟩ := List.mem_filterMap.mp hb
      apply h2
      show Ivs.mem s' b = true
      rw [mem_iff]
      obtain ⟨d, b'⟩ := p; simp only at hpb; subst hpb
      exact ⟨_, hp, memI_hi (hne _ hp)⟩

@[simp] theorem mem_nats (s : Ivs) (i : Int) : s.nats.mem i = (s.mem i && decide (0 ≤ i)) := by
  rw [nats, mem_inter]; congr 1; simp [mem, memI]

end Ivs

theorem least?_eq {S : Int → Prop} {s : Ivs} (h : ∀ i, S i ↔ s.mem i = true) : least? S = s.least? := by
  have hS : {x | S x} = {x | s.mem x = true} := Set.ext fun x => h x
  unfold least?
  rw [hS]
  cases hl : s.least? with
  | none =>
    rw [dif_neg]
    rintro ⟨l, hl'⟩
    rw [(Ivs.least?_spec s l).mpr hl'] at hl; cases hl
  | some l =>
    have hl' := (Ivs.least?_spec s l).mp hl
    rw [dif_pos ⟨l, hl'⟩]
    congr 1
    exact (Classical.choose_spec (⟨l, hl'⟩ : ∃ l, IsLeast {x | s.mem x = true} l)).unique hl'

theorem greatest?_eq {S : Int → Prop} {s : Ivs} (h : ∀ i, S i ↔ s.mem i = true) :
    greatest? S = s.greatest? := by
  have hS : {x | S x} = {x | s.mem x = true} := Set.ext fun x => h x
  unfold greatest?
  rw [hS]
  cases hl : s.greatest? with
  | none =>
    rw [dif_neg]
    rintro ⟨l, hl'⟩
    rw [(Ivs.greatest?_spec s l).mpr hl'] at hl; cases hl
  | some l =>
    have hl' := (Ivs.greatest?_spec s l).mp hl
    rw [dif_pos ⟨l, hl'⟩]
    congr 1
    exact (Classical.choose_spec (⟨l, hl'⟩ : ∃ l, IsGreatest {x | s.mem x = true} l)).unique hl'

theorem natLeast?_eq {S : Nat → Prop} {s : Ivs} (h : ∀ k : Nat, S k ↔ s.mem k = true) :
    natLeast? S = s.natLeast? := by
  unfold natLeast? Ivs.natLeast?
  cases hl : s.nats.least? with
  | none =>
    simp only [Option.map_none]
    rw [dif_neg]
    rintro ⟨k, hk1, hk2⟩
    have : IsLeast {x | s.nats.mem x = true} (k : Int) := by
      refine ⟨?_, ?_⟩
      · show s.nats.mem k = true
        simp [(h k).mp hk1]
      · intro x hx
        have hx : s.nats.mem x = true := hx
        simp only [Ivs.mem_nats, Bool.and_eq_true, decide_eq_true_eq] at hx
        have : S x.toNat := (h _).mpr (by rw [Int.toNat_of_nonneg hx.2]; exact hx.1)
        have := hk2 this; omega
    rw [(Ivs.least?_spec _ _).mpr this] at hl; cases hl
  | some l =>
    obtain ⟨hl1, hl2⟩ := (Ivs.least?_spec _ l).mp hl
    have hl1 : s.nats.mem l = true := hl1
    simp only [Ivs.mem_nats, Bool.and_eq_true, decide_eq_true_eq] at hl1
    have hk : IsLeast {x | S x} l.toNat := by
      refine ⟨(h _).mpr (by rw [Int.toNat_of_nonneg hl1.2]; exact hl1.1), ?_⟩
      intro k hk
      have : l ≤ (k : Int) := hl2 (show s.nats.mem k = true by simp [(h k).mp hk])
      omega
    rw [dif_pos ⟨_, hk⟩]
    simp only [Option.map_some, Option.some.injEq]
    exact (Classical.choose_spec (⟨_, hk⟩ : ∃ l, IsLeast {x | S x} l)).unique hk

theorem natGreatest?_eq {S : Nat → Prop} {s : Ivs} (h : ∀ k : Nat, S k ↔ s.mem k = true) :
    natGreatest? S = s.natGreatest? := by
  unfold natGreatest? Ivs.natGreatest?
  cases hl : s.nats.greatest? with
  | none =>
    simp only [Option.map_none]
    rw [dif_neg]
    rintro ⟨k, hk1, hk2⟩
    have : IsGreatest {x | s.nats.mem x = true} (k : Int) := by
      refine ⟨?_, ?_⟩
      · show s.nats.mem k = true
        simp [(h k).mp hk1]
      · intro x hx
        have hx : s.nats.mem x = true := hx
        simp only [Ivs.mem_nats, Bool.and_eq_true, decide_eq_true_eq] at hx
        have : S x.toNat := (h _).mpr (by rw [Int.toNat_of_nonneg hx.2]; exact hx.1)
        have := hk2 this; omega
    rw [(Ivs.greatest?_spec _ _).mpr this] at hl; cases hl
  | some l =>
    obtain ⟨hl1, hl2⟩ := (Ivs.greatest?_spec _ l).mp hl
    have hl1 : s.nats.mem l = true := hl1
    simp only [Ivs.mem_nats, Bool.and_eq_true, decide_eq_true_eq] at hl1
    have hk : IsGreatest {x | S x} l.toNat := by
      refine ⟨(h _).mpr (by rw [Int.toNat_of_nonneg hl1.2]; exact hl1.1), ?_⟩
      intro k hk
      have : (k : Int) ≤ l := hl2 (show s.nats.mem k = true by simp [(h k).mp hk])
      omega
    rw [dif_pos ⟨_, hk⟩]
    simp only [Option.map_some, Option.some.injEq]
    exact (Classical.choose_spec (⟨_, hk⟩ : ∃ l, IsGreatest {x | S x} l)).unique hk


/-- Two optional results are related: both absent, or both present and related. -/
def ORel {β β' : Type} (R : β → β' → Prop) : Option β → Option β' → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

theorem ORel.getD {β β' : Type} {R : β → β' → Prop} {o : Option β} {o' : Option β'} {d : β} {d' : β'}
    (h : ORel R o o') (hd : R d d') : R (o.getD d) (o'.getD d') := by
  cases o <;> cases o' <;> simp_all [ORel]

theorem evalES_rel {β β' : Type} (R : β → β' → Prop) (A : Alg β) (A' : Alg β')
    (hu : ∀ x x' y y', R x x' → R y y' → R (A.union x y) (A'.union x' y'))
    (hi : ∀ x x' y y', R x x' → R y y' → R (A.inter x y) (A'.inter x' y'))
    (hall : R A.all A'.all) (atom : Elem → Option β) (atom' : Elem → Option β')
    (hat : ∀ e, ORel R (atom e) (atom' e)) : ∀ es, ORel R (evalES A atom es) (evalES A' atom' es)
  | .elem e => by simp only [evalES]; exact hat e
  | .union a b => by
    have ha := evalES_rel R A A' hu hi hall atom atom' hat a
    have hb := evalES_rel R A A' hu hi hall atom atom' hat b
    simp only [evalES]
    revert ha hb
    cases evalES A atom a <;> cases evalES A' atom' a <;> cases evalES A atom b <;>
      cases evalES A' atom' b <;> simp_all [ORel]
  | .inter a b => by
    have ha := evalES_rel R A A' hu hi hall atom atom' hat a
    have hb := evalES_rel R A A' hu hi hall atom atom' hat b
    simp only [evalES]
    revert ha hb
    cases evalES A atom a <;> cases evalES A' atom' a <;> cases evalES A atom b <;>
      cases evalES A' atom' b <;> simp_all [ORel]
  | .except a _ => by simp only [evalES]; exact evalES_rel R A A' hu hi hall atom atom' hat a
  | .allExcept _ => by simp only [evalES, ORel]; exact hall

theorem evalC_rel {β β' : Type} (R : β → β' → Prop) (A : Alg β) (A' : Alg β')
    (hu : ∀ x x' y y', R x x' → R y y' → R (A.union x y) (A'.union x' y'))
    (hi : ∀ x x' y y', R x x' → R y y' → R (A.inter x y) (A'.inter x' y'))
    (hall : R A.all A'.all)
    (ho : ∀ e r r', R r r' → R (A.ofSpecs e r none) (A'.ofSpecs e r' none))
    (hos : ∀ e r r' x x', R r r' → R x x' → R (A.ofSpecs e r (some x)) (A'.ofSpecs e r' (some x')))
    (atom : Elem → Option β) (atom' : Elem → Option β')
    (hat : ∀ e, ORel R (atom e) (atom' e)) (c : Constraint) :
    ORel R (evalC A atom c) (evalC A' atom' c) := by
  cases c with
  | mk root ext adds =>
    have hr := evalES_rel R A A' hu hi hall atom atom' hat root
    simp only [evalC]
    cases adds with
    | none =>
      simp only [Option.map_none]
      revert hr
      cases evalES A atom root <;> cases evalES A' atom' root <;> simp only [ORel] <;>
        (try intro h) <;> (first | trivial | exact ho _ _ _ h)
    | some a =>
      have ha := evalES_rel R A A' hu hi hall atom atom' hat a
      simp only [Option.map_some]
      revert hr ha
      cases evalES A atom root <;> cases evalES A' atom' root <;> cases evalES A atom a <;>
        cases evalES A' atom' a <;> simp only [ORel] <;>
        (try intro h1 h2) <;> (first | trivial | exact hos _ _ _ _ _ h1 h2)
  | _ => simp [evalC, ORel]

theorem view_rel {β β' : Type} (R : β → β' → Prop) (E : Env)
    {base : Scope → Ty → Option β} {empty : β} {rootOnly : β → β}
    {cons : Nat → Scope → Ty → β → (Scope → Ty → β) → Constraint → Option β}
    {base' : Scope → Ty → Option β'} {empty' : β'} {rootOnly' : β' → β'}
    {cons' : Nat → Scope → Ty → β' → (Scope → Ty → β') → Constraint → Option β'}
    (hempty : R empty empty')
    (hbase : ∀ sc t, R ((base sc t).getD empty) ((base' sc t).getD empty'))
    (hroot : ∀ P P', R P P' → R (rootOnly P) (rootOnly' P'))
    (hcons : ∀ n sc t P P' (rec : Scope → Ty → β) (rec' : Scope → Ty → β') c, R P P' →
      (∀ sc t, R (rec sc t) (rec' sc t)) →
      ORel R (cons n sc t P rec c) (cons' n sc t P' rec' c)) :
    ∀ n sc t, R (view E base empty rootOnly cons n sc t) (view E base' empty' rootOnly' cons' n sc t) := by
  intro n
  induction n with
  | zero => intro sc t; simpa [view] using hempty
  | succ n ih =>
    intro sc t
    cases t <;> simp only [view]
    case tagged => exact ih _ _
    case constrained t c => exact (hcons n sc t _ _ _ _ c (ih sc t) ih).getD (hroot _ _ (ih sc t))
    all_goals
      split
      · exact ih _ _
      · exact hbase _ _

/-! ## Value notation -/

open Asn1.X690 (evalLit eqIsEq) in
theorem evalLit_det (E : Env) : ∀ (n : Nat) (sc : Scope) (d d' w : Val),
    evalLit E n sc d = some d' → evalVal E n sc d w → w = d'
  | 0, _, _, _, _, h, _ => by simp [evalLit] at h
  | n + 1, sc, d, d', w, h, hv => by
    cases d with
    | ref mn name args =>
      simp only [evalLit] at h
      simp only [evalVal] at hv
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      rw [hr] at hv
      exact evalLit_det E n sc' v d' w h hv
    | bool _ | int _ | enum _ | oid _ | chars _ | octets _ | bits _ =>
      simp only [evalLit, Option.some.injEq] at h
      simp only [evalVal] at hv
      rw [hv, h]
    | _ => simp [evalLit] at h

open Asn1.X690 (evalLit) in
theorem evalLit_val (E : Env) : ∀ (n : Nat) (sc : Scope) (d d' : Val),
    evalLit E n sc d = some d' → evalVal E n sc d d'
  | 0, _, _, _, h => by simp [evalLit] at h
  | n + 1, sc, d, d', h => by
    cases d with
    | ref mn name args =>
      simp only [evalLit] at h
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [evalVal, hr]
      exact evalLit_val E n sc' v d' h
    | bool _ | int _ | enum _ | oid _ | chars _ | octets _ | bits _ =>
      simp only [evalLit, Option.some.injEq] at h; subst h; simp [evalVal]
    | _ => simp [evalLit] at h

theorem evalLit_iff {E : Env} {n : Nat} {sc : Scope} {d d' : Val} (h : Asn1.X690.evalLit E n sc d = some d')
    (w : Val) : evalVal E n sc d w ↔ w = d' :=
  ⟨evalLit_det E n sc d d' w h, fun hw => hw ▸ evalLit_val E n sc d d' h⟩

theorem intLit_iff {E : Env} {n : Nat} {sc : Scope} {v : Val} {j : Int} (h : intLit E n sc v = some j)
    (w : Val) : evalVal E n sc v w ↔ w = .int j := by
  unfold intLit at h
  split at h
  · rename_i i hl; cases h; exact evalLit_iff hl w
  · cases h

/-! ## Denotations -/

/-- A computed set denotes a PER-visible set, its members read through `f`. -/
def DenF {α : Type} (f : α → Int) (C : CSet) (P : PSet α) : Prop :=
  (∀ x, P.r x ↔ C.r.mem (f x) = true) ∧ (∀ x, P.a x ↔ C.a.mem (f x) = true) ∧ P.ext = C.ext

def Den (C : CSet) (P : PSet Int) : Prop :=
  (∀ i, P.r i ↔ C.r.mem i = true) ∧ (∀ i, P.a i ↔ C.a.mem i = true) ∧ P.ext = C.ext

def DenN (C : CSet) (P : PSet Nat) : Prop :=
  (∀ k : Nat, P.r k ↔ C.r.mem k = true) ∧ (∀ k : Nat, P.a k ↔ C.a.mem k = true) ∧ P.ext = C.ext

theorem den_iff {C : CSet} {P : PSet Int} : Den C P ↔ DenF id C P := Iff.rfl
theorem denN_iff {C : CSet} {P : PSet Nat} : DenN C P ↔ DenF (fun k : Nat => (k : Int)) C P := Iff.rfl

/-- The relation `view_rel` carries: a computed view, when known, denotes the spec's. -/
def RF {α : Type} (f : α → Int) (P : PSet α) (o : Option CSet) : Prop := ∀ C, o = some C → DenF f C P

section
variable {α : Type} {f : α → Int}

theorem DenF.union {A B : CSet} {P Q : PSet α} (h1 : DenF f A P) (h2 : DenF f B Q) :
    DenF f (A.union B) (P.union Q) := by
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · simp [CSet.union, PSet.union, h1.1, h2.1]
  · simp [CSet.union, PSet.union, h1.1, h2.1, h1.2.1, h2.2.1]
  · simp [CSet.union, PSet.union, h1.2.2, h2.2.2]

theorem DenF.inter {A B : CSet} {P Q : PSet α} (h1 : DenF f A P) (h2 : DenF f B Q) :
    DenF f (A.inter B) (P.inter Q) := by
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · simp [CSet.inter, PSet.inter, h1.1, h2.1]
  · simp [CSet.inter, PSet.inter, h1.1, h2.1, h1.2.1, h2.2.1]
  · simp [CSet.inter, PSet.inter, h1.2.2, h2.2.2]

theorem DenF.ofSpecs (e : Bool) {A : CSet} {P : PSet α} (h1 : DenF f A P) :
    DenF f (CSet.ofSpecs e A none) (PSet.ofSpecs e P none) := by
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.1]
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.2.1]
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.2.2]

theorem DenF.ofSpecsSome (e : Bool) {A B : CSet} {P Q : PSet α} (h1 : DenF f A P) (h2 : DenF f B Q) :
    DenF f (CSet.ofSpecs e A (some B)) (PSet.ofSpecs e P (some Q)) := by
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.1]
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.2.1, h2.2.1]
  · simp [CSet.ofSpecs, PSet.ofSpecs, h1.2.2]

theorem DenF.plain {s : Ivs} {g : α → Prop} (h : ∀ x, g x ↔ s.mem (f x) = true) :
    DenF f (CSet.plain s) (PSet.plain g) :=
  ⟨h, h, rfl⟩

theorem DenF.rootOnly {A : CSet} {P : PSet α} (h : DenF f A P) : DenF f A.rootOnly P.rootOnly :=
  DenF.plain h.1

theorem DenF.within {A : CSet} {P : PSet α} {s : Ivs} {g : α → Prop} (hg : ∀ x, g x ↔ s.mem (f x) = true)
    (h : DenF f A P) : DenF f (A.within s) (P.within g) := by
  refine ⟨fun x => ?_, fun x => ?_, h.2.2⟩
  · simp [CSet.within, PSet.within, hg, h.1]
  · simp [CSet.within, PSet.within, hg, h.2.1]

theorem DenF.empty : DenF f CSet.empty (PSet.empty : PSet α) :=
  ⟨fun _ => by simp [CSet.empty, PSet.empty], fun _ => by simp [CSet.empty, PSet.empty], rfl⟩

/-- The algebra of a computed view, against `psetAlg` of the spec, under a parent related by `RF`. -/
theorem cAlg_rel {P : PSet α} {P' : Option CSet} (hP : RF f P P') :
    (∀ x x' y y', RF f x x' → RF f y y' → RF f ((psetAlg P.r).union x y) ((cAlg (P'.map (·.r))).union x' y')) ∧
    (∀ x x' y y', RF f x x' → RF f y y' → RF f ((psetAlg P.r).inter x y) ((cAlg (P'.map (·.r))).inter x' y')) ∧
    RF f (psetAlg P.r).all (cAlg (P'.map (·.r))).all ∧
    (∀ e r r', RF f r r' → RF f ((psetAlg P.r).ofSpecs e r none) ((cAlg (P'.map (·.r))).ofSpecs e r' none)) ∧
    (∀ e r r' x x', RF f r r' → RF f x x' →
      RF f ((psetAlg P.r).ofSpecs e r (some x)) ((cAlg (P'.map (·.r))).ofSpecs e r' (some x'))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy C hC
    cases x' <;> cases y' <;> simp [cAlg, optAlg, csetAlg] at hC
    subst hC; exact (hx _ rfl).union (hy _ rfl)
  · intro x x' y y' hx hy C hC
    cases x' <;> cases y' <;> simp [cAlg, optAlg, csetAlg] at hC
    subst hC; exact (hx _ rfl).inter (hy _ rfl)
  · intro C hC
    cases P' <;> simp [cAlg, optAlg] at hC
    subst hC; exact DenF.plain (hP _ rfl).1
  · intro e r r' hr C hC
    cases r' <;> simp [cAlg, optAlg, csetAlg] at hC
    subst hC; exact (hr _ rfl).ofSpecs e
  · intro e r r' x x' hr hx C hC
    cases r' <;> cases x' <;> simp [cAlg, optAlg, csetAlg] at hC
    subst hC; exact (hr _ rfl).ofSpecsSome e (hx _ rfl)

end


/-! ## Integers -/

/-- The lower half of `InRange`. -/
def LoPart (lo : Bound) (loOpen : Bool) (w : Val) : Prop :=
  match lo with
  | .min => True
  | .max => False
  | .val v => if loOpen then v.lt w else v.le w

def HiPart (hi : Bound) (hiOpen : Bool) (w : Val) : Prop :=
  match hi with
  | .max => True
  | .min => False
  | .val v => if hiOpen then w.lt v else w.le v

theorem inRange_iff (lo : Bound) (lo' : Bool) (hi : Bound) (hi' : Bool) (w : Val) :
    InRange lo lo' hi hi' w ↔ LoPart lo lo' w ∧ HiPart hi hi' w := Iff.rfl

/-- What an end computed by `loEnd` says of `i`: `some e`, above the bound `e`; `none`, nothing. -/
def endLo : Option (Option Int) → Int → Prop
  | some e, i => e.all (· ≤ i) = true
  | none, _ => False

def endHi : Option (Option Int) → Int → Prop
  | some e, i => e.all (i ≤ ·) = true
  | none, _ => False

theorem loEnd_spec {E : Env} {n : Nat} {sc : Scope} {lo : Bound} {op : Bool} {r : Option (Option Int)}
    (h : loEnd E n sc lo op = some r) (i : Int) :
    (∃ l, EvalBound E n sc lo l ∧ LoPart l op (.int i)) ↔ endLo r i := by
  cases n with
  | zero => simp [loEnd] at h; subst h; simp [EvalBound, endLo, endHi]
  | succ n =>
    cases lo with
    | min => simp [loEnd] at h; subst h; simp [EvalBound, LoPart, endLo]
    | max => simp [loEnd] at h; subst h; simp [EvalBound, LoPart, endLo]
    | val v =>
      simp only [loEnd] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [EvalBound, intLit_iff hj, endLo, endHi]
      constructor
      · rintro ⟨l, ⟨w, rfl, rfl⟩, hl⟩
        cases op <;> simp_all [LoPart, Val.lt, Val.le] <;> omega
      · intro hi
        refine ⟨_, ⟨_, rfl, rfl⟩, ?_⟩
        cases op <;> simp_all [LoPart, Val.lt, Val.le] <;> omega

theorem hiEnd_spec {E : Env} {n : Nat} {sc : Scope} {hi : Bound} {op : Bool} {r : Option (Option Int)}
    (h : hiEnd E n sc hi op = some r) (i : Int) :
    (∃ l, EvalBound E n sc hi l ∧ HiPart l op (.int i)) ↔ endHi r i := by
  cases n with
  | zero => simp [hiEnd] at h; subst h; simp [EvalBound, endLo, endHi]
  | succ n =>
    cases hi with
    | min => simp [hiEnd] at h; subst h; simp [EvalBound, HiPart, endHi]
    | max => simp [hiEnd] at h; subst h; simp [EvalBound, HiPart, endHi]
    | val v =>
      simp only [hiEnd] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [EvalBound, intLit_iff hj, endLo, endHi]
      constructor
      · rintro ⟨l, ⟨w, rfl, rfl⟩, hl⟩
        cases op <;> simp_all [HiPart, Val.lt, Val.le] <;> omega
      · intro hi
        refine ⟨_, ⟨_, rfl, rfl⟩, ?_⟩
        cases op <;> simp_all [HiPart, Val.lt, Val.le] <;> omega

abbrev RI : PSet Int → Option CSet → Prop := RF (fun i => i)

theorem intAtom_rel {E : Env} {n : Nat} {sc : Scope} {P : PSet Int} {P' : Option CSet} (hP : RI P P')
    {rec : Scope → Ty → PSet Int} {rec' : Scope → Ty → Option CSet} (hrec : ∀ sc t, RI (rec sc t) (rec' sc t))
    (e : Elem) : ORel RI (intAtom E n sc P.r rec e) (intAtomC E n sc (P'.map (·.r)) rec' e) := by
  cases e with
  | single v =>
    simp only [intAtom, intAtomC, ORel]
    intro C hC
    cases P' with
    | none => simp at hC
    | some PC =>
      cases hj : intLit E n sc v with
      | none => simp [hj] at hC
      | some j =>
        simp only [hj, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hC
        subst hC
        refine DenF.plain fun i => ?_
        simp [intLit_iff hj, (hP PC rfl).1 i]
  | range lo lo' hi hi' =>
    simp only [intAtom, intAtomC, ORel]
    intro C hC
    cases P' with
    | none => simp at hC
    | some PC =>
      cases hl : loEnd E n sc lo lo' with
      | none => simp [hl] at hC
      | some l =>
      cases hh : hiEnd E n sc hi hi' with
      | none => simp [hl, hh] at hC
      | some h =>
        simp only [hl, hh, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hC
        have key : ∀ i, (∃ l h, EvalBound E n sc lo l ∧ EvalBound E n sc hi h ∧ RangeHas l lo' h hi' (.int i)) ↔
            endLo l i ∧ endHi h i := by
          intro i
          rw [← loEnd_spec hl i, ← hiEnd_spec hh i]
          simp only [RangeHas, inRange_iff]
          constructor
          · rintro ⟨a, b, ha, hb, h1, h2⟩; exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
          · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩; exact ⟨a, b, ha, hb, h1, h2⟩
        cases l <;> cases h <;> simp only [Option.some.injEq] at hC <;> subst hC <;>
          refine DenF.plain fun i => ?_ <;> rw [key, (hP PC rfl).1 i] <;> (try rw [Ivs.mem_inter]) <;> simp [Ivs.mem, Ivs.memI, endLo, endHi]
  | contained t x =>
    simp only [intAtom, intAtomC]
    split
    · simp [ORel]
    · simp only [ORel]
      intro C hC
      cases P' with
      | none => simp at hC
      | some PC =>
        cases hq : rec' sc t with
        | none => simp [hq] at hC
        | some Q =>
          simp only [hq, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hC
          subst hC
          refine DenF.plain fun i => ?_
          simp [(hP PC rfl).1 i, (hrec sc t Q hq).1 i]
  | _ => simp [intAtom, intAtomC, ORel]

theorem intCons_rel {E : Env} {n : Nat} {sc : Scope} {P : PSet Int} {P' : Option CSet} (hP : RI P P')
    {rec : Scope → Ty → PSet Int} {rec' : Scope → Ty → Option CSet} (hrec : ∀ sc t, RI (rec sc t) (rec' sc t))
    (c : Constraint) : ORel RI (intCons E n sc P rec c) (intConsC E n sc P' rec' c) := by
  unfold intCons intConsC
  split
  · simp [ORel]
  · obtain ⟨hu, hi, hall, ho, hos⟩ := cAlg_rel hP
    exact evalC_rel RI _ _ hu hi hall ho hos _ _ (intAtom_rel hP hrec) c

theorem pIntC_rel (E : Env) : ∀ n sc t, RI (pInt E n sc t) (pIntC E n sc t) := by
  unfold pInt pIntC
  apply view_rel RI E
  · intro C hC; cases hC; exact DenF.empty
  · intro sc t
    cases t <;> simp only [Option.getD_none, Option.getD_some] <;>
      first
      | (intro C hC; cases hC; exact DenF.empty)
      | (intro C hC; cases hC; exact DenF.plain fun i => by simp)
  · intro P P' h C hC
    cases P' with
    | none => cases hC
    | some PC => cases hC; exact (h PC rfl).rootOnly
  · intro n sc t P P' rec rec' c hP hrec
    exact intCons_rel hP hrec c

theorem pIntC_sound {E : Env} {n : Nat} {sc : Scope} {t : Ty} {C : CSet} (h : pIntC E n sc t = some C) :
    Den C (pInt E n sc t) :=
  pIntC_rel E n sc t C h


/-! ## Sizes -/

abbrev RN : PSet Nat → Option CSet → Prop := RF (fun k : Nat => (k : Int))

theorem sizeOf_rel {E : Env} {n : Nat} {sc : Scope}
    {rec : Scope → Ty → PSet Int} {rec' : Scope → Ty → Option CSet} (hrec : ∀ sc t, RI (rec sc t) (rec' sc t))
    (c : Constraint) : ORel RN (sizeOf E n sc rec c) (sizeOfC E n sc rec' c) := by
  have h0 : RI (PSet.plain fun i => 0 ≤ i) (some (CSet.plain [(some 0, none)])) := by
    intro C hC; cases hC; exact DenF.plain fun i => by simp [Ivs.mem, Ivs.memI]
  have := intCons_rel (E := E) (n := n) (sc := sc) h0 hrec c
  unfold sizeOf sizeOfC
  revert this
  cases intCons E n sc (PSet.plain fun i => 0 ≤ i) rec c <;>
    cases intConsC E n sc (some (CSet.plain [(some 0, none)])) rec' c <;> simp only [ORel, Option.map_none, Option.map_some] <;>
    first
    | exact id
    | exact fun h => h.elim
    | (intro h C hC
       have h := h C hC
       exact ⟨fun k => h.1 k, fun k => h.2.1 k, h.2.2⟩)

theorem sizeAtom_rel {E : Env} {n : Nat} {sc : Scope} {P : PSet Nat} {P' : Option CSet} (hP : RN P P')
    (e : Elem) : ORel RN (sizeAtom E n sc P.r e) (sizeAtomC E n sc (P'.map (·.r)) e) := by
  cases e with
  | size c =>
    have := sizeOf_rel (E := E) (n := n) (sc := sc) (pIntC_rel E n) c
    simp only [sizeAtom, sizeAtomC]
    revert this
    cases sizeOf E n sc (pInt E n) c <;> cases sizeOfC E n sc (pIntC E n) c <;>
      simp only [ORel, Option.map_none, Option.map_some] <;> try (first | exact id | exact fun h => h.elim)
    · rename_i Q Q'
      intro h C hC
      cases P' with
      | none => simp at hC
      | some PC =>
        cases Q' with
        | none => simp at hC
        | some QC =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hC
          subst hC
          exact (h QC rfl).within (hP PC rfl).1
  | _ => simp [sizeAtom, sizeAtomC, ORel]

theorem pSizeC_rel (E : Env) : ∀ n sc t, RN (pSize E n sc t) (pSizeC E n sc t) := by
  unfold pSize pSizeC
  apply view_rel RN E
  · intro C hC; cases hC; exact DenF.empty
  · intro sc t
    cases t <;> simp only [Option.getD_none, Option.getD_some] <;>
      first
      | (intro C hC; cases hC; exact DenF.empty)
      | (intro C hC; cases hC; exact DenF.plain fun i => by simp)
  · intro P P' h C hC
    cases P' with
    | none => cases hC
    | some PC => cases hC; exact (h PC rfl).rootOnly
  · intro n sc t P P' rec rec' c hP hrec
    split
    · simp [ORel]
    · obtain ⟨hu, hi, hall, ho, hos⟩ := cAlg_rel hP
      exact evalC_rel RN _ _ hu hi hall ho hos _ _ (sizeAtom_rel hP) c

theorem pSizeC_sound {E : Env} {n : Nat} {sc : Scope} {t : Ty} {C : CSet} (h : pSizeC E n sc t = some C) :
    DenN C (pSize E n sc t) :=
  pSizeC_rel E n sc t C h


/-! ## Known-multiplier strings: FROM -/

theorem valEqIsEq_eqv (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    valEqIsEq E n sc t = true → (eqv E n sc t x y ↔ x = y)
  | 0, _, _, _, _, h => by simp [valEqIsEq] at h
  | n + 1, sc, t, x, y, h => by
    cases t with
    | ref name =>
      simp only [valEqIsEq] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact valEqIsEq_eqv E n sc' t' x y h
      · cases h
    | extRef mn name =>
      simp only [valEqIsEq] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact valEqIsEq_eqv E n sc' t' x y h
      · cases h
    | paramRef mn name args =>
      simp only [valEqIsEq] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact valEqIsEq_eqv E n sc' t' x y h
      · cases h
    | tagged tg k t =>
      simp only [valEqIsEq] at h; simp only [eqv]; exact valEqIsEq_eqv E n sc t x y h
    | constrained t c =>
      simp only [valEqIsEq] at h; simp only [eqv]; exact valEqIsEq_eqv E n sc t x y h
    | boolean | integer _ | enumerated _ _ | null | objectIdentifier | relativeOid | octetString
    | restricted _ | utcTime | generalizedTime =>
      simp [eqv]
    | _ => simp [valEqIsEq] at h

theorem le_chars_left (a : Nat) (w : Val) : Val.le (.chars [a]) w ↔ ∃ c, w = .chars [c] ∧ a ≤ c := by
  cases w with
  | chars l => rcases l with _ | ⟨c, _ | ⟨_, _⟩⟩ <;> simp [Val.le]
  | _ => simp [Val.le]

theorem le_chars_right (b : Nat) (w : Val) : Val.le w (.chars [b]) ↔ ∃ c, w = .chars [c] ∧ c ≤ b := by
  cases w with
  | chars l => rcases l with _ | ⟨c, _ | ⟨_, _⟩⟩ <;> simp [Val.le]
  | _ => simp [Val.le]

theorem lt_chars_left (a : Nat) (w : Val) : Val.lt (.chars [a]) w ↔ ∃ c, w = .chars [c] ∧ a < c := by
  simp only [Val.lt, le_chars_left, le_chars_right]
  constructor
  · rintro ⟨⟨c, rfl, h⟩, h2⟩
    refine ⟨c, rfl, ?_⟩
    by_contra hc; exact h2 ⟨c, rfl, by omega⟩
  · rintro ⟨c, rfl, h⟩
    refine ⟨⟨c, rfl, by omega⟩, ?_⟩
    rintro ⟨d, hd, h'⟩; cases hd; omega

theorem lt_chars_right (b : Nat) (w : Val) : Val.lt w (.chars [b]) ↔ ∃ c, w = .chars [c] ∧ c < b := by
  simp only [Val.lt, le_chars_left, le_chars_right]
  constructor
  · rintro ⟨⟨c, rfl, h⟩, h2⟩
    refine ⟨c, rfl, ?_⟩
    by_contra hc; exact h2 ⟨c, rfl, by omega⟩
  · rintro ⟨c, rfl, h⟩
    refine ⟨⟨c, rfl, by omega⟩, ?_⟩
    rintro ⟨d, hd, h'⟩; cases hd; omega

/-- What an end computed by `charEnd` says of a value. -/
def charLo : Option (Option Int) → Val → Prop
  | some (some e), w => ∃ c : Nat, w = .chars [c] ∧ e ≤ c
  | some none, _ => True
  | none, _ => False

def charHi : Option (Option Int) → Val → Prop
  | some (some e), w => ∃ c : Nat, w = .chars [c] ∧ (c : Int) ≤ e
  | some none, _ => True
  | none, _ => False

theorem charEnd_lo {E : Env} {k : Nat} {sc : Scope} {lo : Bound} {op : Bool} {r : Option (Option Int)}
    (h : charEnd E true (k + 1) sc lo op = some r) (w : Val) :
    (∃ l, EvalBound E (k + 1) sc lo l ∧ LoPart l op w) ↔ charLo r w := by
  cases lo with
  | min => simp [charEnd] at h; subst h; simp [EvalBound, LoPart, charLo]
  | max => simp [charEnd] at h; subst h; simp [EvalBound, LoPart, charLo]
  | val v =>
    simp only [charEnd] at h
    split at h
    · rename_i c hc
      simp only [Option.some.injEq, ite_true] at h; subst h
      simp only [EvalBound, evalLit_iff hc, charLo]
      constructor
      · rintro ⟨l, ⟨w', rfl, rfl⟩, hl⟩
        cases op <;> simp only [LoPart, Bool.false_eq_true, ite_false, ite_true, le_chars_left, lt_chars_left] at hl <;>
          obtain ⟨c', rfl, hc'⟩ := hl <;> exact ⟨c', rfl, by simp only [Bool.false_eq_true, ite_false, ite_true]; omega⟩
      · rintro ⟨c', rfl, hc'⟩
        refine ⟨_, ⟨_, rfl, rfl⟩, ?_⟩
        cases op <;> simp only [LoPart, Bool.false_eq_true, ite_false, ite_true, le_chars_left, lt_chars_left] <;>
          exact ⟨c', rfl, by simp only [Bool.false_eq_true, ite_false, ite_true] at hc'; omega⟩
    · cases h

theorem charEnd_hi {E : Env} {k : Nat} {sc : Scope} {hi : Bound} {op : Bool} {r : Option (Option Int)}
    (h : charEnd E false (k + 1) sc hi op = some r) (w : Val) :
    (∃ l, EvalBound E (k + 1) sc hi l ∧ HiPart l op w) ↔ charHi r w := by
  cases hi with
  | min => simp [charEnd] at h; subst h; simp [EvalBound, HiPart, charHi]
  | max => simp [charEnd] at h; subst h; simp [EvalBound, HiPart, charHi]
  | val v =>
    simp only [charEnd] at h
    split at h
    · rename_i c hc
      simp only [Option.some.injEq, Bool.false_eq_true, ite_false] at h; subst h
      simp only [EvalBound, evalLit_iff hc, charHi]
      constructor
      · rintro ⟨l, ⟨w', rfl, rfl⟩, hl⟩
        cases op <;> simp only [HiPart, Bool.false_eq_true, ite_false, ite_true, le_chars_right, lt_chars_right] at hl <;>
          obtain ⟨c', rfl, hc'⟩ := hl <;> exact ⟨c', rfl, by simp only [Bool.false_eq_true, ite_false, ite_true]; omega⟩
      · rintro ⟨c', rfl, hc'⟩
        refine ⟨_, ⟨_, rfl, rfl⟩, ?_⟩
        cases op <;> simp only [HiPart, Bool.false_eq_true, ite_false, ite_true, le_chars_right, lt_chars_right] <;>
          exact ⟨c', rfl, by simp only [Bool.false_eq_true, ite_false, ite_true] at hc'; omega⟩
    · cases h

/-- A fixed element set (its root is all its values, not extensible) whose values' characters are
the members of `x`. -/
def FixedChars (X : ESet) (x : Ivs) : Prop :=
  X.ext = false ∧ (∀ w, X.r w ↔ X.a w) ∧ ∀ ch : Nat, (∃ s, X.r s ∧ ch ∈ s.charList) ↔ x.mem ch = true

theorem FixedChars.empty : FixedChars ESet.empty [] := by
  refine ⟨rfl, fun _ => Iff.rfl, fun ch => ?_⟩
  simp [ESet.empty]

theorem mem_charIvs (cs : List Nat) (ch : Nat) : (charIvs cs).mem ch = true ↔ ch ∈ cs := by
  simp [charIvs, Ivs.mem, Ivs.memI]
  constructor
  · rintro ⟨c, hc, h1, h2⟩; have : ch = c := by omega
    exact this ▸ hc
  · intro h; exact ⟨ch, h, le_refl _, le_refl _⟩

theorem from_spec {E : Env} {H : ContentsHook} {sc : Scope} {pt : Ty} {S A : Ivs} {Sp Ap : Nat → Prop}
    (hS : ∀ k : Nat, Sp k ↔ S.mem k = true) (hA : ∀ c : Nat, Ap c ↔ A.mem c = true) :
    ∀ k, (∀ es x, fromES E sc pt S A k es = some x →
        FixedChars (eset E H k sc [] pt (stringsOver Sp Ap) es) x) ∧
      (∀ el x, fromElem E sc pt S A k el = some x →
        FixedChars (elem E H k sc [] pt (stringsOver Sp Ap) el) x) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun es x h => ?_, fun el x h => ?_⟩
    · simp [fromES] at h; subst h; simpa [eset] using FixedChars.empty
    · simp [fromElem] at h; subst h; simpa [elem] using FixedChars.empty
  | succ k ih =>
    refine ⟨fun es x h => ?_, fun el x h => ?_⟩
    · cases es with
      | elem el => simp only [fromES] at h; simp only [eset]; exact ih.2 el x h
      | union a b =>
        simp only [fromES, Option.bind_eq_bind, Option.pure_def] at h
        obtain ⟨xa, ha, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨xb, hb, h⟩ := Option.bind_eq_some_iff.mp h
        cases h
        obtain ⟨ea, ra, ca⟩ := ih.1 a xa ha
        obtain ⟨eb, rb, cb⟩ := ih.1 b xb hb
        simp only [eset]
        refine ⟨by simp [ESet.union, ea, eb], fun w => ?_, fun ch => ?_⟩
        · simp only [ESet.union, ← ra, ← rb]; tauto
        · simp only [ESet.union, Ivs.mem_append, Bool.or_eq_true, ← ca, ← cb]
          constructor
          · rintro ⟨s, hs | hs, hc⟩
            · exact Or.inl ⟨s, hs, hc⟩
            · exact Or.inr ⟨s, hs, hc⟩
          · rintro (⟨s, hs, hc⟩ | ⟨s, hs, hc⟩)
            · exact ⟨s, Or.inl hs, hc⟩
            · exact ⟨s, Or.inr hs, hc⟩
      | _ => simp [fromES] at h
    · cases el with
      | single v =>
        simp only [fromElem] at h
        split at h
        · rename_i cs hcs
          split at h
          · rename_i hq
            simp only [Option.some.injEq] at h; subst h
            simp only [elem]
            refine ⟨rfl, fun _ => Iff.rfl, fun ch => ?_⟩
            simp only [ESet.fixed, evalLit_iff hcs, valEqIsEq_eqv E k sc pt _ _ hq, exists_eq_left]
            constructor
            · rintro ⟨s, ⟨⟨cs', hs, hl, hall⟩, rfl⟩, hc⟩
              cases hs
              have h1 : S.mem cs.length = true := (hS _).mp hl
              have h2 : (cs.all fun c => A.mem c) = true := List.all_eq_true.mpr fun c hc => (hA c).mp (hall c hc)
              simp only [h1, h2, Bool.and_self, ite_true, mem_charIvs]; exact hc
            · intro hm
              by_cases hg : (S.mem cs.length && cs.all fun c => A.mem c) = true
              · rw [if_pos hg, mem_charIvs] at hm
                simp only [Bool.and_eq_true, List.all_eq_true] at hg
                exact ⟨_, ⟨⟨cs, rfl, (hS _).mpr hg.1, fun c hc => (hA c).mpr (hg.2 c hc)⟩, rfl⟩, hm⟩
              · rw [if_neg hg] at hm; simp at hm
          · cases h
        · cases h
      | range lo lo' hi hi' =>
        cases k with
        | zero =>
          simp only [fromElem, Option.some.injEq] at h; subst h
          simp only [elem]
          refine ⟨rfl, fun _ => Iff.rfl, fun ch => ?_⟩
          simp [ESet.fixed, EvalBound]
        | succ k' =>
          simp only [fromElem] at h
          have key : ∀ rl rh, charEnd E true (k' + 1) sc lo lo' = some rl →
              charEnd E false (k' + 1) sc hi hi' = some rh → ∀ cs,
              (∃ l h, EvalBound E (k' + 1) sc lo l ∧ EvalBound E (k' + 1) sc hi h ∧
                RangeHas l lo' h hi' (.chars cs)) ↔ (charLo rl (.chars cs) ∧ charHi rh (.chars cs)) := by
            intro rl rh hl hh cs
            rw [← charEnd_lo hl, ← charEnd_hi hh]
            simp only [RangeHas, inRange_iff]
            constructor
            · rintro ⟨a, b, ha, hb, h1, h2⟩; exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
            · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩; exact ⟨a, b, ha, hb, h1, h2⟩
          simp only [elem]
          refine ⟨rfl, fun _ => Iff.rfl, fun ch => ?_⟩
          simp only [ESet.fixed]
          split at h
          · rename_i l hh hl hhh
            split at h
            · cases h
            · rename_i hnn
              simp only [Option.some.injEq] at h; subst h
              constructor
              · rintro ⟨s, ⟨⟨cs, rfl, hlen, hall⟩, hr⟩, hc⟩
                rw [key _ _ hl hhh] at hr
                obtain ⟨h1, h2⟩ := hr
                have hcs : ∃ c : Nat, cs = [c] ∧ l.all (· ≤ (c : Int)) = true ∧ hh.all ((c : Int) ≤ ·) = true := by
                  cases l with
                  | some e =>
                    obtain ⟨c, hcs, he⟩ := h1; cases hcs
                    refine ⟨c, rfl, by simpa using he, ?_⟩
                    cases hh with
                    | some f => obtain ⟨c', hcs', hf⟩ := h2; cases hcs'; simpa using hf
                    | none => rfl
                  | none =>
                    cases hh with
                    | some f =>
                      obtain ⟨c, hcs, hf⟩ := h2; cases hcs
                      exact ⟨c, rfl, rfl, by simpa using hf⟩
                    | none => simp at hnn
                obtain ⟨c, rfl, hlo, hhi⟩ := hcs
                simp only [Val.charList, List.mem_singleton] at hc; subst hc
                have hS1 : S.mem 1 = true := (hS 1).mp hlen
                rw [if_pos hS1, Ivs.mem_inter]
                simp only [Bool.and_eq_true]
                refine ⟨(hA _).mp (hall _ (List.mem_singleton_self _)), ?_⟩
                simp [Ivs.mem, Ivs.memI, hlo, hhi]
              · intro hm
                by_cases hS1 : S.mem 1 = true
                · rw [if_pos hS1, Ivs.mem_inter, Bool.and_eq_true] at hm
                  obtain ⟨hAc, hI⟩ := hm
                  simp only [Ivs.mem, List.any_cons, List.any_nil, Bool.or_false, Ivs.memI,
                    Bool.and_eq_true] at hI
                  refine ⟨.chars [ch], ⟨⟨[ch], rfl, (hS 1).mpr hS1, ?_⟩, ?_⟩, by simp [Val.charList]⟩
                  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact (hA _).mpr hAc
                  · rw [key _ _ hl hhh]
                    refine ⟨?_, ?_⟩
                    · cases l with
                      | some e => exact ⟨ch, rfl, by simpa using hI.1⟩
                      | none => trivial
                    · cases hh with
                      | some f => exact ⟨ch, rfl, by simpa using hI.2⟩
                      | none => trivial
                · rw [if_neg hS1] at hm; simp at hm
          · rename_i rh hl hhh
            simp only [Option.some.injEq] at h; subst h
            simp only [Ivs.mem_nil, Bool.false_eq_true, iff_false]
            rintro ⟨s, ⟨⟨cs, rfl, _, _⟩, hr⟩, _⟩
            rw [key _ _ hl hhh] at hr
            exact hr.1
          · rename_i rl hl hhh
            simp only [Option.some.injEq] at h; subst h
            simp only [Ivs.mem_nil, Bool.false_eq_true, iff_false]
            rintro ⟨s, ⟨⟨cs, rfl, _, _⟩, hr⟩, _⟩
            rw [key _ _ hl hhh] at hr
            exact hr.2
          · cases h
      | _ => simp [fromElem] at h


theorem fromC_spec {E : Env} {H : ContentsHook} {sc : Scope} {pt : Ty} {S A : Ivs} {Sp Ap : Nat → Prop}
    (hS : ∀ k : Nat, Sp k ↔ S.mem k = true) (hA : ∀ c : Nat, Ap c ↔ A.mem c = true) {n : Nat}
    {c : Constraint} {V : CSet} (h : fromC E sc pt S A n c = some V) :
    DenF (fun k : Nat => (k : Int)) V
      ⟨fun ch => Ap ch ∧ ∃ s, (cons E H n sc [] pt ⟨stringsOver Sp Ap, stringsOver Sp Ap, false⟩ c).root s ∧
          ch ∈ s.charList,
       fun ch => Ap ch ∧ ∃ s, (cons E H n sc [] pt ⟨stringsOver Sp Ap, stringsOver Sp Ap, false⟩ c).all s ∧
          ch ∈ s.charList,
       (cons E H n sc [] pt ⟨stringsOver Sp Ap, stringsOver Sp Ap, false⟩ c).ext⟩ := by
  cases n with
  | zero =>
    simp only [fromC, Option.some.injEq] at h; subst h
    refine ⟨fun ch => ?_, fun ch => ?_, rfl⟩ <;> simp [cons, VSet.empty, CSet.empty]
  | succ m =>
    cases c with
    | mk root ext adds =>
      unfold fromC at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      obtain ⟨er, rr, cr⟩ := (from_spec (H := H) hS hA m).1 root r hr
      have hxa : ∀ ch : Nat, (∃ s, (∃ e, adds.map (eset E H m sc [] pt (stringsOver Sp Ap)) = some e ∧ e.a s) ∧
          ch ∈ s.charList) ↔ x.mem ch = true := by
        intro ch
        cases adds with
        | none => simp at hx; subst hx; simp
        | some a =>
          simp only [Option.map_some, Option.getD_some] at hx
          obtain ⟨_, ra, ca⟩ := (from_spec (H := H) hS hA m).1 a x hx
          simp only [Option.map_some, Option.some.injEq, exists_eq_left', ← ca]
          constructor
          · rintro ⟨s, hs, hc⟩; exact ⟨s, (ra s).mpr hs, hc⟩
          · rintro ⟨s, hs, hc⟩; exact ⟨s, (ra s).mp hs, hc⟩
      refine ⟨fun ch => ?_, fun ch => ?_, ?_⟩
      · simp only [cons, VSet.keepExt, VSet.ofSpecs, Ivs.mem_inter, Bool.and_eq_true, ← hA, ← cr]
      · simp only [cons, VSet.keepExt, VSet.ofSpecs, Ivs.mem_inter, Ivs.mem_append, Bool.and_eq_true,
          Bool.or_eq_true, ← hA, ← cr, ← hxa]
        constructor
        · rintro ⟨ha, s, hs | hs, hc⟩
          · exact ⟨ha, Or.inl ⟨s, (rr s).mpr hs, hc⟩⟩
          · exact ⟨ha, Or.inr ⟨s, hs, hc⟩⟩
        · rintro ⟨ha, ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩⟩
          · exact ⟨ha, s, Or.inl ((rr s).mp hs), hc⟩
          · exact ⟨ha, s, Or.inr hs, hc⟩
      · simp [cons, VSet.keepExt, VSet.ofSpecs, er]
    | _ => simp [fromC] at h


/-! ## Known-multiplier strings: the view -/

abbrev RS (P : PSet Nat × PSet Nat) (o : Option (CSet × CSet)) : Prop :=
  ∀ C, o = some C → DenF (fun k : Nat => (k : Int)) C.1 P.1 ∧ DenF (fun k : Nat => (k : Int)) C.2 P.2

theorem pairAlg_rel {P : PSet Nat × PSet Nat} {P' : Option (CSet × CSet)} (hP : RS P P') :
    let g := P'.map fun P => (P.1.r, P.2.r)
    let A := pairAlg P.1.r P.2.r
    let A' := optAlg (pairAlgC ((g.map (·.1)).getD []) ((g.map (·.2)).getD []))
          (g.map fun (S, A) => (CSet.plain S, CSet.plain A))
    (∀ x x' y y', RS x x' → RS y y' → RS (A.union x y) (A'.union x' y')) ∧
    (∀ x x' y y', RS x x' → RS y y' → RS (A.inter x y) (A'.inter x' y')) ∧
    RS A.all A'.all ∧
    (∀ e r r', RS r r' → RS (A.ofSpecs e r none) (A'.ofSpecs e r' none)) ∧
    (∀ e r r' x x', RS r r' → RS x x' → RS (A.ofSpecs e r (some x)) (A'.ofSpecs e r' (some x'))) := by
  intro g A A'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy C hC
    cases x' <;> cases y' <;> simp [A', optAlg, pairAlgC] at hC
    subst hC
    obtain ⟨h1, h2⟩ := hx _ rfl; obtain ⟨h3, h4⟩ := hy _ rfl
    exact ⟨h1.union h3, h2.union h4⟩
  · intro x x' y y' hx hy C hC
    cases x' <;> cases y' <;> simp [A', optAlg, pairAlgC] at hC
    subst hC
    obtain ⟨h1, h2⟩ := hx _ rfl; obtain ⟨h3, h4⟩ := hy _ rfl
    exact ⟨h1.inter h3, h2.inter h4⟩
  · intro C hC
    cases P' <;> simp [A', g, optAlg] at hC
    subst hC
    obtain ⟨h1, h2⟩ := hP _ rfl
    exact ⟨DenF.plain h1.1, DenF.plain h2.1⟩
  · intro e r r' hr C hC
    cases r' <;> simp [A', optAlg, pairAlgC] at hC
    subst hC
    obtain ⟨h1, h2⟩ := hr _ rfl
    exact ⟨h1.ofSpecs e, h2.ofSpecs e⟩
  · intro e r r' x x' hr hx C hC
    cases r' <;> cases x' <;> simp [A', optAlg, pairAlgC] at hC
    subst hC
    obtain ⟨h1, h2⟩ := hr _ rfl; obtain ⟨h3, h4⟩ := hx _ rfl
    exact ⟨h1.ofSpecsSome e h3, h2.ofSpecsSome e h4⟩

theorem strAtom_rel {E : Env} {n : Nat} {sc : Scope} {pt : Ty} {P : PSet Nat × PSet Nat}
    {P' : Option (CSet × CSet)} (hP : RS P P')
    {rec : Scope → Ty → PSet Nat × PSet Nat} {rec' : Scope → Ty → Option (CSet × CSet)}
    (hrec : ∀ sc t, RS (rec sc t) (rec' sc t)) (e : Elem) :
    ORel RS (strAtom E n sc pt P.1.r P.2.r rec e)
      (strAtomC E n sc pt (P'.map fun P => (P.1.r, P.2.r)) rec' e) := by
  cases e with
  | size c =>
    have := sizeOf_rel (E := E) (n := n) (sc := sc) (pIntC_rel E n) c
    simp only [strAtom, strAtomC]
    revert this
    cases sizeOf E n sc (pInt E n) c <;> cases sizeOfC E n sc (pIntC E n) c <;>
      simp only [ORel, Option.map_none, Option.map_some] <;> try (first | exact id | exact fun h => h.elim)
    rename_i Q Q'
    intro h C hC
    cases P' with
    | none => simp at hC
    | some PC =>
      cases Q' with
      | none => simp at hC
      | some QC =>
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hC
        subst hC
        obtain ⟨h1, h2⟩ := hP PC rfl
        exact ⟨(h QC rfl).within h1.1, DenF.plain h2.1⟩
  | from_ c =>
    simp only [strAtom, strAtomC]
    split
    · simp [ORel]
    · simp only [ORel]
      intro C hC
      cases P' with
      | none => simp at hC
      | some PC =>
        cases hv : fromC E sc pt PC.1.r PC.2.r n c with
        | none => simp [hv] at hC
        | some V =>
          simp only [Option.map_some, hv, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hC
          subst hC
          obtain ⟨h1, h2⟩ := hP PC rfl
          exact ⟨DenF.plain h1.1, fromC_spec h1.1 h2.1 hv⟩
  | contained t x =>
    simp only [strAtom, strAtomC]
    split
    · simp [ORel]
    · simp only [ORel]
      intro C hC
      cases P' with
      | none => simp at hC
      | some PC =>
        cases hq : rec' sc t with
        | none => simp [hq] at hC
        | some Q =>
          simp only [Option.map_some, hq, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hC
          subst hC
          obtain ⟨h1, h2⟩ := hP PC rfl
          obtain ⟨h3, h4⟩ := hrec sc t Q hq
          refine ⟨DenF.plain fun k => ?_, DenF.plain fun k => ?_⟩
          · simp [h1.1 k, h3.1 k]
          · simp [h2.1 k, h4.1 k]
  | _ => simp [strAtom, strAtomC, ORel]

theorem mem_rangeIvs (rs : CharRanges) (c : Nat) : (rangeIvs rs).mem c = rs.mem c := by
  apply Bool.eq_iff_iff.mpr
  simp [rangeIvs, Ivs.mem, Ivs.memI, CharRanges.mem]

theorem pStrC_rel (E : Env) : ∀ n sc t, RS (pStr E n sc t) (pStrC E n sc t) := by
  unfold pStr pStrC
  apply view_rel RS E
  · intro C hC; cases hC; exact ⟨DenF.empty, DenF.empty⟩
  · intro sc t
    cases t <;> simp only [Option.getD_none, Option.getD_some] <;>
      try (intro C hC; cases hC; exact ⟨DenF.empty, DenF.empty⟩)
    rename_i k
    split
    · intro C hC; cases hC
      exact ⟨DenF.plain fun i => by simp, DenF.plain fun c => by simp [mem_rangeIvs]⟩
    · intro C hC; cases hC; exact ⟨DenF.empty, DenF.empty⟩
  · intro P P' h C hC
    cases P' with
    | none => cases hC
    | some PC => cases hC; obtain ⟨h1, h2⟩ := h PC rfl; exact ⟨h1.rootOnly, h2.rootOnly⟩
  · intro n sc t P P' rec rec' c hP hrec
    split
    · simp [ORel]
    · obtain ⟨hu, hi, hall, ho, hos⟩ := pairAlg_rel hP
      exact evalC_rel RS _ _ hu hi hall ho hos _ _ (strAtom_rel hP hrec) c

theorem pStrC_sound {E : Env} {n : Nat} {sc : Scope} {t : Ty} {P : CSet × CSet}
    (h : pStrC E n sc t = some P) : DenN P.1 (pStr E n sc t).1 ∧ DenN P.2 (pStr E n sc t).2 :=
  pStrC_rel E n sc t P h

theorem dedupAdj_eq : ∀ l : List Nat, l.Pairwise (· ≤ ·) → dedupAdj l = l.eraseDups
  | [], _ => rfl
  | [a], _ => by simp [dedupAdj, List.eraseDups_cons]
  | a :: b :: l, h => by
    have hb : (b :: l).Pairwise (· ≤ ·) := h.of_cons
    have ih := dedupAdj_eq (b :: l) hb
    rw [List.eraseDups_cons]
    by_cases e : a = b
    · subst e
      simp only [dedupAdj, ↓reduceIte, ih, List.eraseDups_cons]
      simp
    · have hlt : a < b := lt_of_le_of_ne (List.rel_of_pairwise_cons h (by simp)) e
      have hf : (b :: l).filter (fun x => !x == a) = b :: l := by
        rw [List.filter_eq_self]; intro x hx
        have hbx : b ≤ x := by
          rcases List.mem_cons.mp hx with h1 | h1
          · omega
          · exact List.rel_of_pairwise_cons hb h1
        have : x ≠ a := by omega
        simpa using this
      simp only [dedupAdj, e, ↓reduceIte, ih, hf]

theorem effAlphabet_eq {k : StrType} {A : CSet} {P : PSet Nat} (h : DenN A P) :
    effAlphabet k P = effAlphabetC k A := by
  unfold effAlphabet effAlphabetC
  rw [dedupAdj_eq _ ((List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) _).imp (by simp))]
  rw [h.2.2]
  split
  · rfl
  · simp only [Ivs.filterNat]
    congr 1
    funext c
    exact Bool.eq_iff_iff.mpr (by simpa using h.1 c)

end Asn1.X691
