import Asn1.X691.DecodeLemmas
import Asn1.X691.ViewCSound

/-!
# The PER decoder is sound

`pdec_sound`: what `pdec` returns, `per` relates; `decode_sound`: the octets `decode` accepts are the
complete encoding (11.1) of a field-list that `per` relates to the value returned.

The decoder's control flow is walked with `OkP m P` ("every result `m` returns satisfies `P`"):
reads whose results need no property are passed over, throws are vacuous, and each case of `pdecB`
ends in a `pure` of a value and a field-list built with the functions `perB` names, which the
lemmas below relate to `perB`'s case with the computed view (`ViewCSound.lean`).
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (DFrame)

/-! ## Results of the decoder's computations -/

/-- Every result of `m` satisfies `P`. -/
def OkP {α : Type} (m : PM α) (P : α → Prop) : Prop := ∀ r a r', m.run r = .ok (a, r') → P a

theorem OkP.bind {α β : Type} {m : PM α} {f : α → PM β} {Q : α → Prop} {P : β → Prop}
    (hm : OkP m Q) (hf : ∀ a, Q a → OkP (f a) P) : OkP (m >>= f) P := by
  intro r b r' h
  simp only [StateT.run_bind] at h
  cases hx : m.run r with
  | error e => rw [hx] at h; cases h
  | ok p =>
    rw [hx] at h
    exact hf p.1 (hm r p.1 p.2 hx) p.2 b r' h

theorem OkP.pure {α : Type} {a : α} {P : α → Prop} (h : P a) : OkP (Pure.pure a) P := by
  intro r b r' hr
  simp only [StateT.run_pure] at hr
  cases hr; exact h

theorem OkP.throw {α : Type} {e : String} {P : α → Prop} : OkP (throw e : PM α) P := by
  intro r b r' h; cases h

theorem OkP.pure_bind {α β : Type} {a : α} {f : α → PM β} {P : β → Prop} (h : OkP (f a) P) :
    OkP ((Pure.pure a : PM α) >>= f) P := by simpa using h

theorem OkP.pure_unit : OkP (Pure.pure () : PM Unit) (fun _ => True) := OkP.pure trivial

theorem OkP.any {α : Type} (m : PM α) : OkP m (fun _ => True) := fun _ _ _ _ => trivial

theorem OkP.mono {α : Type} {m : PM α} {P Q : α → Prop} (h : OkP m P) (hpq : ∀ a, P a → Q a) :
    OkP m Q := fun r a r' hr => hpq a (h r a r' hr)

/-- Walk a decoder's control flow: binds whose result needs no property, `pure` binds, throws and
branches. Stops at a final `pure`, and at binds that need a property of their result. -/
macro "okp" : tactic => `(tactic| repeat' (first
  | exact OkP.throw
  | (with_reducible refine OkP.bind OkP.throw ?_; intro _ h; exact h.elim)
  | (with_reducible apply OkP.pure_bind)
  | split
  | (with_reducible refine OkP.bind (OkP.any _) ?_; intro _ _)))

/-- The induction hypothesis: what `rec` returns, `per` relates, at one less fuel. -/
abbrev RecOk (E : Env) (v : Variant) (n : Nat) (rec : List DFrame → Scope → Ty → PM (Val × FieldList)) :
    Prop := ∀ frames sc t, OkP (rec frames sc t) (fun p => per E v n sc t p.1 p.2)

theorem mapM_rec_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) {frames : List DFrame} {sc : Scope} {t : Ty} {k : Nat} :
    OkP ((List.replicate k ()).mapM fun _ => rec frames sc t)
      (fun xs => ∀ p ∈ xs, per E v n sc t p.1 p.2) := by
  induction k with
  | zero => simp only [List.replicate, List.mapM_nil]; exact OkP.pure (by simp)
  | succ k ihk =>
    simp only [List.replicate, List.mapM_cons]
    refine OkP.bind (ih _ _ _) fun a ha => OkP.bind ihk fun as has => OkP.pure ?_
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ha
    · exact has p hp

theorem lenDetR_rec_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) {frames : List DFrame} {sc : Scope} {t : Ty} {kind : LenKind} {al : Bool}
    {fuel : Nat} :
    OkP (lenDetR v kind (fun _ k => (List.replicate k ()).mapM fun _ => rec frames sc t) al fuel)
      (fun xs => ∀ p ∈ xs, per E v n sc t p.1 p.2) := by
  intro r xs r' h
  exact lenDetR_mem (P := fun p => per E v n sc t p.1 p.2) (fun _ _ r as r' h => mapM_rec_ok ih r as r' h) h

/-- `okp`, and binds of the recursive decoder, whose results `ih` describes. -/
macro "okpr " ih:term : tactic => `(tactic| repeat' (first
  | exact OkP.throw
  | (with_reducible refine OkP.bind OkP.throw ?_; intro _ h; exact h.elim)
  | (with_reducible apply OkP.pure_bind)
  | (with_reducible refine OkP.bind ($ih _ _ _) ?_; intro _ _)
  | (with_reducible refine OkP.bind (mapM_rec_ok $ih) ?_; intro _ _)
  | (with_reducible refine OkP.bind (lenDetR_rec_ok $ih) ?_; intro _ _)
  | split
  | dsimp only
  | simp only [↓reduceIte]
  | (with_reducible refine OkP.bind (OkP.any _) ?_; intro _ _)))

theorem runInner_ok {α : Type} {m : PM α} {P : α → Prop} {bs : Bits} {a : α} (hm : OkP m P)
    (h : runInner m bs = .ok a) : P a := by
  unfold runInner at h
  cases hr : m.run ⟨0, bs⟩ with
  | error e => rw [hr] at h; cases h
  | ok p => rw [hr] at h; cases h; exact hm _ _ _ hr

theorem rec_inner {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) {frames : List DFrame} {sc : Scope} {t : Ty} {bs : Bits} {y : Val} {afl : FieldList}
    (h : runInner (rec frames sc t) bs = .ok (y, afl)) : per E v n sc t y afl :=
  runInner_ok (P := fun p => per E v n sc t p.1 p.2) (ih frames sc t) h

/-! ## INTEGER (13) -/

theorem intRootFieldsC_eq {v : Variant} {P : PSet Int} {C : CSet} (h : Den C P) (i : Int) :
    intRootFieldsC v C.r i = intRootFields v P.r i := by
  unfold intRootFieldsC intRootFields
  rw [least?_eq h.1, greatest?_eq h.1]
  cases C.r.least? <;> cases C.r.greatest? <;> rfl

theorem int_ok {E : Env} {v : Variant} {n : Nat} {sc sc' : Scope} {t : Ty} {z : List (String × Int)}
    {C : CSet} {i : Int} (hC : pIntC E n sc t = some C) (ha : C.a.mem i = true)
    (hr : C.ext = false → C.r.mem i = true) :
    perB E v n (per E v n) sc t sc' (.integer z) (.int i) (intFl v C i) := by
  have hD := pIntC_sound hC
  simp only [perB, IntFields]
  refine ⟨(hD.2.1 i).2 ha, ?_⟩
  rw [hD.2.2]
  unfold intFl
  rw [intRootFieldsC_eq hD]
  cases hx : C.ext
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨(hD.1 i).2 (hr hx), trivial⟩
  · simp only [↓reduceIte]
    cases hm : C.r.mem i
    · right; exact ⟨fun h => by simp [(hD.1 i).1 h] at hm, by simp⟩
    · left; exact ⟨(hD.1 i).2 hm, by simp⟩

theorem pdecB_integer (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' z :
    OkP (pdecB E v n rec frames hint sc t sc' (.integer z))
      (fun p => perB E v n (per E v n) sc t sc' (.integer z) p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; apply int_ok ‹_› <;> simp_all)

/-! ## Sized types (16, 17, 20, 30) -/

theorem lbOf_eq {S : CSet} {P : PSet Nat} (hD : DenN S P) : (natLeast? P.r).getD 0 = lbOf S := by
  unfold lbOf; rw [natLeast?_eq hD.1]

theorem ubOf_eq {S : CSet} {P : PSet Nat} (hD : DenN S P) : natGreatest? P.r = ubOf S := by
  unfold ubOf; rw [natGreatest?_eq hD.1]

theorem sized_ok {S : CSet} {P : PSet Nat} (hD : DenN S P) {len : Nat} (rootF extF : FieldList)
    (ha : S.a.mem len = true) (hr : S.ext = false → S.r.mem len = true) :
    P.a len ∧ (if P.ext then (P.r len ∧ sizedFl S len rootF extF = .unaligned [false] :: rootF) ∨
      (¬ P.r len ∧ sizedFl S len rootF extF = .unaligned [true] :: extF)
    else P.r len ∧ sizedFl S len rootF extF = rootF) := by
  refine ⟨(hD.2.1 len).2 ha, ?_⟩
  rw [hD.2.2]
  unfold sizedFl
  cases hx : S.ext
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨(hD.1 len).2 (hr hx), trivial⟩
  · simp only [↓reduceIte]
    cases hm : S.r.mem len
    · right; exact ⟨fun h => by simp [(hD.1 len).1 h] at hm, by simp⟩
    · left; exact ⟨(hD.1 len).2 hm, by simp⟩

theorem bits_ok {E : Env} {v : Variant} {n : Nat} {sc sc' : Scope} {t : Ty} {named : List (String × Nat)}
    {S : CSet} {bs : Bits} (hS : pSizeC E n sc t = some S) (ha : S.a.mem bs.length = true)
    (hr : S.ext = false → S.r.mem bs.length = true)
    (hn : named ≠ [] → ∀ k, k < bs.length → (stripTrailingZeros bs).length ≤ k → S.a.mem k = false) :
    perB E v n (per E v n) sc t sc' (.bitString named) (.bits bs)
      (sizedFl S bs.length (bitsRootFields v (lbOf S) (ubOf S) bs) (bitsRootFields v 0 none bs)) := by
  have hD := pSizeC_sound hS
  simp only [perB]
  refine ⟨bs, ?_, ?_⟩
  · split
    · rfl
    · rename_i hne
      exact namedBitsSent_self _ bs ((hD.2.1 _).2 ha) fun k hk hc hP => by
        have := hn hne k hk hc; rw [(hD.2.1 k).1 hP] at this; cases this
  · simp only [BitsFields]
    rw [lbOf_eq hD, ubOf_eq hD]
    exact sized_ok hD _ _ ha hr

theorem octets_ok {E : Env} {v : Variant} {n : Nat} {sc sc' : Scope} {t : Ty}
    {S : CSet} {os : Octets} (hS : pSizeC E n sc t = some S) (ha : S.a.mem os.length = true)
    (hr : S.ext = false → S.r.mem os.length = true) :
    perB E v n (per E v n) sc t sc' .octetString (.octets os)
      (sizedFl S os.length (octetsRootFields v (lbOf S) (ubOf S) os) (octetsRootFields v 0 none os)) := by
  have hD := pSizeC_sound hS
  simp only [perB, OctetsFields]
  rw [lbOf_eq hD, ubOf_eq hD]
  exact sized_ok hD _ _ ha hr

theorem km_core {v : Variant} {k : StrType} {S A : CSet} {P : PSet Nat × PSet Nat} {cs : List Nat}
    (hD1 : DenN S P.1) (hD2 : DenN A P.2) (hc : ∀ c ∈ cs, c ∈ effAlphabetC k A)
    (ha : S.a.mem cs.length = true) (hr : S.ext = false → S.r.mem cs.length = true) :
    KmFields v k P cs (sizedFl S cs.length (kmBody v (effAlphabetC k A) (lbOf S) (ubOf S) cs)
        (kmBody v (effAlphabetC k A) 0 none cs)) := by
  simp only [KmFields]
  rw [effAlphabet_eq hD2, lbOf_eq hD1, ubOf_eq hD1]
  exact ⟨hc, sized_ok hD1 _ _ ha hr⟩

theorem km_ok {E : Env} {v : Variant} {n : Nat} {sc sc' : Scope} {t : Ty} {k : StrType}
    {S A : CSet} {cs : List Nat} (hk : k.knownMultiplier = true) (hS : pStrC E n sc t = some (S, A))
    (hc : ∀ c ∈ cs, c ∈ effAlphabetC k A)
    (ha : S.a.mem cs.length = true) (hr : S.ext = false → S.r.mem cs.length = true) :
    perB E v n (per E v n) sc t sc' (.restricted k) (.chars cs)
      (sizedFl S cs.length (kmBody v (effAlphabetC k A) (lbOf S) (ubOf S) cs)
        (kmBody v (effAlphabetC k A) 0 none cs)) := by
  have hD := pStrC_sound hS
  simp only [perB, hk, ↓reduceIte]
  exact ⟨cs, rfl, km_core hD.1 hD.2 hc ha hr⟩

theorem mem_rangeIvs' (rs : CharRanges) (c : Nat) : (rangeIvs rs).mem (c : Int) = rs.mem c := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    obtain ⟨lo, hi⟩ := p
    have : (rangeIvs ((lo, hi) :: rs)) = [(some (lo : Int), some (hi : Int))] ++ rangeIvs rs := rfl
    rw [this, Ivs.mem_append, ih]
    simp [Ivs.mem, Ivs.memI, CharRanges.mem]

theorem denN_univ : DenN CSet.univ PSet.univ := by
  refine ⟨fun k => ?_, fun k => ?_, rfl⟩ <;> simp [CSet.univ, CSet.plain, PSet.univ, PSet.plain]

theorem denN_visible : DenN (CSet.plain (rangeIvs visibleChars)) (PSet.plain fun c => visibleChars.mem c) := by
  refine ⟨fun k => ?_, fun k => ?_, rfl⟩ <;> simp [CSet.plain, PSet.plain, mem_rangeIvs']

theorem time_ok {v : Variant} {canon : List Char → Prop} {cs : List Nat} (hcanon : canon (cs.map Char.ofNat))
    (hc : ∀ c ∈ cs, c ∈ effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))) :
    UsefulTimeFields v canon (.chars cs)
      (sizedFl CSet.univ cs.length
          (kmBody v (effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))) (lbOf CSet.univ)
            (ubOf CSet.univ) cs)
          (kmBody v (effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))) 0 none cs)) :=
  ⟨cs, rfl, hcanon, km_core denN_univ denN_visible hc (by simp [CSet.univ, CSet.plain])
    (fun _ => by simp [CSet.univ, CSet.plain])⟩

theorem pdecB_bitString (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' named :
    OkP (pdecB E v n rec frames hint sc t sc' (.bitString named))
      (fun p => perB E v n (per E v n) sc t sc' (.bitString named) p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; apply bits_ok ‹_›)
  all_goals first
    | (intro _; exact range_all_of ‹_›)
    | (intro h; simp_all)
    | simp_all

theorem pdecB_octetString (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .octetString)
      (fun p => perB E v n (per E v n) sc t sc' .octetString p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; apply octets_ok ‹_›)
  all_goals first
    | (intro h; simp_all)
    | simp_all

theorem pdecB_boolean (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .boolean)
      (fun p => perB E v n (per E v n) sc t sc' .boolean p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp [perB])

theorem pdecB_null (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .null)
      (fun p => perB E v n (per E v n) sc t sc' .null p.1 p.2) := by
  simp only [pdecB]
  apply OkP.pure; simp [perB]

theorem pdecB_real (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .real)
      (fun p => perB E v n (per E v n) sc t sc' .real p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp only [perB]; exact ⟨_, X690.decReal_spec ‹_›, rfl⟩)

theorem pdecB_oid (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .objectIdentifier)
      (fun p => perB E v n (per E v n) sc t sc' .objectIdentifier p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp [perB])

theorem pdecB_relOid (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .relativeOid)
      (fun p => perB E v n (per E v n) sc t sc' .relativeOid p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp [perB])

theorem pdecB_oidIri (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .oidIri)
      (fun p => perB E v n (per E v n) sc t sc' .oidIri p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp [perB])

theorem pdecB_relOidIri (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .relativeOidIri)
      (fun p => perB E v n (per E v n) sc t sc' .relativeOidIri p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp [perB])

theorem other_ok {v : Variant} {p : X690.Profile} {k : StrType} {os : Octets} {x : Val}
    (h : X690.decString p k os = .ok x) (hp : p = if v.canonical then .der else .ber) :
    OtherStringFields v k x (unconstrainedLength (.field true (octetUnits os))) :=
  ⟨os, hp ▸ X690.decString_spec h, rfl⟩

theorem pdecB_restricted (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' k :
    OkP (pdecB E v n rec frames hint sc t sc' (.restricted k))
      (fun p => perB E v n (per E v n) sc t sc' (.restricted k) p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals apply OkP.pure
  all_goals first
    | (simp only [perB, ‹k.knownMultiplier = true›, ↓reduceIte]; exact absurd ‹k.knownMultiplier = true› ‹_›)
    | (apply km_ok ‹_› ‹_› <;> first
        | (intro c hc; have := ‹¬(!_ : Bool) = true›; simp_all)
        | (intro h; simp_all)
        | simp_all)
    | (simp only [perB, ‹¬k.knownMultiplier = true›, Bool.false_eq_true, ↓reduceIte]
       exact other_ok ‹_› (by simp_all))

theorem pdecB_objectDescriptor (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .objectDescriptor)
      (fun p => perB E v n (per E v n) sc t sc' .objectDescriptor p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals (apply OkP.pure; simp only [perB]; exact other_ok ‹_› (by simp_all))

theorem pdecB_enumerated (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' root ext :
    OkP (pdecB E v n rec frames hint sc t sc' (.enumerated root ext))
      (fun p => perB E v n (per E v n) sc t sc' (.enumerated root ext) p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals apply OkP.pure
  all_goals (simp only [perB, EnumFields]; simp_all)

theorem pdecB_genTime (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .generalizedTime)
      (fun p => perB E v n (per E v n) sc t sc' .generalizedTime p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals apply OkP.pure
  all_goals first
    | exact absurd trivial ‹¬True›
    | (simp only [perB]; exact time_ok (X690.genTimeCanonB_spec (by simpa using ‹¬(!_ : Bool) = true›))
        (by intro c hc; simp_all))

theorem pdecB_utcTime (E : Env) (v : Variant) (n : Nat) rec frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .utcTime)
      (fun p => perB E v n (per E v n) sc t sc' .utcTime p.1 p.2) := by
  simp only [pdecB]
  okp
  all_goals apply OkP.pure
  all_goals first
    | exact absurd trivial ‹¬True›
    | exact absurd ‹false = true› (by simp)
    | (simp only [perB]; exact time_ok (X690.utcTimeCanonB_spec (by simpa using ‹¬(!_ : Bool) = true›))
        (by intro c hc; simp_all))

theorem pdecB_openType (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' :
    OkP (pdecB E v n rec frames hint sc t sc' .openType)
      (fun p => perB E v n (per E v n) sc t sc' .openType p.1 p.2) := by
  simp only [pdecB]
  okpr ih
  all_goals apply OkP.pure
  all_goals (simp only [perB]; exact ⟨_, _, rec_inner ih ‹_›, rfl⟩)

theorem choice_root {R : Ty → Val → FieldList → Prop} {S A : List (Alt × Option (List Tag))} {v : Variant}
    {isExt : Bool} {k : Nat} {a : Alt} {tg : Option (List Tag)} {y : Val} {afl fl : FieldList}
    (hk : S[k]? = some (a, tg)) (hi : ¬(List.idxOf? a.name (S.map (·.1.name)) != some k) = true)
    (hr : R a.ty y afl)
    (hfl : fl = if isExt then .unaligned [false] :: (constrainedInt v 0 ↑(S.length - 1) ↑k ++ afl)
      else constrainedInt v 0 ↑(S.length - 1) ↑k ++ afl) :
    ∃ a' afl', R a'.ty y afl' ∧
      ((∃ k', (S.map (·.1.name)).idxOf? a.name = some k' ∧ S[k']?.map (·.1) = some a' ∧
          ChoiceFields v isExt S.length (.inl k') afl' fl) ∨
       (∃ k', (A.map (·.1.name)).idxOf? a.name = some k' ∧ A[k']?.map (·.1) = some a' ∧
          ChoiceFields v isExt S.length (.inr k') afl' fl)) := by
  refine ⟨a, afl, hr, Or.inl ⟨k, by simpa using hi, by simp [hk], ?_⟩⟩
  simp only [ChoiceFields]; exact hfl

theorem choice_add {R : Ty → Val → FieldList → Prop} {S A : List (Alt × Option (List Tag))} {v : Variant}
    {isExt : Bool} {k : Nat} {a : Alt} {tg : Option (List Tag)} {y : Val} {afl : FieldList}
    (hk : A[k]? = some (a, tg)) (hi : ¬(List.idxOf? a.name (A.map (·.1.name)) != some k) = true)
    (hr : R a.ty y afl) (hx : isExt = true) :
    ∃ a' afl', R a'.ty y afl' ∧
      ((∃ k', (S.map (·.1.name)).idxOf? a.name = some k' ∧ S[k']?.map (·.1) = some a' ∧
          ChoiceFields v isExt S.length (.inl k') afl' (.unaligned [true] :: normallySmall k ++ openField v afl)) ∨
       (∃ k', (A.map (·.1.name)).idxOf? a.name = some k' ∧ A[k']?.map (·.1) = some a' ∧
          ChoiceFields v isExt S.length (.inr k') afl' (.unaligned [true] :: normallySmall k ++ openField v afl))) := by
  refine ⟨a, afl, hr, Or.inr ⟨k, by simpa using hi, by simp [hk], ?_⟩⟩
  simp [ChoiceFields, hx]

theorem pdecB_choice (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' root ext :
    OkP (pdecB E v n rec frames hint sc t sc' (.choice root ext))
      (fun p => perB E v n (per E v n) sc t sc' (.choice root ext) p.1 p.2) := by
  simp only [pdecB]
  okpr ih
  all_goals apply OkP.pure
  all_goals simp only [perB]
  all_goals first
    | (simp only [‹autoChoice _ _ _ = true›, ↓reduceIte])
    | (simp only [‹¬autoChoice _ _ _ = true›, Bool.false_eq_true, ↓reduceIte])
  all_goals first
    | (apply choice_root ‹_› ‹_› ‹_›; simp_all)
    | (apply choice_add ‹_› ‹_› (rec_inner ih ‹_›); simp_all)

theorem forall₂_map_of {α β γ : Type} {R : α → β → Prop} {xs : List γ} {f : γ → α} {g : γ → β}
    (h : ∀ p ∈ xs, R (f p) (g p)) : List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons p xs ih => exact .cons (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

theorem seqOfFields_ok {v : Variant} {S : CSet} {P : PSet Nat} (hD : DenN S P) {fls : List FieldList}
    (ha : S.a.mem fls.length = true) (hr : S.ext = false → S.r.mem fls.length = true) :
    SeqOfFields v P fls (seqOfFl v S fls) := by
  simp only [SeqOfFields, seqOfFl]
  rw [lbOf_eq hD, ubOf_eq hD]
  exact sized_ok hD _ _ ha hr

theorem pdecB_sequenceOf (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' el :
    OkP (pdecB E v n rec frames hint sc t sc' (.sequenceOf el))
      (fun p => perB E v n (per E v n) sc t sc' (.sequenceOf el) p.1 p.2) := by
  simp only [pdecB]
  okpr ih
  all_goals apply OkP.pure
  all_goals try exact absurd ‹false = true› Bool.false_ne_true
  all_goals try exact absurd trivial ‹¬True›
  all_goals (simp only [perB]; refine ⟨_, forall₂_map_of ‹_›, seqOfFields_ok (pSizeC_sound ‹_›) ?_ ?_⟩)
  all_goals first
    | (intro h; simp_all)
    | simp_all

theorem guard_imp {c : Bool} {P : Prop} [Decidable P] (h : ¬(c && !decide P) = true) : c = true → P := by
  intro hc; simp_all

theorem pdecB_setOf (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' el :
    OkP (pdecB E v n rec frames hint sc t sc' (.setOf el))
      (fun p => perB E v n (per E v n) sc t sc' (.setOf el) p.1 p.2) := by
  simp only [pdecB]
  okpr ih
  all_goals apply OkP.pure
  all_goals try exact absurd ‹false = true› Bool.false_ne_true
  all_goals try exact absurd trivial ‹¬True›
  all_goals (simp only [perB]; refine ⟨_, _, List.Perm.refl _, forall₂_map_of ‹_›, ?_,
    seqOfFields_ok (pSizeC_sound ‹_›) ?_ ?_⟩)
  all_goals try exact absurd rfl ‹¬true = true›
  all_goals first
    | exact guard_imp ‹_›
    | (intro h; simp_all)
    | simp_all

/-! ## SEQUENCE and SET (19, 21) -/

/-- The names of the entries that are present. -/
def presKeys (L : List (Entry × Option FieldList)) : List String :=
  L.filterMap fun p => p.2.map fun _ => p.1.name

/-- What the decoder established about one entry and its outcome, among the components `cs`. -/
def RawOk (E : Env) (v : Variant) (n : Nat) (root : Bool) (cs : List (String × Val))
    (p : Entry × Option FieldList) : Prop :=
  match p.2 with
  | some f => ∃ x, (p.1.name, x) ∈ cs ∧ per E v n p.1.scope p.1.ty x f ∧ presentOkB E v n p.1 x = true
  | none => absentOkB E n root p.1 = true

theorem RawOk.mono {E : Env} {v : Variant} {n : Nat} {root : Bool} {cs cs' : List (String × Val)}
    {p : Entry × Option FieldList} (h : RawOk E v n root cs p) (hs : ∀ q ∈ cs, q ∈ cs') :
    RawOk E v n root cs' p := by
  unfold RawOk at *
  split at h
  · obtain ⟨x, hm, hp, hok⟩ := h; exact ⟨x, hs _ hm, hp, hok⟩
  · exact h

theorem compsR_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) (frames : List DFrame) (all : List (String × Scope × Ty)) (root : Bool) :
    ∀ (es : List Entry) (pre : Bits) (acc : List (String × Val)),
    OkP (compsR E v n rec frames all root es pre acc) (fun r => r.2.length = es.length ∧
      ∃ new, r.1 = acc ++ new ∧ new.map (·.1) = presKeys (es.zip r.2) ∧
        ∀ p ∈ es.zip r.2, RawOk E v n root r.1 p)
  | [], pre, acc => by
    simp only [compsR]
    exact OkP.pure ⟨rfl, [], by simp, by simp [presKeys], by simp⟩
  | en :: es, pre, acc => by
    unfold compsR
    generalize (if en.presence.isMandatory = true then (true, pre) else (List.headD pre false, List.tail pre)) = q
    obtain ⟨present, pre'⟩ := q
    dsimp only
    split
    · refine OkP.bind (ih _ _ _) fun ⟨x, f⟩ hx => ?_
      dsimp only
      split
      · exact OkP.bind OkP.throw fun _ h => False.elim h
      rename_i hok
      refine OkP.bind (compsR_ok ih frames all root es pre' _) fun ⟨cs, outs⟩ ⟨hlen, new, hcs, hkeys, hraw⟩ => ?_
      simp only at hcs hlen hkeys hraw hx ⊢
      refine OkP.pure ⟨by simp [hlen], (en.name, x) :: new, by simp [hcs], ?_, ?_⟩
      · simp only [List.zip_cons_cons, presKeys, List.filterMap_cons, Option.map_some, List.map_cons]
        exact congrArg _ hkeys
      · intro p hp
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨x, by simp [hcs], hx, by simpa using hok⟩
        · exact hraw p hp
    · split
      · exact OkP.bind OkP.throw fun _ h => False.elim h
      rename_i hok
      refine OkP.bind (compsR_ok ih frames all root es pre' _) fun ⟨cs, outs⟩ ⟨hlen, new, hcs, hkeys, hraw⟩ => ?_
      simp only at hcs hlen hkeys hraw ⊢
      refine OkP.pure ⟨by simp [hlen], new, hcs, ?_, ?_⟩
      · simp only [List.zip_cons_cons, presKeys, List.filterMap_cons, Option.map_none]
        exact hkeys
      · intro p hp
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · show absentOkB E n root en = true
          simpa using hok
        · exact hraw p hp

theorem bnot_false {b : Bool} (h : ¬(!b) = true) : b = true := by simpa using h

/-- What an extension addition `a` came to: its outcome `o`, and its entries with theirs (`La`). -/
def AddRel (v : Variant) (a : List Entry × Bool) (o : Option FieldList) (La : List (Entry × Option FieldList)) :
    Prop :=
  La.map (·.1) = a.1 ∧
  if a.2 then
    (if (La.map (·.2)).all Option.isNone then o = none
     else (∀ p ∈ a.1.zip (La.map (·.2)), p.1.presence.isMandatory → p.2.isSome) ∧
       o = some (seqRootFields v a.1 (La.map (·.2))))
  else ∃ e, a.1 = [e] ∧ La = [(e, o)]

theorem addStep_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) (frames : List DFrame) (all : List (String × Scope × Ty))
    (cs : List (String × Val)) (outs : List (Option FieldList)) (es : List Entry) (grp p : Bool)
    (hshape : grp = true ∨ es.length = 1) :
    OkP (addStep E v n rec frames all (cs, outs) ((es, grp), p)) (fun r =>
      ∃ more o La, r.1 = cs ++ more ∧ r.2 = outs ++ [o] ∧ AddRel v (es, grp) o La ∧
        more.map (·.1) = presKeys La ∧ ∀ q ∈ La, RawOk E v n false r.1 q) := by
  unfold addStep
  dsimp only
  okp
  · -- absent
    rename_i hok
    refine OkP.pure ⟨[], none, es.map fun e => (e, none), by simp, rfl,
      ⟨by simp [List.map_map, Function.comp_def], ?_⟩, ?_, ?_⟩
    · split
      · simp
      · rename_i hg
        rcases hshape with h | h
        · exact absurd h hg
        · match es, h with
          | [e], _ => exact ⟨e, rfl, rfl⟩
    · simp [presKeys]
    · intro q hq
      simp only [List.mem_map] at hq
      obtain ⟨e, he, rfl⟩ := hq
      show absentOkB E n false e = true
      exact List.all_eq_true.1 (bnot_false hok) e he
  · -- a group
    rename_i hg _ _ _ cs' f heq _
    have hP := runInner_ok (P := fun (r : List (String × Val) × FieldList) => ∃ gouts new, r.1 = cs ++ new ∧ gouts.length = es.length ∧
        new.map (·.1) = presKeys (es.zip gouts) ∧ (∀ q ∈ es.zip gouts, RawOk E v n false r.1 q) ∧
        ¬ (gouts.all Option.isNone = true) ∧
        (∀ q ∈ es.zip gouts, q.1.presence.isMandatory → q.2.isSome) ∧ r.2 = seqRootFields v es gouts)
      (by
        refine OkP.bind (OkP.any _) fun pre _ => OkP.bind (compsR_ok ih frames all false es pre cs) fun x hx => ?_
        obtain ⟨hlen, new, hcs, hkeys, hraw⟩ := hx
        okp
        all_goals apply OkP.pure
        all_goals refine ⟨x.2, new, hcs, hlen, hkeys, hraw, ‹_›, ?_, rfl⟩
        all_goals intro q hq hm
        all_goals have := List.all_eq_true.1 (bnot_false ‹_›) q hq
        all_goals simp_all) heq
    obtain ⟨gouts, new, hcs, hlen, hkeys, hraw, hne, hman, hf⟩ := hP
    simp only at hcs hraw hf
    refine OkP.pure ⟨new, some f, es.zip gouts, hcs, rfl, ⟨List.map_fst_zip (by omega), ?_⟩, hkeys, hraw⟩
    simp only [hg, ↓reduceIte, List.map_snd_zip (by omega : gouts.length ≤ es.length)]
    simp only [hne, ↓reduceIte]
    exact ⟨hman, by rw [hf]⟩
  · -- one component
    rename_i hg es' e _ _ _ cs' f heq _
    have hP := runInner_ok (P := fun (r : List (String × Val) × FieldList) => ∃ x, r.1 = cs ++ [(e.name, x)] ∧ per E v n e.scope e.ty x r.2 ∧
        presentOkB E v n e x = true)
      (by
        refine OkP.bind (ih _ _ _) fun xf hx => ?_
        okp
        all_goals apply OkP.pure
        all_goals exact ⟨xf.1, rfl, hx, by simpa using ‹¬(!presentOkB E v n e xf.1) = true›⟩) heq
    obtain ⟨x, hcs, hper, hok⟩ := hP
    simp only at hcs hper
    refine OkP.pure ⟨[(e.name, x)], some f, [(e, some f)], hcs, rfl, ⟨rfl, ?_⟩, rfl, ?_⟩
    · simp only [hg, Bool.false_eq_true, ↓reduceIte]; exact ⟨e, rfl, rfl⟩
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨x, by simp [hcs], hper, hok⟩
  · exact absurd ‹Except.error _ = Except.ok _› (by simp)

theorem presKeys_append (L M : List (Entry × Option FieldList)) :
    presKeys (L ++ M) = presKeys L ++ presKeys M := by simp [presKeys]

theorem presKeys_sublist : ∀ (L : List (Entry × Option FieldList)),
    (presKeys L).Sublist (L.map (·.1.name))
  | [] => by simp [presKeys]
  | (e, o) :: L => by
    cases o with
    | none => simpa [presKeys] using (presKeys_sublist L).cons e.name
    | some f => simpa [presKeys] using (presKeys_sublist L).cons_cons e.name

theorem absent_notin : ∀ (L : List (Entry × Option FieldList)) (e : Entry),
    (L.map (·.1.name)).Nodup → (e, none) ∈ L → e.name ∉ presKeys L
  | [], _, _, h => by simp at h
  | (e', o) :: L, e, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at hm
    rcases hm with h | h
    · cases h
      simp only [presKeys, List.filterMap_cons, Option.map_none]
      exact fun hk => hnd.1 ((presKeys_sublist L).subset hk)
    · have ih := absent_notin L e hnd.2 h
      have hne : e.name ≠ e'.name := fun he => hnd.1 (he ▸ List.mem_map.2 ⟨(e, none), h, rfl⟩)
      cases o with
      | none => simpa [presKeys] using ih
      | some f =>
        simp only [presKeys, List.filterMap_cons, Option.map_some, List.mem_cons, not_or]
        exact ⟨hne, ih⟩

theorem lookup_of_mem : ∀ (cs : List (String × Val)) (k : String) (x : Val),
    (cs.map (·.1)).Nodup → (k, x) ∈ cs → cs.lookup k = some x
  | [], _, _, _, h => by simp at h
  | (k', y) :: cs, k, x, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at hm
    rcases hm with h | h
    · cases h; simp [List.lookup]
    · have hne : k ≠ k' := fun he => hnd.1 (he ▸ List.mem_map.2 ⟨(k, x), h, rfl⟩)
      simp only [List.lookup, show (k == k') = false from by simpa using hne]
      exact lookup_of_mem cs k x hnd.2 h

theorem lookup_none : ∀ (cs : List (String × Val)) (k : String), k ∉ cs.map (·.1) → cs.lookup k = none
  | [], _, _ => rfl
  | (k', y) :: cs, k, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup, show (k == k') = false from by simpa using h.1]
    exact lookup_none cs k h.2

theorem compOut_of_raw {E : Env} {v : Variant} {n : Nat} {root : Bool} {cs : List (String × Val)}
    {L : List (Entry × Option FieldList)} (hnd : (L.map (·.1.name)).Nodup)
    (hk : cs.map (·.1) = presKeys L) {q : Entry × Option FieldList} (hq : q ∈ L)
    (h : RawOk E v n root cs q) : CompOut E v n (per E v n) root cs q.1 q.2 := by
  obtain ⟨e, o⟩ := q
  unfold RawOk at h
  cases o with
  | some f =>
    obtain ⟨x, hm, hp, hok⟩ := h
    have hnd' : (cs.map (·.1)).Nodup := hk ▸ (presKeys_sublist L).nodup hnd
    exact presentOkB_compOut hok (lookup_of_mem cs _ x hnd' hm) hp
  | none =>
    exact absentOkB_compOut h (lookup_none cs _ (hk ▸ absent_notin L e hnd hq))

theorem forall₂_of_zip {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, R p.1 p.2) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h => .cons (h (a, b) (by simp)) (forall₂_of_zip (by simpa using hl)
      fun p hp => h p (by simp [hp]))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem flatMap_fst {T : List ((List Entry × Bool) × Option FieldList × List (Entry × Option FieldList))}
    {v : Variant} (hT : ∀ t ∈ T, AddRel v t.1 t.2.1 t.2.2) :
    (T.flatMap (·.2.2)).map (·.1) = (T.map (·.1)).flatMap (·.1) := by
  induction T with
  | nil => rfl
  | cons t T ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons]
    rw [(hT t (by simp)).1, ih fun t' ht' => hT t' (by simp [ht'])]

theorem seq_core {E : Env} {v : Variant} {n : Nat} {rootEs : List Entry} {adds : List (List Entry × Bool)}
    {rootOuts : List (Option FieldList)} {new0 more : List (String × Val)}
    (hnd : ((rootEs ++ adds.flatMap (·.1)).map (·.name)).Nodup)
    (hlen0 : rootOuts.length = rootEs.length) (hk0 : new0.map (·.1) = presKeys (rootEs.zip rootOuts))
    (hr0 : ∀ q ∈ rootEs.zip rootOuts, RawOk E v n true new0 q)
    (T : List ((List Entry × Bool) × Option FieldList × List (Entry × Option FieldList)))
    (hT1 : T.map (·.1) = adds) (hT2 : ∀ t ∈ T, AddRel v t.1 t.2.1 t.2.2)
    (hk1 : more.map (·.1) = presKeys (T.flatMap (·.2.2)))
    (hr1 : ∀ q ∈ T.flatMap (·.2.2), RawOk E v n false (new0 ++ more) q) :
    (∀ p ∈ new0 ++ more, p.1 ∈ (rootEs ++ adds.flatMap (·.1)).map (·.name)) ∧
    List.Forall₂ (CompOut E v n (per E v n) true (new0 ++ more)) rootEs rootOuts ∧
    List.Forall₂ (fun (a : List Entry × Bool) (o : Option FieldList) =>
      if a.2 then GroupOut E v n (per E v n) (new0 ++ more) a.1 o
      else ∃ e, a.1 = [e] ∧ CompOut E v n (per E v n) false (new0 ++ more) e o) adds (T.map (·.2.1)) := by
  set L := rootEs.zip rootOuts ++ T.flatMap (·.2.2) with hL
  have hLn : L.map (·.1.name) = (rootEs ++ adds.flatMap (·.1)).map (·.name) := by
    have h1 : (rootEs.zip rootOuts).map (·.1) = rootEs := List.map_fst_zip (by omega)
    have h2 := flatMap_fst hT2
    rw [hT1] at h2
    have : L.map (·.1.name) = (L.map (·.1)).map (·.name) := by simp [List.map_map, Function.comp_def]
    rw [this, hL, List.map_append, h1, h2]
  have hndL : (L.map (·.1.name)).Nodup := hLn ▸ hnd
  have hkL : (new0 ++ more).map (·.1) = presKeys L := by
    rw [List.map_append, hk0, hk1, hL, presKeys_append]
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · have : p.1 ∈ presKeys L := hkL ▸ List.mem_map.2 ⟨p, hp, rfl⟩
    exact hLn ▸ (presKeys_sublist L).subset this
  · refine forall₂_of_zip hlen0.symm fun q hq => ?_
    exact compOut_of_raw hndL hkL (List.mem_append_left _ hq)
      (RawOk.mono (hr0 q hq) fun r hr => List.mem_append_left _ hr)
  · subst hT1
    refine forall₂_map_of fun t ht => ?_
    have hc : ∀ q ∈ t.2.2, CompOut E v n (per E v n) false (new0 ++ more) q.1 q.2 := fun q hq =>
      compOut_of_raw hndL hkL (List.mem_append_right _ (List.mem_flatMap.2 ⟨t, ht, hq⟩))
        (hr1 q (List.mem_flatMap.2 ⟨t, ht, hq⟩))
    obtain ⟨hf, hrel⟩ := hT2 t ht
    split
    · rename_i hg
      simp only [hg, ↓reduceIte] at hrel
      refine ⟨t.2.2.map (·.2), ?_, ?_⟩
      · rw [← hf]; exact forall₂_map_of hc
      · exact hrel
    · rename_i hg
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at hrel
      obtain ⟨e, he, hLa⟩ := hrel
      refine ⟨e, he, ?_⟩
      exact hc (e, t.2.1) (by rw [hLa]; simp)

theorem foldlM_okp {α β : Type} {f : β → α → PM β} {I : List α → β → Prop} :
    ∀ (l pre : List α) (b : β), (∀ pre b a, a ∈ l → I pre b → OkP (f b a) (I (pre ++ [a]))) →
      I pre b → OkP (l.foldlM f b) (I (pre ++ l))
  | [], pre, b, _, h => by simpa using OkP.pure (P := I pre) h
  | a :: l, pre, b, hf, h => by
    simp only [List.foldlM_cons]
    refine OkP.bind (hf pre b a (by simp) h) fun b' hb' => ?_
    have := foldlM_okp l (pre ++ [a]) b' (fun pre b a' ha => hf pre b a' (by simp [ha])) hb'
    simpa using this

/-- After the additions `l`, from the components `cs0`. -/
def FoldI (E : Env) (v : Variant) (n : Nat) (cs0 : List (String × Val))
    (l : List ((List Entry × Bool) × Bool)) (r : List (String × Val) × List (Option FieldList)) : Prop :=
  ∃ (more : List (String × Val)) (T : List ((List Entry × Bool) × Option FieldList × List (Entry × Option FieldList))),
    r.1 = cs0 ++ more ∧ T.map (·.1) = l.map (·.1) ∧ r.2 = T.map (·.2.1) ∧
    (∀ t ∈ T, AddRel v t.1 t.2.1 t.2.2) ∧ more.map (·.1) = presKeys (T.flatMap (·.2.2)) ∧
    ∀ q ∈ T.flatMap (·.2.2), RawOk E v n false r.1 q

theorem fold_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) (frames : List DFrame) (all : List (String × Scope × Ty))
    (l : List ((List Entry × Bool) × Bool)) (cs0 : List (String × Val)) :
    OkP (l.foldlM (addStep E v n rec frames all) (cs0, []))
      (fun r => (∀ a ∈ l, a.1.2 = true ∨ a.1.1.length = 1) → FoldI E v n cs0 l r) := by
  have := foldlM_okp (f := addStep E v n rec frames all)
    (I := fun pre r => (∀ a ∈ l, a.1.2 = true ∨ a.1.1.length = 1) → FoldI E v n cs0 pre r) l [] (cs0, [])
    (fun pre b a ha hI => by
      obtain ⟨cs, outs⟩ := b
      obtain ⟨⟨es, grp⟩, p⟩ := a
      intro r a' r' hr hsh
      obtain ⟨more, T, hcs, hT1, hT2, hT3, hk, hraw⟩ := hI hsh
      obtain ⟨more', o, La, hcs', hout, hrel, hk', hraw'⟩ :=
        addStep_ok ih frames all cs outs es grp p (hsh _ ha) r a' r' hr
      simp only at hcs hT2 hraw
      refine ⟨more ++ more', T ++ [(((es, grp)), o, La)], by simp [hcs', hcs], by simp [hT1], by simp [hout, hT2],
        fun t ht => ?_, by simp [hk, hk', presKeys_append], fun q hq => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hT3 t ht
        · exact hrel
      · simp only [List.flatMap_append, List.mem_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at hq
        rcases hq with hq | hq
        · exact RawOk.mono (hraw q hq) (by intro x hx; simp [hcs', hx])
        · exact hraw' q hq)
    (fun _ => ⟨[], [], by simp, rfl, rfl, by simp, by simp [presKeys], by simp⟩)
  simpa using this

theorem seq_noadd {E : Env} {v : Variant} {n : Nat} {isExt : Bool} {rootEs : List Entry}
    {adds : List (List Entry × Bool)} {r0 : List (String × Val) × List (Option FieldList)}
    (hnd : ¬(!decide (List.map (fun x => x.name) (rootEs ++ List.flatMap (fun x => x.1) adds)).Nodup) = true)
    (hsh : ¬(!adds.all fun a => a.2 || a.1.length == 1) = true)
    (habs : ¬(!adds.all fun a => a.1.all (absentOkB E n false)) = true)
    (h0 : r0.2.length = rootEs.length ∧ ∃ new, r0.1 = [] ++ new ∧
      new.map (·.1) = presKeys (rootEs.zip r0.2) ∧ ∀ q ∈ rootEs.zip r0.2, RawOk E v n true r0.1 q) :
    SeqFields E v n (per E v n) isExt rootEs adds r0.1
      (if isExt then .unaligned [false] :: seqRootFields v rootEs r0.2 else seqRootFields v rootEs r0.2) := by
  obtain ⟨hlen, new, hcs, hk, hr⟩ := h0
  have hnd' := bnot_false hnd
  rw [decide_eq_true_eq] at hnd'
  have hsh' := List.all_eq_true.1 (bnot_false hsh)
  have habs' := List.all_eq_true.1 (bnot_false habs)
  simp only [List.nil_append] at hcs
  subst hcs
  let T := adds.map fun a => (a, (none : Option FieldList), a.1.map fun e => (e, (none : Option FieldList)))
  have hT2 : ∀ t ∈ T, AddRel v t.1 t.2.1 t.2.2 := by
    intro t ht
    simp only [T, List.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    refine ⟨by simp [List.map_map, Function.comp_def], ?_⟩
    split
    · simp
    · rename_i hg
      have h1 := hsh' a ha
      have : a.1.length = 1 := by
        obtain ⟨es, g⟩ := a
        cases g
        · simpa using h1
        · exact absurd rfl hg
      obtain ⟨es, g⟩ := a
      match es, this with
      | [e], _ => exact ⟨e, rfl, rfl⟩
  have hflat : T.flatMap (·.2.2) = (adds.flatMap (·.1)).map fun e => (e, (none : Option FieldList)) := by
    simp [T, List.flatMap_map, List.map_flatMap]
  have core := seq_core (E := E) (v := v) (n := n) (more := []) hnd' hlen hk
    (fun q hq => by simpa using hr q hq) T (by simp [T, Function.comp_def]) hT2
    (by rw [hflat]; simp [presKeys])
    (fun q hq => by
      rw [hflat] at hq
      simp only [List.mem_map, List.mem_flatMap] at hq
      obtain ⟨e, ⟨a, ha, he⟩, rfl⟩ := hq
      exact List.all_eq_true.1 (habs' a ha) e he)
  simp only [List.append_nil] at core
  obtain ⟨c1, c2, c3⟩ := core
  refine ⟨c1, r0.2, T.map (·.2.1), c2, c3, ?_⟩
  have hp : (List.map Option.isSome (List.map (fun x => x.2.1) T)).any id = false := by simp [T]
  simp only [hp]
  cases isExt <;> simp

theorem seq_add {E : Env} {v : Variant} {n : Nat} {rootEs : List Entry}
    {adds : List (List Entry × Bool)} {r0 r1 : List (String × Val) × List (Option FieldList)} {present : List Bits}
    (hnd : ¬(!decide (List.map (fun x => x.name) (rootEs ++ List.flatMap (fun x => x.1) adds)).Nodup) = true)
    (hsh : ¬(!adds.all fun a => a.2 || a.1.length == 1) = true)
    (h0 : r0.2.length = rootEs.length ∧ ∃ new, r0.1 = [] ++ new ∧
      new.map (·.1) = presKeys (rootEs.zip r0.2) ∧ ∀ q ∈ rootEs.zip r0.2, RawOk E v n true r0.1 q)
    (hpl : ¬((List.map (fun u => List.headD u false) present).length != adds.length) = true)
    (h1 : (∀ a ∈ adds.zip (List.map (fun u => List.headD u false) present), a.1.2 = true ∨ a.1.1.length = 1) →
      FoldI E v n r0.1 (adds.zip (List.map (fun u => List.headD u false) present)) r1)
    (hany : ¬(!(List.map Option.isSome r1.2).any id) = true) :
    SeqFields E v n (per E v n) true rootEs adds r1.1
      (.unaligned [true] :: seqRootFields v rootEs r0.2 ++
        (lengthDet v .normallySmall (.field false (bitUnits (List.map Option.isSome r1.2))) ++
          r1.2.flatMap fun o => match o with
            | some f => openField v f
            | none => [])) := by
  obtain ⟨hlen, new, hcs, hk, hr⟩ := h0
  have hnd' := bnot_false hnd
  rw [decide_eq_true_eq] at hnd'
  have hsh' := List.all_eq_true.1 (bnot_false hsh)
  have hpl' : (List.map (fun u => List.headD u false) present).length = adds.length := by simpa using hpl
  simp only [List.nil_append] at hcs
  obtain ⟨more, T, hcs1, hT1, hT2, hT3, hk1, hraw1⟩ := h1 (fun a ha => by
    have := hsh' a.1 (List.of_mem_zip ha).1
    simpa [beq_iff_eq] using this)
  rw [List.map_fst_zip (by omega)] at hT1
  rw [hcs] at hcs1
  have core := seq_core (E := E) (v := v) (n := n) (more := more) hnd' hlen hk
    (fun q hq => by rw [← hcs]; exact hr q hq) T hT1 hT3 hk1 (fun q hq => by rw [← hcs1]; exact hraw1 q hq)
  rw [← hcs1, ← hT2] at core
  obtain ⟨c1, c2, c3⟩ := core
  refine ⟨c1, r0.2, r1.2, c2, c3, ?_⟩
  have hp : (List.map Option.isSome r1.2).any id = true := by simpa [Option.isSome_iff_ne_none] using hany
  simp only [hp, ↓reduceIte]
  rfl

/-- `okpr`, and the binds of `seqR`: the root components and the additions. -/
macro "okps " ih:term : tactic => `(tactic| repeat' (first
  | exact OkP.throw
  | (with_reducible refine OkP.bind OkP.throw ?_; intro _ h; exact h.elim)
  | (with_reducible apply OkP.pure_bind)
  | (with_reducible refine OkP.bind (compsR_ok $ih _ _ _ _ _ _) ?_; intro _ _)
  | (with_reducible refine OkP.bind (fold_ok $ih _ _ _ _) ?_; intro _ _)
  | split
  | dsimp only
  | simp only [↓reduceIte]
  | (with_reducible refine OkP.bind (OkP.any _) ?_; intro _ _)))

theorem seqR_ok {E : Env} {v : Variant} {n : Nat} {rec : List DFrame → Scope → Ty → PM (Val × FieldList)}
    (ih : RecOk E v n rec) (frames : List DFrame) (isExt : Bool) (rootEs : List Entry)
    (adds : List (List Entry × Bool)) :
    OkP (seqR E v n rec frames isExt rootEs adds)
      (fun p => ∃ cs, p.1 = .seq cs ∧ SeqFields E v n (per E v n) isExt rootEs adds cs p.2) := by
  unfold seqR
  okps ih
  all_goals first
    | exact absurd rfl ‹¬(!false) = true›
    | (apply OkP.pure; exact ⟨_, rfl, by simpa [*] using seq_noadd (isExt := isExt) ‹_› ‹_› ‹_› ‹_›⟩)
    | (apply OkP.pure; refine ⟨_, rfl, ?_⟩; simp only [‹isExt = true›]
       exact seq_add ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)

theorem pdecB_sequence (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' r e r2 :
    OkP (pdecB E v n rec frames hint sc t sc' (.sequence r e r2))
      (fun p => perB E v n (per E v n) sc t sc' (.sequence r e r2) p.1 p.2) := by
  simp only [pdecB]
  cases hs : splitEntries (entries E n sc' r e r2) e with
  | mk rootEs adds =>
    refine OkP.mono (seqR_ok ih _ _ _ _) fun p ⟨cs, hp, hsf⟩ => ?_
    obtain ⟨x, fl⟩ := p
    simp only at hp hsf
    subst hp
    simp only [perB, hs]
    exact hsf

theorem pdecB_set (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' r e r2 :
    OkP (pdecB E v n rec frames hint sc t sc' (.set r e r2))
      (fun p => perB E v n (per E v n) sc t sc' (.set r e r2) p.1 p.2) := by
  simp only [pdecB]
  refine OkP.mono (seqR_ok ih _ _ _ _) fun p ⟨cs, hp, hsf⟩ => ?_
  obtain ⟨x, fl⟩ := p
  simp only at hp hsf
  subst hp
  simp only [perB]
  exact hsf

theorem pdecB_ok (E : Env) (v : Variant) (n : Nat) rec (ih : RecOk E v n rec) frames hint sc t sc' bt :
    OkP (pdecB E v n rec frames hint sc t sc' bt)
      (fun p => perB E v n (per E v n) sc t sc' bt p.1 p.2) := by
  cases bt with
  | boolean => exact pdecB_boolean E v n rec frames hint sc t sc'
  | integer z => exact pdecB_integer E v n rec frames hint sc t sc' z
  | enumerated root ext => exact pdecB_enumerated E v n rec frames hint sc t sc' root ext
  | real => exact pdecB_real E v n rec frames hint sc t sc'
  | bitString named => exact pdecB_bitString E v n rec frames hint sc t sc' named
  | octetString => exact pdecB_octetString E v n rec frames hint sc t sc'
  | null => exact pdecB_null E v n rec frames hint sc t sc'
  | sequence r e r2 => exact pdecB_sequence E v n rec ih frames hint sc t sc' r e r2
  | set r e r2 => exact pdecB_set E v n rec ih frames hint sc t sc' r e r2
  | sequenceOf el => exact pdecB_sequenceOf E v n rec ih frames hint sc t sc' el
  | setOf el => exact pdecB_setOf E v n rec ih frames hint sc t sc' el
  | choice root ext => exact pdecB_choice E v n rec ih frames hint sc t sc' root ext
  | objectIdentifier => exact pdecB_oid E v n rec frames hint sc t sc'
  | relativeOid => exact pdecB_relOid E v n rec frames hint sc t sc'
  | oidIri => exact pdecB_oidIri E v n rec frames hint sc t sc'
  | relativeOidIri => exact pdecB_relOidIri E v n rec frames hint sc t sc'
  | restricted k => exact pdecB_restricted E v n rec frames hint sc t sc' k
  | generalizedTime => exact pdecB_genTime E v n rec frames hint sc t sc'
  | utcTime => exact pdecB_utcTime E v n rec frames hint sc t sc'
  | objectDescriptor => exact pdecB_objectDescriptor E v n rec frames hint sc t sc'
  | openType => exact pdecB_openType E v n rec ih frames hint sc t sc'
  | _ => simp only [pdecB]; exact OkP.throw

theorem pdec_ok (E : Env) (v : Variant) : ∀ n, RecOk E v n (pdec E v n)
  | 0 => fun frames sc t => by simp only [pdec]; exact OkP.throw
  | n + 1 => fun frames sc t => by
    simp only [pdec]
    split
    · rename_i sc' bt hb
      refine OkP.bind (pdecB_ok E v n (pdec E v n) (pdec_ok E v n) (framesIn frames t) _ sc t sc' bt) fun p hp => ?_
      have hp' : per E v (n + 1) sc t p.1 p.2 := by simp only [per, hb]; exact hp
      split
      · exact OkP.bind (Q := fun _ => True) OkP.throw fun _ _ => OkP.pure hp'
      · exact OkP.pure hp'
    · exact OkP.throw

/-- **Soundness of the PER decoder**: what `pdec` returns, `per` relates. -/
theorem pdec_sound (E : Env) (v : Variant) : ∀ (n : Nat) (frames : List DFrame) (sc : Scope) (t : Ty)
    (r r' : Rd) (x : Val) (fl : FieldList),
    (pdec E v n frames sc t).run r = .ok ((x, fl), r') → per E v n sc t x fl :=
  fun n frames sc t r r' x fl h => pdec_ok E v n frames sc t r (x, fl) r' h

/-- **Soundness of `decode`**: the octets it accepts are the complete encoding (X.691 11.1) of a
field-list that `per` relates to the value it returns. -/
theorem decode_sound {E : Env} {v : Variant} {fuel : Nat} {m : Module} {t : Ty} {os : Octets} {x : Val}
    (h : decode E v fuel m t os = .ok x) :
    ∃ fl, per E v fuel (.ofModule m) t x fl ∧ bitsOf os = complete v .other fl := by
  unfold decode at h
  cases hr : (pdec E v fuel [] (.ofModule m) t).run ⟨0, bitsOf os⟩ with
  | error e => simp [hr] at h; cases h
  | ok res =>
    obtain ⟨⟨x', fl⟩, r'⟩ := res
    simp only [hr] at h
    have hfl := pdec_sound E v fuel [] _ t _ _ x' fl hr
    have key : x = x' ∧ completeFast v .other fl = bitsOf os := by
      simp only [bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
      · rename_i hc
        refine ⟨?_, by simpa using hc⟩
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
          · simp [pure, Except.pure] at h; exact h.symm
    obtain ⟨rfl, hc⟩ := key
    exact ⟨fl, hfl, by rw [← completeFast_eq, hc]⟩

/-- **Soundness of `decodePrefix`**: the octets start with the complete encoding (X.691 11.1) of a
field-list that `per` relates to the value returned. -/
theorem decodePrefix_sound {E : Env} {v : Variant} {fuel : Nat} {m : Module} {t : Ty} {os : Octets} {x : Val}
    {k : Nat} (h : decodePrefix E v fuel m t os = .ok (x, k)) :
    ∃ fl rest, per E v fuel (.ofModule m) t x fl ∧ bitsOf os = complete v .other fl ++ rest := by
  unfold decodePrefix at h
  cases hr : (pdec E v fuel [] (.ofModule m) t).run ⟨0, bitsOf os⟩ with
  | error e => simp [hr] at h; cases h
  | ok res =>
    obtain ⟨⟨x', fl⟩, r'⟩ := res
    simp only [hr] at h
    have hfl := pdec_sound E v fuel [] _ t _ _ x' fl hr
    have key : x = x' ∧ completeFast v .other fl = (bitsOf os).take (completeFast v .other fl).length := by
      simp only [bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
      · rename_i hc
        refine ⟨?_, by simpa using hc⟩
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
          · simp [pure, Except.pure] at h; exact h.1.symm
    obtain ⟨rfl, hc⟩ := key
    refine ⟨fl, (bitsOf os).drop (completeFast v .other fl).length, hfl, ?_⟩
    rw [← completeFast_eq]
    conv_lhs => rw [← List.take_append_drop (completeFast v .other fl).length (bitsOf os)]
    rw [← hc]

end Asn1.X691
