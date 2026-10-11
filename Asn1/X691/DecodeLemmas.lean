import Asn1.X691.Decode
import Asn1.X690.DecSound

/-!
# Lemmas for the soundness of the PER decoder

What `DecodeSound.lean` needs about the pieces of `Decode.lean` that are not one case of `perB`:
the one-pass complete encoding, value evaluation, the equality checks for DEFAULT components, the
readers' results, and the bits sent for a bit string with named bits.
-/

namespace Asn1.X691

open Asn1.X680

/-! ## The complete encoding -/

theorem concatFields_eq_layout (al : Bool) (acc : Bits) (fl : FieldList) :
    concatFields al acc fl = acc ++ layout al acc.length fl := by
  induction fl generalizing acc with
  | nil => simp [concatFields, layout]
  | cons f fs ih =>
    cases f with
    | unaligned bs =>
      simp only [concatFields, layout, ih, List.length_append, List.append_assoc]
    | aligned bs =>
      cases al
      · simp [concatFields, layout, ih]
      · simp only [concatFields, layout, ih, pad8, List.length_append, List.length_replicate, ite_true,
          List.append_assoc, Nat.add_assoc]

theorem completeFast_eq (v : Variant) (c : Carrier) (fl : FieldList) :
    completeFast v c fl = complete v c fl := by
  have h := concatFields_eq_layout v.aligned [] fl
  simp only [List.nil_append, List.length_nil] at h
  simp only [completeFast, complete, h]

/-! ## Values and DEFAULT components -/

theorem evalValC_spec (E : Env) : ∀ (n : Nat) (sc : Scope) (d w : Val),
    evalValC E n sc d = some w → evalVal E n sc d w
  | 0, _, _, _, h => by simp [evalValC] at h
  | n + 1, sc, d, w, h => by
    cases d with
    | ref mn name args =>
      simp only [evalValC] at h
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [evalVal, hr]
      exact evalValC_spec E n sc' v w h
    | fromObject _ _ => simp [evalValC] at h
    | raw _ => simp [evalValC] at h
    | seq cs =>
      simp only [evalValC, Option.map_eq_some_iff] at h
      obtain ⟨ds, hm, rfl⟩ := h
      simp only [evalVal]
      refine ⟨ds, rfl, ?_⟩
      clear * - hm
      induction cs generalizing ds with
      | nil => simp at hm; subst hm; exact .nil
      | cons p cs ih =>
        simp only [List.mapM_cons] at hm
        cases hq : evalValC E n sc p.2 with
        | none => simp [hq] at hm
        | some q =>
          cases hws : List.mapM (fun p : String × Val => Option.map (fun x => (p.1, x)) (evalValC E n sc p.2)) cs with
          | none => simp [hq, hws] at hm
          | some ds' =>
            simp [hq, hws] at hm; subst hm
            exact .cons ⟨rfl, evalValC_spec E n sc _ _ hq⟩ (ih ds' hws)
    | seqOf vs =>
      simp only [evalValC, Option.map_eq_some_iff] at h
      obtain ⟨ws, hm, rfl⟩ := h
      simp only [evalVal]
      refine ⟨ws, rfl, ?_⟩
      clear * - hm
      induction vs generalizing ws with
      | nil => simp at hm; subst hm; exact .nil
      | cons p vs ih =>
        simp only [List.mapM_cons] at hm
        cases hq : evalValC E n sc p with
        | none => simp [hq] at hm
        | some q =>
          cases hws : List.mapM (evalValC E n sc) vs with
          | none => simp [hq, hws] at hm
          | some ws' =>
            simp [hq, hws] at hm; subst hm
            exact .cons (evalValC_spec E n sc _ _ hq) (ih ws' hws)
    | setOf vs =>
      simp only [evalValC, Option.map_eq_some_iff] at h
      obtain ⟨ws, hm, rfl⟩ := h
      simp only [evalVal]
      refine ⟨ws, rfl, ?_⟩
      clear * - hm
      induction vs generalizing ws with
      | nil => simp at hm; subst hm; exact .nil
      | cons p vs ih =>
        simp only [List.mapM_cons] at hm
        cases hq : evalValC E n sc p with
        | none => simp [hq] at hm
        | some q =>
          cases hws : List.mapM (evalValC E n sc) vs with
          | none => simp [hq, hws] at hm
          | some ws' =>
            simp [hq, hws] at hm; subst hm
            exact .cons (evalValC_spec E n sc _ _ hq) (ih ws' hws)
    | choice a x =>
      simp only [evalValC, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact ⟨y, rfl, evalValC_spec E n sc x y hy⟩
    | open_ t x =>
      simp only [evalValC, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact ⟨y, rfl, evalValC_spec E n sc x y hy⟩
    | _ => simp only [evalValC, Option.some.injEq] at h; subst h; simp [evalVal]

theorem eqvReflB_spec (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x : Val),
    eqvReflB E n sc t x = true → eqv E n sc t x x
  | 0, _, _, _, h => by simp [eqvReflB] at h
  | n + 1, sc, t, x, h => by
    cases t with
    | ref name =>
      simp only [eqvReflB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact eqvReflB_spec E n sc' t' x h
      · cases h
    | extRef mn name =>
      simp only [eqvReflB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact eqvReflB_spec E n sc' t' x h
      · cases h
    | paramRef mn name args =>
      simp only [eqvReflB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact eqvReflB_spec E n sc' t' x h
      · cases h
    | tagged tg k t => simp only [eqvReflB] at h; simp only [eqv]; exact eqvReflB_spec E n sc t x h
    | constrained t c => simp only [eqvReflB] at h; simp only [eqv]; exact eqvReflB_spec E n sc t x h
    | sequence r e r2 | set r e r2 =>
      cases x with
      | seq cs =>
        simp only [eqvReflB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
        simp only [eqv]
        obtain ⟨h1, h2⟩ := h
        refine ⟨h1, h1, fun en hen => ?_⟩
        have h3 := h2 ⟨en, hen⟩ (List.mem_attach _ _)
        simp only at h3
        unfold SeqEntry
        cases hl : cs.lookup en.name with
        | none => trivial
        | some y => rw [hl] at h3; exact eqvReflB_spec E n _ _ _ h3
      | _ => simp [eqvReflB] at h
    | sequenceOf el =>
      cases x with
      | seqOf xs =>
        simp only [eqvReflB, List.all_eq_true] at h
        simp only [eqv]
        clear * - h eqvReflB_spec
        have : ∀ y ∈ xs, eqv E n sc el y y := fun y hy => eqvReflB_spec E n sc el y (h ⟨y, hy⟩ (List.mem_attach _ _))
        clear h
        induction xs with
        | nil => exact .nil
        | cons y ys ih => exact .cons (this y (by simp)) (ih fun z hz => this z (by simp [hz]))
      | _ => simp [eqvReflB] at h
    | setOf el =>
      cases x with
      | setOf xs =>
        simp only [eqvReflB, List.all_eq_true] at h
        simp only [eqv]
        refine ⟨xs, List.Perm.refl _, ?_⟩
        have : ∀ y ∈ xs, eqv E n sc el y y := fun y hy => eqvReflB_spec E n sc el y (h ⟨y, hy⟩ (List.mem_attach _ _))
        clear h
        induction xs with
        | nil => exact .nil
        | cons y ys ih => exact .cons (this y (by simp)) (ih fun z hz => this z (by simp [hz]))
      | _ => simp [eqvReflB] at h
    | choice root ext =>
      cases x with
      | choice a y =>
        simp only [eqvReflB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨alt, hm, hn, hr⟩ := h
        simp only [eqv]
        exact ⟨trivial, alt, hm, hn, eqvReflB_spec E n sc alt.ty y hr⟩
      | _ => simp [eqvReflB] at h
    | bitString named =>
      cases x with
      | bits bs => simp only [eqv]; split <;> trivial
      | _ => simp [eqvReflB] at h
    | openType =>
      cases x with
      | open_ t y =>
        simp only [eqvReflB] at h
        simp only [eqv]
        exact ⟨trivial, eqvReflB_spec E n sc t y h⟩
      | _ => simp [eqvReflB] at h
    | selection _ _ | classField _ _ | instanceOf _ | embeddedPdv | external | characterString
    | time | date | timeOfDay | dateTime | duration => simp [eqvReflB] at h
    | _ => simp [eqv]

theorem neqvB_spec (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    neqvB E n sc t x y = true → ¬ eqv E n sc t x y
  | 0, _, _, _, _, _ => by simp [eqv]
  | n + 1, sc, t, x, y, h => by
    cases t with
    | ref name =>
      simp only [neqvB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact neqvB_spec E n sc' t' x y h
      · rename_i hr; split <;> simp_all
    | extRef mn name =>
      simp only [neqvB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact neqvB_spec E n sc' t' x y h
      · rename_i hr; split <;> simp_all
    | paramRef mn name args =>
      simp only [neqvB] at h; simp only [eqv]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact neqvB_spec E n sc' t' x y h
      · rename_i hr; split <;> simp_all
    | tagged tg k t => simp only [neqvB] at h; simp only [eqv]; exact neqvB_spec E n sc t x y h
    | constrained t c => simp only [neqvB] at h; simp only [eqv]; exact neqvB_spec E n sc t x y h
    | sequenceOf el =>
      simp only [eqv]
      cases x <;> cases y <;> simp only [neqvB, bne_iff_ne, ne_eq] at h <;> try simp
      intro hf; exact h hf.length_eq
    | setOf el =>
      simp only [eqv]
      cases x <;> cases y <;> simp only [neqvB, bne_iff_ne, ne_eq] at h <;> try simp
      rintro ys' hp hf; exact h (hf.length_eq.trans hp.length_eq)
    | boolean | integer _ | enumerated _ _ | null | objectIdentifier | relativeOid | octetString
    | restricted _ | utcTime | generalizedTime =>
      simp only [neqvB] at h; simp only [eqv]; exact X690.litNeq_spec x y h
    | bitString named =>
      simp only [eqv]
      cases x <;> cases y <;> simp only [neqvB] at h <;> try simp
      split at h <;> simp_all
    | _ => simp [neqvB] at h

theorem isCompositeB_spec {E : Env} {n : Nat} {sc : Scope} {t : Ty} (h : isCompositeB E n sc t = true) :
    CompOut.isComposite E n sc t := by
  unfold isCompositeB at h
  unfold CompOut.isComposite
  split at h <;> simp_all

theorem presentOkB_compOut {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → FieldList → Prop}
    {root : Bool} {cs : List (String × Val)} {en : Entry} {x : Val} {f : FieldList}
    (h : presentOkB E v n en x = true) (hx : cs.lookup en.name = some x) (hr : rec en.scope en.ty x f) :
    CompOut E v n rec root cs en (some f) := by
  unfold presentOkB at h
  unfold CompOut
  split
  · rw [hx]; exact ⟨f, hr, rfl⟩
  · rw [hx]; exact ⟨f, hr, rfl⟩
  · rename_i d hd
    rw [hd] at h
    simp only at h
    split at h
    · rename_i dv hdv
      refine ⟨dv, evalValC_spec E n en.scope d dv hdv, ?_⟩
      simp only [hx, Option.getD_some]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      refine ⟨fun he => ?_, fun _ => ⟨f, hr, rfl⟩⟩
      rcases h with (h | h) | ⟨hc, hb⟩
      · have := X690.notDefaultB_spec h
        unfold X690.IsDefault at this
        rw [hd] at this
        exact absurd ⟨dv, evalValC_spec E n en.scope d dv hdv, he⟩ this
      · exact absurd he (neqvB_spec E n _ _ _ _ h)
      · exact .inr ⟨hc, isCompositeB_spec hb, f, hr, rfl⟩
    · cases h

theorem absentOkB_compOut {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → FieldList → Prop}
    {root : Bool} {cs : List (String × Val)} {en : Entry}
    (h : absentOkB E n root en = true) (hx : cs.lookup en.name = none) :
    CompOut E v n rec root cs en none := by
  unfold absentOkB at h
  unfold CompOut
  split
  · rename_i hp; rw [hp] at h; rw [hx]; simpa using h
  · rw [hx]
  · rename_i d hd
    rw [hd] at h
    simp only at h
    split at h
    · rename_i dv hdv
      refine ⟨dv, evalValC_spec E n en.scope d dv hdv, ?_⟩
      simp only [hx, Option.getD_none]
      have he := eqvReflB_spec E n _ _ _ h
      exact ⟨fun _ => .inl trivial, fun hn => absurd he hn⟩
    · cases h

/-! ## What the readers return -/

theorem DecodeLemmas.pm_bind_ok {α β : Type} {x : PM α} {g : α → PM β} {r r' : Rd} {b : β}
    (h : (x >>= g).run r = .ok (b, r')) : ∃ a r1, x.run r = .ok (a, r1) ∧ (g a).run r1 = .ok (b, r') := by
  simp only [StateT.run_bind] at h
  cases hx : x.run r with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem DecodeLemmas.pm_pure_ok {α : Type} {a b : α} {r r' : Rd} (h : (pure a : PM α).run r = .ok (b, r')) : b = a ∧ r' = r := by
  simp only [StateT.run_pure] at h
  cases h; exact ⟨rfl, rfl⟩

theorem DecodeLemmas.pm_throw_ok {α : Type} {e : String} {b : α} {r r' : Rd} (h : (throw e : PM α).run r = .ok (b, r')) : False := by
  cases h


theorem ulR_mem {α : Type} {P : α → Prop} {v : Variant} {readK : Bool → Nat → PM (List α)}
    (hk : ∀ al k r as r', (readK al k).run r = .ok (as, r') → ∀ a ∈ as, P a) :
    ∀ (f : Nat) (al : Bool) (r r' : Rd) (xs : List α),
      (ulR v readK al f).run r = .ok (xs, r') → ∀ a ∈ xs, P a
  | 0, al, r, r', xs, h => by simp only [ulR] at h; exact (DecodeLemmas.pm_throw_ok h).elim
  | f + 1, al, r, r', xs, h => by
    simp only [ulR] at h
    obtain ⟨o, r1, _, h⟩ := DecodeLemmas.pm_bind_ok h
    split at h
    · exact hk _ _ _ _ _ h
    · obtain ⟨o2, r2, _, h⟩ := DecodeLemmas.pm_bind_ok h
      exact hk _ _ _ _ _ h
    · split at h
      · exact (DecodeLemmas.pm_throw_ok h).elim
      · obtain ⟨us, r2, hus, h⟩ := DecodeLemmas.pm_bind_ok h
        obtain ⟨more, r3, hmore, h⟩ := DecodeLemmas.pm_bind_ok h
        obtain ⟨rfl, -⟩ := DecodeLemmas.pm_pure_ok h
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hk _ _ _ _ _ hus a ha
        · exact ulR_mem hk f al _ _ _ hmore a ha

theorem lenDetR_mem {α : Type} {P : α → Prop} {v : Variant} {k : LenKind}
    {readK : Bool → Nat → PM (List α)} {al : Bool} {fuel : Nat}
    (hk : ∀ al k r as r', (readK al k).run r = .ok (as, r') → ∀ a ∈ as, P a)
    {r r' : Rd} {xs : List α} (h : (lenDetR v k readK al fuel).run r = .ok (xs, r')) :
    ∀ a ∈ xs, P a := by
  unfold lenDetR at h
  split at h
  · split at h
    · obtain ⟨c, r1, _, h⟩ := DecodeLemmas.pm_bind_ok h
      split at h
      · obtain ⟨rfl, -⟩ := DecodeLemmas.pm_pure_ok h; simp
      · exact hk _ _ _ _ _ h
    · exact ulR_mem hk _ _ _ _ _ h
  · obtain ⟨b, r1, _, h⟩ := DecodeLemmas.pm_bind_ok h
    split at h
    · exact ulR_mem hk _ _ _ _ _ h
    · obtain ⟨c, r2, _, h⟩ := DecodeLemmas.pm_bind_ok h
      exact hk _ _ _ _ _ h
  · exact ulR_mem hk _ _ _ _ _ h

theorem octetsOf_completeFast {v : Variant} {fl : FieldList} {us : List Bits}
    (h : (us != octetsOf (completeFast v .other fl)) = false) :
    us = octetsOf (complete v .other fl) := by
  rw [← completeFast_eq]
  simpa using h

/-! ## Bit strings with named bits (16.2, 16.3) -/

theorem DecodeLemmas.strip_append (bs : Bits) :
    bs = stripTrailingZeros bs ++ List.replicate (bs.length - (stripTrailingZeros bs).length) false := by
  have h := List.takeWhile_append_dropWhile (p := (· == false)) (l := bs.reverse)
  generalize ht : List.takeWhile (· == false) bs.reverse = t at h
  generalize hd : List.dropWhile (· == false) bs.reverse = d at h
  have hall : ∀ b ∈ t, b = false := by
    intro b hb
    have := List.all_eq_true.mp (ht ▸ List.all_takeWhile (p := (· == false)) (l := bs.reverse)) b hb
    simpa using this
  have hr : t = List.replicate t.length false := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hs : stripTrailingZeros bs = d.reverse := by simp only [stripTrailingZeros, hd]
  have hlen : bs.length = t.length + d.length := by
    rw [← List.length_reverse (as := bs), ← h, List.length_append]
  rw [hs, List.length_reverse, show bs.length - d.length = t.length by omega]
  conv => lhs; rw [← List.reverse_reverse bs, ← h]
  rw [List.reverse_append]
  conv => lhs; rw [hr]
  rw [List.reverse_replicate]


theorem namedBitsSent_self (S : PSet Nat) (bs : Bits) (ha : S.a bs.length)
    (hmin : ∀ k, k < bs.length → (stripTrailingZeros bs).length ≤ k → ¬ S.a k) :
    NamedBitsSent S bs bs := by
  have hle : (stripTrailingZeros bs).length ≤ bs.length := by
    have := congrArg List.length (DecodeLemmas.strip_append bs)
    simp at this; omega
  refine ⟨bs.length, DecodeLemmas.strip_append bs, hle, ha, fun k' h1 h2 => ?_⟩
  by_contra hc
  exact hmin k' (by omega) h1 h2

end Asn1.X691
