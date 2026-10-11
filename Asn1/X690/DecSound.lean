import Asn1.X690.DecodeSound

/-!
# What the decoder returns, `ber` relates

`dec_sound`: when `dec E p n … sc t nd` returns the value `v`, `ber E p n sc t v nd` holds: `nd` is
an encoding of `v` under profile `p`, by the relation that states X.690. With `parseNode_octets`
and `lenOkB_spec`, `decode_sound` gives the encoding and its octets.

The theorem is at the fuel the decoder ran with. `BerEncodes` asks for every large enough fuel, and
`ber` is not monotone in fuel by construction: under CER and DER it says that an encoded component
is *not* its default (`¬ IsDefault`, X.690 11.5), a negative use of `eqv`. Stability in fuel is a
separate property of the X.680 layer, not proved here. Completeness (every encoding `ber` allows is
decoded) is not claimed either.
-/
namespace Asn1.X690
open Asn1.X680

/-! ## Plumbing -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β}
    (h : (x >>= f) = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {v : β}
    (h : Except.map f x = .ok v) : ∃ a, x = .ok a ∧ f a = v := by
  cases x with
  | error e => cases h
  | ok a => simp only [Except.map, Except.ok.injEq] at h; exact ⟨a, rfl, h⟩

theorem mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → List.Forall₂ (fun x y => f x = .ok y) l ys
  | [], ys, h => by
    simp only [List.mapM_nil] at h; cases h; exact .nil
  | x :: l, ys, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := except_bind_ok h
    obtain ⟨ys', hys, h⟩ := except_bind_ok h
    cases h
    exact .cons hy (mapM_ok hys)

theorem guardE_ok {α : Type} {b : Bool} {m : String} {x y : α} (h : guardE b m x = .ok y) :
    b = true ∧ y = x := by
  unfold guardE at h; split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem sortedB_pairwise {α : Type} {r : α → α → Bool}
    (htr : ∀ a b c, r a b = true → r b c = true → r a c = true) :
    ∀ {l : List α}, sortedB r l = true → l.Pairwise fun a b => r a b = true
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [sortedB, Bool.and_eq_true] at h
    have ih := sortedB_pairwise htr h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact htr _ _ _ h.1 (List.rel_of_pairwise_cons ih hc)

theorem sortedB_pairwise' {α : Type} {r : α → α → Bool} {R : α → α → Prop}
    (hR : ∀ a b, r a b = true → R a b) (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ {l : List α}, sortedB r l = true → l.Pairwise R
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [sortedB, Bool.and_eq_true] at h
    have ih := sortedB_pairwise' hR htr h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hR _ _ h.1
    · exact htr _ _ _ (hR _ _ h.1) (List.rel_of_pairwise_cons ih hc)

theorem Tag.lt_trans (a b c : Tag) : Tag.lt a b = true → Tag.lt b c = true → Tag.lt a c = true := by
  simp only [Tag.lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  omega

/-! ## Octets -/

theorem octet_val (o : Fin 256) : octet o.val = o := by
  apply Fin.ext; simp [octet, Nat.mod_eq_of_lt o.isLt]

theorem octLeB_spec : ∀ (a b : Octets), octLeB a b = true → octLe a b
  | [], _, _ => trivial
  | x :: as, [], h => by
    simp only [octLeB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨Fin.ext h.1, octLeB_spec as [] h.2⟩
  | x :: as, y :: bs, h => by
    simp only [octLeB, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, octLeB_spec as bs h2⟩

/-- An octet string that `octLe` puts below the empty one is all zeros, so it is below any. -/
theorem octLe_nil_any : ∀ (a b : Octets), octLe a [] → octLe a b
  | [], _, _ => trivial
  | x :: as, [], h => h
  | x :: as, y :: bs, h => by
    obtain ⟨hx, h⟩ := h
    subst hx
    by_cases hy : (0 : Fin 256) < y
    · exact Or.inl hy
    · have : y = 0 := by
        apply Fin.ext; simp only [Fin.lt_def, Fin.val_zero, not_lt, Nat.le_zero] at hy; exact hy
      exact Or.inr ⟨this.symm, octLe_nil_any as bs h⟩

theorem octLe_nil_inv : ∀ (b : Octets), octLe [] b := fun _ => trivial

theorem octLe_trans : ∀ (a b c : Octets), octLe a b → octLe b c → octLe a c
  | [], _, _, _, _ => trivial
  | x :: as, [], c, h1, _ => octLe_nil_any _ _ h1
  | x :: as, y :: bs, [], h1, h2 => by
    obtain ⟨hy, h2⟩ := h2
    subst hy
    rcases h1 with h1 | ⟨rfl, h1⟩
    · exact absurd h1 (by simp)
    · exact ⟨rfl, octLe_trans as bs [] h1 h2⟩
  | x :: as, y :: bs, z :: cs, h1, h2 => by
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, octLe_trans as bs cs h1 h2⟩

/-! ## Length forms and tags -/

mutual
  theorem lenOkB_spec (p : Profile) : ∀ (nd : Node), lenOkB p nd = true → nd.LenOk p
    | .prim _ f cs, h => by simpa [lenOkB, Node.LenOk] using h
    | .cons _ f ch, h => by
      simp only [lenOkB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, lenOkListB_spec p ch h.2⟩
  theorem lenOkListB_spec (p : Profile) : ∀ (ch : List Node), lenOkListB p ch = true → Node.LenOkList p ch
    | [], _ => trivial
    | nd :: rest, h => by
      simp only [lenOkListB, Bool.and_eq_true] at h
      exact ⟨lenOkB_spec p nd h.1, lenOkListB_spec p rest h.2⟩
end

theorem Node.retag_retag (a b : Tag) (nd : Node) : (nd.retag a).retag b = nd.retag b := by
  cases nd <;> rfl

theorem Node.retag_tag (nd : Node) : nd.retag nd.tag = nd := by
  cases nd <;> rfl

theorem Node.tag_retag (a : Tag) (nd : Node) : (nd.retag a).tag = a := by
  cases nd <;> rfl

/-! ## Contents octets -/

theorem octetBits_length (o : Fin 256) : (octetBits o).length = 8 := by simp [octetBits]

theorem octetOf_octetBits (o : Fin 256) (r : Bits) : octetOf (octetBits o ++ r) = o := by
  apply Fin.ext
  have h8 : (octetBits o ++ r).take 8 = octetBits o := by
    rw [List.take_append_of_le_length (by rw [octetBits_length]), List.take_of_length_le (by rw [octetBits_length])]
  simp only [octetOf, h8, octetBits_length, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [octetBits, nnbValue_nnbFn]; simp [Nat.mod_eq_of_lt o.isLt]

theorem bitsToOctets_go_bitsOf : ∀ (k : Nat) (os : Octets), os.length ≤ k → bitsToOctets.go k (bitsOf os) = os
  | _, [], _ => by cases ‹Nat› <;> rfl
  | 0, _ :: _, h => by simp at h
  | k + 1, o :: os, h => by
    have hb : bitsOf (o :: os) = octetBits o ++ bitsOf os := by simp [bitsOf]
    have hne : bitsOf (o :: os) ≠ [] := by
      rw [hb]; intro he; have := congrArg List.length he; simp [octetBits_length] at this
    obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
    rw [hbs, bitsToOctets.go, ← hbs, hb, octetOf_octetBits, List.drop_left' (octetBits_length o),
      bitsToOctets_go_bitsOf k os (by simp at h; omega)]

theorem bitsToOctets_bitsOf (os : Octets) : bitsToOctets (bitsOf os) = os :=
  bitsToOctets_go_bitsOf _ _ (by rw [bitsOf_length]; omega)

theorem boolContents_dec (p : Profile) (o : Fin 256) (h : (p.restricted && o.val != 0 && o.val != 255) = false) :
    BoolContents p (o.val != 0) [o] := by
  refine ⟨o, rfl, ?_⟩
  by_cases h0 : o.val = 0
  · have : o = 0 := Fin.ext h0
    simp [this]
  · have hne : o ≠ 0 := fun e => h0 (by rw [e]; rfl)
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
    refine ⟨hne, fun hr => ?_⟩
    rw [hr] at h
    simp only [Bool.true_and, Bool.and_eq_false_imp, bne_iff_ne, ne_eq, h0, not_false_eq_true,
      forall_const] at h
    exact Fin.ext (by simpa using h)

theorem intContentsB_spec {cs : Octets} (h : intContentsB cs = true) : IntContents (tcValue (bitsOf cs)) cs := by
  simp only [intContentsB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hne, hl⟩ := h
  refine ⟨⟨?_, ?_, rfl, ?_⟩, hne⟩
  · rw [bitsOf_length]; omega
  · rw [bitsOf_length]; have := List.length_pos_iff.mpr hne; omega
  · rcases hl with hl | hl
    · left; rw [bitsOf_length, hl]
    · right; exact hl

theorem decBitsPrim_spec {p : Profile} {cs : Octets} {bs : Bits} (h : decBitsPrim p cs = .ok bs) :
    BitsPrim p bs cs := by
  unfold decBitsPrim at h
  split at h
  · cases h
  · rename_i u rest
    split at h
    · cases h
    split at h
    · cases h
    rename_i hu hemp
    simp only [not_lt] at hu
    have hall := bitsOf_length rest
    have hrest : rest ≠ [] → 8 ≤ (bitsOf rest).length := fun hn => by
      have := List.length_pos_iff.mpr hn; omega
    have hu0 : rest = [] → u.val = 0 := fun hr => by
      by_contra hc; simp [hr, hc] at hemp
    have hle : u.val ≤ (bitsOf rest).length := by
      by_cases hr : rest = []
      · rw [hu0 hr]; omega
      · have := hrest hr; omega
    dsimp only at h
    split at h
    · cases h
    rename_i hpad
    cases h
    refine ⟨u.val, (bitsOf rest).drop ((bitsOf rest).length - u.val), hu, ?_, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp only [List.length_take]; rw [Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel hle, hall]; omega
    · intro he
      have := congrArg List.length he
      simp only [List.length_take, List.length_nil] at this
      rw [Nat.min_eq_left (Nat.sub_le _ _)] at this
      by_cases hr : rest = []
      · exact hu0 hr
      · have := hrest hr; omega
    · rw [List.take_append_drop, bitsToOctets_bitsOf, octet_val]
    · intro hr; simp only [hr, Bool.true_and, bne_iff_ne, ne_eq, Decidable.not_not] at hpad; exact hpad

theorem cerFragmentsB_spec {ch : List Node} (h : decOctets.cerFragmentsB ch = true) : CerFragments ch := by
  simp only [decOctets.cerFragmentsB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro i nd hi hlt
    have : ch.dropLast[i]? = some nd := by rw [List.getElem?_dropLast]; simp [hi]; omega
    simpa using h2 nd (List.mem_of_getElem? this)
  · split at h3
    · rename_i nd hnd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨nd, hnd, h3⟩
    · cases h3

theorem decOctets_spec (p : Profile) : ∀ (n : Nat) (tg : Tag) (nd : Node) (os : Octets),
    decOctets p n tg nd = .ok os → octetsEnc p n tg os nd
  | 0, _, _, _, h => by simp [decOctets] at h
  | n + 1, tg, .prim tg' f cs, os, h => by
    simp only [decOctets] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i h1 h2
    cases h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
    subst h1
    refine Or.inl ⟨f, rfl, fun hc => ?_⟩
    simp [hc] at h2; omega
  | n + 1, tg, .cons tg' f ch, os, h => by
    simp only [decOctets] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i h1 h2
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
    subst h1
    obtain ⟨segs, hsegs, h⟩ := except_bind_ok h
    split at h
    · cases h
    rename_i h3
    cases h
    refine Or.inr ⟨f, ch, segs, rfl, h2, rfl, ?_, fun hc => ?_⟩
    · exact ((mapM_ok hsegs).imp fun _ _ hh => decOctets_spec p n _ _ _ hh).flip
    · have : (1000 < (segs.flatten).length && decOctets.cerFragmentsB ch) = true := by
        simpa [hc] using h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, cerFragmentsB_spec this.2⟩

theorem forall₂_zipIdx_flip {α β : Type} {R : α × Nat → β → Prop} :
    ∀ {ch : List α} {segs : List β} (k : Nat), List.Forall₂ R (ch.zipIdx k) segs →
      List.Forall₂ (fun (si : β × Nat) c => R (c, si.2) si.1) (segs.zipIdx k) ch
  | [], segs, k, h => by
    simp only [List.zipIdx_nil] at h; cases h; exact .nil
  | c :: ch, segs, k, h => by
    simp only [List.zipIdx_cons] at h
    cases h with
    | cons h1 h2 =>
      simp only [List.zipIdx_cons]
      exact .cons h1 (forall₂_zipIdx_flip (k + 1) h2)

theorem decBits_spec (p : Profile) : ∀ (n : Nat) (isLast : Bool) (tg : Tag) (nd : Node) (bs : Bits),
    decBits p n isLast tg nd = .ok bs → bitsEnc p n isLast tg bs nd
  | 0, _, _, _, _, h => by simp [decBits] at h
  | n + 1, isLast, tg, .prim tg' f cs, bs, h => by
    simp only [decBits] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i h1 h2
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
    subst h1
    obtain ⟨bs', hbs, h⟩ := except_bind_ok h
    split at h
    · cases h
    rename_i h3
    cases h
    refine Or.inl ⟨f, cs, rfl, decBitsPrim_spec hbs, fun hl => ?_, fun hc => ?_⟩
    · simpa [hl] using h3
    · simp [hc] at h2; omega
  | n + 1, isLast, tg, .cons tg' f ch, bs, h => by
    simp only [decBits] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i h1 h2
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
    subst h1
    obtain ⟨segs, hsegs, h⟩ := except_bind_ok h
    split at h
    · cases h
    rename_i h3
    cases h
    have hf := mapM_ok hsegs
    have hlen : segs.length = ch.length := by have := hf.length_eq; simpa using this.symm
    refine Or.inr ⟨f, ch, segs, rfl, h2, rfl, ?_, fun hc => ?_⟩
    · have := forall₂_zipIdx_flip 0 hf
      refine this.imp fun si c hh => ?_
      rw [hlen]; exact decBits_spec p n _ _ _ _ hh
    · have : (1000 < ((segs.flatten).length + 7) / 8 + 1 && decOctets.cerFragmentsB ch) = true := by
        simpa [hc] using h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, cerFragmentsB_spec this.2⟩

theorem decUtf8_spec {os : Octets} {cs : List Nat} (h : decUtf8 os = some cs) : utf8String cs = os := by
  unfold decUtf8 at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem decWide_spec {w : Nat} {os : Octets} {cs : List Nat} (h : decWide w os = some cs) :
    cs.flatMap (fun c => beOctets w c) = os := by
  unfold decWide at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h; assumption
    · cases h

theorem decString_spec {p : Profile} {k : StrType} {os : Octets} {v : Val} (h : decString p k os = .ok v) :
    StringOctets p k v os := by
  have hascii : os.all (·.val < 128) = true → StringOctets p .visible (.chars (os.map (·.val))) os ∧
      StringOctets p .ia5 (.chars (os.map (·.val))) os ∧ StringOctets p .numeric (.chars (os.map (·.val))) os ∧
      StringOctets p .printable (.chars (os.map (·.val))) os := by
    intro ha
    have : os = (os.map (·.val)).map octet ∧ ∀ c ∈ os.map (·.val), c < 128 := by
      refine ⟨by simp [Function.comp_def, octet_val], ?_⟩
      intro c hc
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
      exact of_decide_eq_true (List.all_eq_true.mp ha o ho)
    exact ⟨this, this, this, this⟩
  cases k <;> simp only [decString] at h
  · split at h <;> cases h
    simp only [StringOctets, bmpOctets]; exact (decWide_spec (by assumption)).symm
  · split at h <;> cases h
    exact ⟨rfl, by assumption⟩
  · split at h <;> cases h
    exact ⟨rfl, by assumption⟩
  · split at h
    · cases h; exact (hascii (by assumption)).2.1
    · cases h
  · split at h
    · cases h; exact (hascii (by assumption)).2.2.1
    · cases h
  · split at h
    · cases h; exact (hascii (by assumption)).2.2.2
    · cases h
  · split at h <;> cases h
    exact ⟨rfl, by assumption⟩
  · split at h <;> cases h
    simp only [StringOctets, universalOctets]; exact (decWide_spec (by assumption)).symm
  · split at h <;> cases h
    simp only [StringOctets]; exact (decUtf8_spec (by assumption)).symm
  · split at h <;> cases h
    exact ⟨rfl, by assumption⟩
  · split at h
    · cases h; exact (hascii (by assumption)).1
    · cases h

theorem decOidArcs_spec {rel : Bool} {cs : Octets} {a : List Nat} (h : decOidArcs rel cs = some a) :
    cs = (if rel then relOidContents a else oidContents a) := by
  unfold decOidArcs at h
  split at h
  · rename_i ids _
    cases rel
    · simp only [Bool.false_eq_true, ite_false] at h ⊢
      split at h
      · simp only [Option.ite_none_right_eq_some] at h
        obtain ⟨hc, he⟩ := h; cases he; exact hc.symm
      · cases h
    · simp only [ite_true] at h ⊢
      split at h
      · cases h; exact (by assumption : relOidContents _ = cs).symm
      · cases h
  · cases h

theorem decIri_spec {rel : Bool} {cs : Octets} {a : List String} (h : decIri rel cs = some a) :
    cs = (if rel then relIriContents a else iriContents a) := by
  unfold decIri at h
  split at h
  · cases rel
    · simp only [Bool.false_eq_true, ite_false] at h ⊢
      split at h
      · cases h; exact (by assumption : iriContents _ = cs).symm
      · cases h
    · simp only [ite_true] at h ⊢
      split at h
      · cases h; exact (by assumption : relIriContents _ = cs).symm
      · cases h
  · cases h

theorem utcTimeCanonB_spec {s : List Char} (h : utcTimeCanonB s = true) : UtcTimeCanon s := by
  simp only [utcTimeCanonB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem genTimeCanonB_spec {s : List Char} (h : genTimeCanonB s = true) : GenTimeCanon s := by
  simp only [genTimeCanonB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    List.isEmpty_iff, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hz, hlen⟩, hd, hr⟩ := h
  have hdz : (s.drop 14).getLast? = some 'Z' := by
    rw [List.getLast?_drop]; simp [show ¬ s.length ≤ 14 by omega, hz]
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hdz
  have hdl : (s.drop 14).dropLast = ys := by rw [hys]; simp
  rw [hdl] at hr
  have hs : s = s.take 14 ++ ys ++ ['Z'] := by
    rw [List.append_assoc, ← hys, List.take_append_drop]
  refine ⟨hz, s.take 14, (if ys = [] then [] else ys.drop 1), ?_, by simp; omega, hd, ?_, ?_⟩
  · rcases hr with hr | ⟨⟨⟨hh, hl⟩, hall⟩, hlast⟩
    · subst hr; simpa using hs
    · obtain ⟨zs, rfl⟩ := List.head?_eq_some_iff.mp hh
      have hzs : zs ≠ [] := by intro e; subst e; simp at hl
      simp only [reduceCtorEq, ite_false, List.drop_succ_cons, List.drop_zero, hzs]
      exact hs
  · split
    · rfl
    · rcases hr with hr | ⟨⟨_, hall⟩, _⟩
      · contradiction
      · exact hall
  · split
    · simp
    · rcases hr with hr | ⟨⟨⟨hh, hl⟩, _⟩, hlast⟩
      · contradiction
      · obtain ⟨zs, rfl⟩ := List.head?_eq_some_iff.mp hh
        have hzs : zs ≠ [] := by intro e; subst e; simp at hl
        simp only [List.drop_succ_cons, List.drop_zero]
        obtain ⟨z, zs', rfl⟩ := List.exists_cons_of_ne_nil hzs
        simpa using hlast

theorem decTime_spec {p : Profile} {k : TimeKind} {cs : Octets} {w : TimeV} (h : decTime p k cs = .ok w) :
    TimeContents p k w cs := by
  unfold decTime at h
  split at h
  · cases h
  rename_i chars hchars
  dsimp only at h
  split at h
  · cases h
  rename_i w' hparse
  split at h
  · cases h
  rename_i hwf
  split at h
  · cases h
  rename_i hstrip
  split at h
  · cases h
  rename_i hutf
  split at h
  · cases h
  rename_i hcanon
  cases h
  unfold TimeContents
  split
  · rename_i hr
    simp only [hr, Bool.true_and, bne_iff_ne, ne_eq, Decidable.not_not] at hcanon
    exact hcanon.symm
  · refine ⟨_, ⟨_, hparse, by simpa using hwf, rfl⟩, ?_⟩
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hutf
    exact hutf.symm

/-! ## REAL (8.5, 11.3) -/

theorem andNot_true {a b : Bool} (h : ¬(a && !b) = true) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem Char.toNat_ofNat_lt (n : Nat) (h : n < 128) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat, UInt32.toNat]

theorem expFieldB_spec {e : Int} {fmt : Nat} {os : Octets} (h : expFieldB e fmt os = true) :
    ExpField e fmt os := by
  match fmt, h with
  | 0, h | 1, h | 2, h =>
    simp only [expFieldB, Bool.and_eq_true, beq_iff_eq] at h; exact h
  | 3, h =>
    cases os with
    | nil => simp [expFieldB] at h
    | cons x ex =>
      simp only [expFieldB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      exact ⟨x.val, ex, by rw [octet_val], h1, by have := x.isLt; omega, h2, h3, h4⟩
  | k + 4, h => simp [expFieldB] at h

theorem realSplit_append {fmt : Nat} {rest : Octets} (h : (realSplit fmt rest).2 ≠ []) :
    (realSplit fmt rest).1 ++ (realSplit fmt rest).2 = rest := by
  unfold realSplit at h ⊢
  split
  · simp
  · simp at h
  · simp

theorem nr3CanonB_spec {q : ℚ} {s : List Char} (h : nr3CanonB q s = true) : Nr3Canon q s := by
  unfold nr3CanonB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨_, _, _, of_decide_eq_true h1, by simpa using h2, of_decide_eq_true h3, eq_of_beq h4⟩

theorem decReal_spec {p : Profile} {cs : Octets} {r : RealVal} (h : decReal p cs = .ok r) :
    RealContents p r cs := by
  cases cs with
  | nil => simp only [decReal, Except.ok.injEq] at h; subst h; rfl
  | cons o rest =>
    simp only [decReal] at h
    have ho := o.isLt
    split at h
    · -- binary
      rename_i hb
      split at h
      · cases h
      rename_i hbb
      split at h
      · cases h
      rename_i hnn
      split at h
      · cases h
      rename_i hexp
      split at h
      · cases h
      rename_i hres
      cases h
      simp only [Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_or] at hnn
      simp only [Bool.not_eq_true'] at hexp
      refine ⟨o.val / 64 % 2 == 1, o.val / 16 % 4, o.val / 4 % 4,
        tcValue (bitsOf (realExpOctets (o.val % 4) (realSplit (o.val % 4) rest).1)),
        nnbValue (bitsOf (realSplit (o.val % 4) rest).2), o.val % 4, (realSplit (o.val % 4) rest).1,
        (realSplit (o.val % 4) rest).2, by omega, by omega, Nat.pos_of_ne_zero hnn.2, rfl, ?_, hnn.1, rfl, ?_⟩
      · refine List.cons_eq_cons.mpr ⟨?_, (realSplit_append hnn.1).symm⟩
        apply Fin.ext
        by_cases hn : o.val / 64 % 2 = 1 <;> simp [octet, hn] <;> omega
      · split
        · rename_i hr
          have hres := andNot_true hres hr
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hres
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hres
          exact ⟨h1, h2, h3, h4, h5⟩
        · exact expFieldB_spec (by simpa using hexp)
    · split at h
      · -- 8.5.9
        rename_i hb h64
        split at h
        · cases h
        rename_i hemp
        have hemp' : rest = [] := by simpa using hemp
        subst hemp'
        split at h <;> (try cases h) <;> (rename_i hv; show [o] = [octet _]; congr 1; apply Fin.ext; simp [octet, hv])
      · -- 8.5.8
        rename_i hb h64
        split at h
        · cases h
        rename_i hform
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, not_lt] at hform
        obtain ⟨⟨hall, h1⟩, h3⟩ := hform
        split at h
        · rename_i q hq
          split at h
          · cases h
          split at h
          · cases h
          rename_i hres
          cases h
          have hlt : o.val < 64 := by omega
          refine ⟨o.val % 64, rest.map fun c => Char.ofNat c.val, ?_, ?_, by omega, by omega, hq, ?_⟩
          · congr 1
            · apply Fin.ext; show o.val = (o.val % 64) % 256; omega
            · simp only [List.map_map]
              conv_lhs => rw [← List.map_id rest]
              apply List.map_congr_left
              intro c hc
              have : c.val < 128 := by
                have hall' : ∀ x ∈ rest, x.val < 128 := by simpa using hall
                exact hall' c hc
              simp only [Function.comp_apply, id, Char.toNat_ofNat_lt _ this, octet_val]
          · intro c hc
            obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
            have : c'.val < 128 := by
              have hall' : ∀ x ∈ rest, x.val < 128 := by simpa using hall
              exact hall' c' hc'
            rw [Char.toNat_ofNat_lt _ this]; exact this
          · intro hr
            have hres := andNot_true hres hr
            simp only [Bool.and_eq_true, beq_iff_eq] at hres
            exact ⟨hres.1, nr3CanonB_spec hres.2⟩
        · cases h

/-! ## Default values (X.680 25.12, X.690 11.5) -/

theorem evalLit_spec (E : Env) : ∀ (n : Nat) (sc : Scope) (d d' w : Val),
    evalLit E n sc d = some d' → evalVal E n sc d w → w = d'
  | 0, _, _, _, _, h, _ => by simp [evalLit] at h
  | n + 1, sc, d, d', w, h, hv => by
    cases d with
    | ref mn name args =>
      simp only [evalLit] at h
      simp only [evalVal] at hv
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      rw [hr] at hv
      exact evalLit_spec E n sc' v d' w h hv
    | bool _ | int _ | enum _ | oid _ | chars _ | octets _ | bits _ =>
      simp only [evalLit, Option.some.injEq] at h
      simp only [evalVal] at hv
      rw [hv, h]
    | _ => simp [evalLit] at h

theorem eqIsEq_spec (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    eqIsEq E n sc t = true → eqv E n sc t x y → x = y
  | 0, _, _, _, _, h, _ => by simp [eqIsEq] at h
  | n + 1, sc, t, x, y, h, hv => by
    cases t with
    | ref name =>
      simp only [eqIsEq] at h; simp only [eqv] at hv
      split at h
      · rename_i sc' t' hr; rw [hr] at hv; exact eqIsEq_spec E n sc' t' x y h hv
      · cases h
    | extRef mn name =>
      simp only [eqIsEq] at h; simp only [eqv] at hv
      split at h
      · rename_i sc' t' hr; rw [hr] at hv; exact eqIsEq_spec E n sc' t' x y h hv
      · cases h
    | paramRef mn name args =>
      simp only [eqIsEq] at h; simp only [eqv] at hv
      split at h
      · rename_i sc' t' hr; rw [hr] at hv; exact eqIsEq_spec E n sc' t' x y h hv
      · cases h
    | tagged tg k t =>
      simp only [eqIsEq] at h; simp only [eqv] at hv; exact eqIsEq_spec E n sc t x y h hv
    | constrained t c =>
      simp only [eqIsEq] at h; simp only [eqv] at hv; exact eqIsEq_spec E n sc t x y h hv
    | bitString named =>
      simp only [eqIsEq, List.isEmpty_iff] at h
      simp only [eqv] at hv
      split at hv
      · simp only [h, ite_true] at hv; rw [hv]
      · exact hv.elim
    | boolean | integer _ | enumerated _ _ | null | objectIdentifier | relativeOid | octetString
    | restricted _ | utcTime | generalizedTime =>
      simpa [eqv] using hv
    | _ => simp [eqIsEq] at h

theorem litNeq_spec : ∀ (x y : Val), litNeq x y = true → x ≠ y := by
  intro x y h
  cases x <;> cases y <;> simp_all [litNeq]

theorem notDefaultB_spec {E : Env} {n : Nat} {en : Entry} {x : Val} (h : notDefaultB E n en x = true) :
    ¬ IsDefault E n en x := by
  unfold notDefaultB at h
  unfold IsDefault
  split at h
  · rename_i d hd
    rw [hd]
    split at h
    · rename_i d' hl
      simp only [Bool.and_eq_true] at h
      rintro ⟨d'', hev, heq⟩
      have := evalLit_spec E n _ _ _ _ hl hev
      subst this
      exact litNeq_spec _ _ h.2 (eqIsEq_spec E n _ _ _ _ h.1 heq)
    · cases h
  · rename_i hd
    split
    · rename_i d hd'; exact absurd hd' (hd d)
    · exact id

/-! ## Components (8.9, 8.11) -/

/-- The value's components, from the decoded components. -/
def resVals (res : List ((Entry × Ty) × Node × Val)) : List (String × Val) :=
  res.map fun r => (r.1.1.name, r.2.2)

theorem lookup_none_of_not_mem {k : String} {res : List ((Entry × Ty) × Node × Val)}
    (h : k ∉ res.map (·.1.1.name)) : (resVals res).lookup k = none := by
  rw [resVals, List.lookup_eq_none_iff]
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  simp only [bne_iff_ne, ne_eq]
  intro he; exact h (List.mem_map.mpr ⟨r, hr, he.symm⟩)

theorem compFilter_eq : ∀ (comps : List (Entry × Ty)) (res : List ((Entry × Ty) × Node × Val)),
    (res.map (·.1)).Sublist comps → (comps.map (·.1.name)).Nodup →
    (comps.zip (comps.map fun c => (resVals res).lookup c.1.name)).filterMap
        (fun (c, o) => o.map (c, ·)) = res.map fun r => (r.1, r.2.2)
  | [], res, hsub, _ => by
    have : res = [] := by simpa using List.sublist_nil.mp hsub
    subst this; rfl
  | c :: comps', res, hsub, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hc, hnd'⟩ := hnd
    rcases List.sublist_cons_iff.mp hsub with hs | ⟨l, hl, hs⟩
    · -- `c` is not encoded
      have hnot : c.1.name ∉ res.map (·.1.1.name) := by
        intro hm
        obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
        exact hc ⟨r.1, hs.subset (List.mem_map.mpr ⟨r, hr, rfl⟩), he⟩
      simp only [List.map_cons, List.zip_cons_cons, lookup_none_of_not_mem hnot, List.filterMap_cons,
        Option.map_none]
      exact compFilter_eq comps' res hs hnd'
    · -- `c` is the first encoded
      cases res with
      | nil => simp at hl
      | cons r res' =>
        simp only [List.map_cons, List.cons.injEq] at hl
        obtain ⟨hrc, rfl⟩ := hl
        have hlk : (resVals (r :: res')).lookup c.1.name = some r.2.2 := by
          simp [resVals, hrc]
        have hrest : (comps'.map fun c' => (resVals (r :: res')).lookup c'.1.name) =
            comps'.map fun c' => (resVals res').lookup c'.1.name := by
          apply List.map_congr_left
          intro c' hc'
          have hne : (c'.1.name == r.1.1.name) = false := by
            rw [hrc]; simp only [beq_eq_false_iff_ne, ne_eq]
            intro he; exact hc ⟨c', hc', he⟩
          simp only [resVals, List.map_cons, List.lookup_cons, hne]
        simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
        rw [hlk]
        simp only [Option.map_some]
        rw [hrest, compFilter_eq comps' res' hs hnd', hrc]

theorem compEncs_of_sublist {E : Env} {p : Profile} {n : Nat} {comps : List (Entry × Ty)}
    {enc : Scope → Ty → Val → Node → Prop} (res : List ((Entry × Ty) × Node × Val))
    (hsub : (res.map (·.1)).Sublist comps) (hnd : (comps.map (·.1.name)).Nodup)
    (henc : ∀ r ∈ res, enc r.1.1.scope r.1.2 r.2.2 r.2.1)
    (hdef : p.restricted = true → ∀ c ∈ comps, ∀ x, (resVals res).lookup c.1.name = some x →
      ¬ IsDefault E n c.1 x) :
    CompEncs E p n comps (resVals res) enc (res.map fun r => (r.1, r.2.1)) := by
  refine ⟨?_, comps.map fun c => (resVals res).lookup c.1.name, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact List.mem_map.mpr ⟨r.1, hsub.subset (List.mem_map.mpr ⟨r, hr, rfl⟩), rfl⟩
  · rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun c hc => ?_
    unfold CompChoice
    split
    · rename_i x hx
      exact ⟨rfl, fun hr => hdef hr c hc x hx⟩
    · rename_i hx
      simp
  · rw [compFilter_eq comps res hsub hnd, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun r hr => ⟨rfl, henc r hr⟩

theorem resVals_cons (r : (Entry × Ty) × Node × Val) (res : List ((Entry × Ty) × Node × Val)) :
    resVals (r :: res) = (r.1.1.name, r.2.2) :: resVals res := rfl

theorem decSeqComps_spec {β : Type} {E : Env} {n : Nat} {rec : DFrame → Scope → Ty → Node → Except String Val}
    {all : List (String × Scope × Ty)} {fin : List (String × Val) → Except String β} {b : β} :
    ∀ (comps : List (Entry × Ty)) (ch : List Node) (acc : List (String × Val)),
      decSeqComps E n rec all fin comps ch acc = .ok b →
      ∃ res : List ((Entry × Ty) × Node × Val), fin (acc ++ resVals res) = .ok b ∧
        (res.map (·.1)).Sublist comps ∧ res.map (·.2.1) = ch ∧
        ∀ r ∈ res, ∃ fr, rec fr r.1.1.scope r.1.2 r.2.1 = .ok r.2.2
  | [], [], acc, h => by
    simp only [decSeqComps] at h
    exact ⟨[], by simpa [resVals] using h, by simp, rfl, by simp⟩
  | [], nd :: _, acc, h => by simp [decSeqComps] at h
  | (en, ty) :: comps, [], acc, h => by
    simp only [decSeqComps] at h
    obtain ⟨res, h1, h2, h3, h4⟩ := decSeqComps_spec comps [] _ h
    exact ⟨res, h1, h2.cons _, h3, h4⟩
  | (en, ty) :: comps, nd :: rest, acc, h => by
    have skip : decSeqComps E n rec all fin comps (nd :: rest) acc = .ok b →
        ∃ res : List ((Entry × Ty) × Node × Val), fin (acc ++ resVals res) = .ok b ∧
          (res.map (·.1)).Sublist ((en, ty) :: comps) ∧ res.map (·.2.1) = nd :: rest ∧
          ∀ r ∈ res, ∃ fr, rec fr r.1.1.scope r.1.2 r.2.1 = .ok r.2.2 := fun hs => by
      obtain ⟨res, h1, h2, h3, h4⟩ := decSeqComps_spec comps (nd :: rest) _ hs
      exact ⟨res, h1, h2.cons _, h3, h4⟩
    simp only [decSeqComps] at h
    split at h
    · split at h
      · rename_i r hr
        cases h
        obtain ⟨x, hx, h⟩ := except_bind_ok hr
        obtain ⟨res, h1, h2, h3, h4⟩ := decSeqComps_spec comps rest _ h
        refine ⟨((en, ty), nd, x) :: res, ?_, ?_, ?_, ?_⟩
        · rw [resVals_cons]; simpa using h1
        · simpa using h2
        · simp [h3]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨_, hx⟩
          · exact h4 r hr
      · split at h
        · cases h; exact skip ‹_›
        · cases h
    · exact skip h

theorem ite_err_ok {α : Type} {c : Bool} {m : String} {x : Except String α} {v : α}
    (h : (if c = true then Except.error m else x) = .ok v) : c = false ∧ x = .ok v := by
  cases c <;> simp_all

theorem firstOk_spec {α β : Type} {f : α → Except String β} {err : String} :
    ∀ {l : List α} {b : β}, firstOk f err l = .ok b → ∃ a ∈ l, f a = .ok b
  | [], _, h => by simp [firstOk] at h
  | a :: rest, b, h => by
    simp only [firstOk] at h
    split at h
    · cases h; exact ⟨a, List.mem_cons_self .., ‹_›⟩
    · split at h
      · cases h
        obtain ⟨a', ha', h'⟩ := firstOk_spec ‹_›
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
      · cases h

theorem setSearch_spec {L : Nat} {β : Type} {cand : Node → List (Fin L)} {k : List (Fin L × Node) → Except String β}
    {b : β} : ∀ (ch : List Node) (acc : List (Fin L × Node)), setSearch cand k ch acc = .ok b →
      ∃ ext : List (Fin L × Node), ext.map (·.2) = ch ∧ k (acc.reverse ++ ext) = .ok b
  | [], acc, h => ⟨[], rfl, by simpa [setSearch] using h⟩
  | nd :: rest, acc, h => by
    simp only [setSearch] at h
    obtain ⟨i, _, hi⟩ := firstOk_spec h
    obtain ⟨ext, h1, h2⟩ := setSearch_spec rest _ hi
    exact ⟨(i, nd) :: ext, by simp [h1], by simpa using h2⟩

theorem bfalse {b : Bool} (h : ¬b = true) : b = false := by cases b <;> simp_all

theorem restricted_universalTag (k : StrType) : ∃ tg, (Ty.restricted k).universalTag? = some tg := by
  cases k <;> exact ⟨_, rfl⟩

theorem Node.retag_eq_self {nd : Node} {tg : Tag} (h : nd.tag = tg) : nd.retag tg = nd := by
  subst h; exact Node.retag_tag nd

theorem ber_time {E : Env} {p : Profile} {n : Nat} {sc : Scope} {t : Ty} {k : TimeKind} {u : Nat}
    {tg : Tag} {len : LenForm} {cs : Octets} {w : TimeV} (hk : timeKind? t = some k)
    (hu : t.universalTag? = some u) (htg : tg = univ u) (hw : TimeContents p k w cs) :
    ber E p (n + 1) sc t (.time w) (.prim tg len cs) := by
  subst htg
  cases t <;> simp only [timeKind?, reduceCtorEq, Option.some.injEq] at hk
  all_goals (subst hk; simp only [ber, hu, timeKind?]; exact ⟨len, cs, rfl, hw⟩)

theorem defaultErr_none {E : Env} {n : Nat} {comps : List (Entry × Ty)} {cs : List (String × Val)}
    (h : defaultErr E n comps cs = none) :
    ∀ c ∈ comps, ∀ x, cs.lookup c.1.name = some x → ¬ IsDefault E n c.1 x := by
  unfold defaultErr at h
  split at h
  · split at h <;> cases h
  · rename_i hf
    intro c hc x hx
    have := List.find?_eq_none.mp hf c hc
    simp only [hx, Bool.not_eq_true'] at this
    exact notDefaultB_spec (by simpa using this)

theorem forall₂_snd {α β : Type} {R : α → β × α → Prop} (hR : ∀ a b, R a b → b.2 = a) :
    ∀ {l1 : List α} {l2 : List (β × α)}, List.Forall₂ R l1 l2 → l2.map (·.2) = l1
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, hR _ _ h, forall₂_snd hR hs]

/-- The decoded components of a SET, in the order of the type. -/
theorem set_res {β : Type} {C : β → Entry × Ty} {nodeOf : β → Node} {D : β → Except String Val} :
    ∀ {srt : List β} {cs : List (String × Val)},
      List.Forall₂ (fun a q => (do let x ← D a; Except.ok ((C a).1.name, x)) = Except.ok q) srt cs →
      ∃ res : List ((Entry × Ty) × Node × Val),
        res.map (fun r => (r.1, r.2.1)) = srt.map (fun a => (C a, nodeOf a)) ∧ resVals res = cs ∧
        ∀ r ∈ res, ∃ a ∈ srt, r.1 = C a ∧ r.2.1 = nodeOf a ∧ D a = .ok r.2.2
  | _, _, .nil => ⟨[], rfl, rfl, by simp⟩
  | a :: srt, q :: cs, .cons h hs => by
    obtain ⟨x, hx, h⟩ := except_bind_ok h
    cases h
    obtain ⟨res, h1, h2, h3⟩ := set_res (nodeOf := nodeOf) hs
    refine ⟨(C a, nodeOf a, x) :: res, by simp [h1], by rw [resVals_cons, h2], ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨a, List.mem_cons_self .., rfl, rfl, hx⟩
    · obtain ⟨b, hb, h⟩ := h3 r hr
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-! ## EXTERNAL (8.18) -/

theorem extTake_spec (P : Node → Bool) (l : List Node) :
    (extTake P l).1 ++ (extTake P l).2 = l ∧
      ((extTake P l).1 = [] ∨ ∃ c, (extTake P l).1 = [c] ∧ P c = true) := by
  cases l with
  | nil => exact ⟨rfl, Or.inl rfl⟩
  | cons c rest =>
    simp only [extTake]
    split
    · exact ⟨rfl, Or.inr ⟨c, rfl, by assumption⟩⟩
    · exact ⟨rfl, Or.inl rfl⟩

theorem extOid_spec {dr : List Node} {o : Option (List Nat)} (h : extOid dr = .ok o)
    (hs : dr = [] ∨ ∃ c, dr = [c] ∧ isPrimWith (univ 6) c = true) :
    (∀ a, o = some a → ∃ x, dr = [x] ∧ Prim (univ 6) (· = oidContents a) x) ∧ (o = none → dr = []) := by
  rcases hs with rfl | ⟨c, rfl, hc⟩
  · simp only [extOid, Except.ok.injEq] at h; subst h; simp
  · cases c with
    | cons => simp [isPrimWith] at hc
    | prim tg f cs =>
      simp only [isPrimWith, beq_iff_eq] at hc
      subst hc
      simp only [extOid] at h
      split at h
      · rename_i a ha
        cases h
        exact ⟨fun a' e => by cases e; exact ⟨_, rfl, f, cs, rfl, by simpa using decOidArcs_spec ha⟩,
          fun e => by cases e⟩
      · cases h

theorem extInt_spec {ir : List Node} {i : Option Int} (h : extInt ir = .ok i)
    (hs : ir = [] ∨ ∃ c, ir = [c] ∧ isPrimWith (univ 2) c = true) :
    (∀ k, i = some k → ∃ x, ir = [x] ∧ Prim (univ 2) (IntContents k) x) ∧ (i = none → ir = []) := by
  rcases hs with rfl | ⟨c, rfl, hc⟩
  · simp only [extInt, Except.ok.injEq] at h; subst h; simp
  · cases c with
    | cons => simp [isPrimWith] at hc
    | prim tg f cs =>
      simp only [isPrimWith, beq_iff_eq] at hc
      subst hc
      simp only [extInt, intOrErr] at h
      split at h
      · rename_i hi
        cases h
        exact ⟨fun k e => by cases e; exact ⟨_, rfl, f, cs, rfl, intContentsB_spec hi⟩, fun e => by cases e⟩
      · cases h

theorem extId_spec {o : Option (List Nat)} {i : Option Int} {id : Val} (h : extId o i = .ok id) :
    externalRefs id = some (o, i) := by
  cases o <;> cases i <;> simp only [extId, Except.ok.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem extData_spec {p : Profile} {n : Nat} {enc : Node} {dv : Octets} (h : extData p n enc = .ok dv) :
    ExternalEncoding p n dv enc := by
  unfold extData at h
  split at h
  · rename_i f inner
    split at h
    · cases h; exact Or.inl ⟨f, inner, rfl, rfl, lenOkB_spec p _ ‹_›⟩
    · cases h
  · exact Or.inr (Or.inl ⟨_, decOctets_spec p n _ _ _ h, by rw [Node.retag_retag]; rfl⟩)
  · exact Or.inr (Or.inl ⟨_, decOctets_spec p n _ _ _ h, by rw [Node.retag_retag]; rfl⟩)
  · rename_i f cs
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    split at h
    · cases h
      refine Or.inr (Or.inr ⟨(Node.prim ⟨.context, 2⟩ f cs).retag (univ 3), ?_, rfl⟩)
      rw [bitsOf_bitsToOctets _ ‹_›]; exact decBits_spec p n _ _ _ _ hbs
    · cases h
  · rename_i f cs
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    split at h
    · cases h
      refine Or.inr (Or.inr ⟨(Node.cons ⟨.context, 2⟩ f cs).retag (univ 3), ?_, rfl⟩)
      rw [bitsOf_bitsToOctets _ ‹_›]; exact decBits_spec p n _ _ _ _ hbs
    · cases h
  · cases h

/-! ## The decoder is sound -/

set_option maxHeartbeats 4000000 in
/-- What `dec` returns, `ber` relates to the encoding: `nd` is an encoding of `v` under `p`. -/
theorem dec_sound (E : Env) (p : Profile) : ∀ (n : Nat) (frames : List DFrame) (hint : Option (Scope × Ty))
    (sc : Scope) (t : Ty) (nd : Node) (v : Val), dec E p n frames hint sc t nd = .ok v → ber E p n sc t v nd
  | 0, _, _, _, _, _, _, h => by simp [dec] at h
  | n + 1, frames, hint, sc, t, nd, v, h => by
    have IH : ∀ {fr hi sc t nd v}, dec E p n fr hi sc t nd = .ok v → ber E p n sc t v nd :=
      fun h => dec_sound E p n _ _ _ _ _ _ h
    unfold dec at h
    split at h
    all_goals try (have hn := Nat.succ_injective (by assumption : n + 1 = _); subst hn)
    next => cases h
    next => -- BOOLEAN
      split at h
      · cases h
      · rename_i hc; cases h
        exact ⟨_, _, rfl, boolContents_dec p _ (bfalse hc)⟩
    next => -- INTEGER
      split at h
      · cases h; exact ⟨_, _, rfl, intContentsB_spec ‹_›⟩
      · cases h
    next => -- ENUMERATED
      split at h
      · cases h
      · rename_i hi
        dsimp only at h
        split at h
        · obtain ⟨hb, rfl⟩ := guardE_ok h
          exact ⟨_, by simpa using hb, _, _, rfl, intContentsB_spec (by simpa using hi)⟩
        · cases h
    next => -- REAL
      obtain ⟨r, hr, rfl⟩ := except_map_ok h
      exact ⟨_, _, rfl, decReal_spec hr⟩
    next => -- BIT STRING
      obtain ⟨bs, hbs, h⟩ := except_bind_ok h
      split at h
      · cases h
      · rename_i hc; cases h
        refine ⟨bs, ?_, decBits_spec p _ _ _ _ _ hbs⟩
        split
        · rfl
        · rename_i hn
          split
          · rename_i hr
            have := bfalse hc
            simp only [hr,
              Bool.and_eq_false_imp] at this
            simpa [hn] using this
          · rfl
    next => -- OCTET STRING
      obtain ⟨os, hos, rfl⟩ := except_map_ok h
      exact decOctets_spec p _ _ _ _ hos
    next => -- NULL
      cases h; exact ⟨_, _, rfl, rfl⟩
    next => -- SEQUENCE
      rename_i r e r2 len ch _
      dsimp only at h
      split at h
      · cases h
      rename_i hnd
      obtain ⟨res, h1, h2, h3, h4⟩ := decSeqComps_spec _ _ _ h
      simp only [List.nil_append] at h1
      split at h1
      · cases h1
      rename_i hne
      cases h1
      refine ⟨len, res.map fun r => (r.1, r.2.1), ?_, compEncs_of_sublist (E := E) (p := p) (n := n) res h2
        (by simpa using hnd) (fun r hr => by obtain ⟨fr, hfr⟩ := h4 r hr; exact IH hfr) ?_⟩
      · simp only [List.map_map]; rw [← h3]; rfl
      · intro hr
        apply defaultErr_none
        cases hd : defaultErr E n _ (resVals res)
        · rfl
        · exact (hne _ hr hd).elim
    next => -- SEQUENCE OF
      obtain ⟨vs, hvs, rfl⟩ := except_map_ok h
      exact ⟨_, _, rfl, ((mapM_ok hvs).imp fun _ _ hh => IH hh).flip⟩
    next => -- SET
      rename_i sc _ _ _ _ _ _ r e r2 len ch _
      dsimp only at h
      split at h
      · cases h
      rename_i hnd
      obtain ⟨found, hch, h⟩ := setSearch_spec _ _ h
      simp only [List.reverse_nil, List.nil_append] at h
      beta_reduce at h
      obtain ⟨hpw, h⟩ := ite_err_ok h
      obtain ⟨cs, hcs, h⟩ := except_bind_ok h
      obtain ⟨hder, h⟩ := ite_err_ok h
      obtain ⟨hcer, h⟩ := ite_err_ok h
      have hder := ne_true_of_eq_false hder
      have hcer := ne_true_of_eq_false hcer
      split at h
      · cases h
      rename_i hne
      cases h
      obtain ⟨res, hres1, hres2, hres3⟩ := set_res (nodeOf := fun a => a.2) (mapM_ok hcs)
      have hsub : (res.map (·.1)).Sublist (compTys E n sc r e r2) := by
        have := congrArg (List.map Prod.fst) hres1
        simp only [List.map_map] at this
        rw [show (res.map (·.1)) = _ from this]
        have hpw' := sortedB_pairwise' (R := fun (a b : Fin (compTys E n sc r e r2).length) => a < b)
          (fun a b h => of_decide_eq_true h) (fun a b c => lt_trans) (by simpa using hpw)
        have hs := List.map_getElem_sublist hpw'
        simp only [List.map_map] at hs
        exact hs
      refine ⟨len, found.map fun a => ((compTys E n sc r e r2)[a.1], a.2), res.map fun r => (r.1, r.2.1),
        ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_map]; rw [← hch]; rfl
      · rw [← hres2]
        refine compEncs_of_sublist (E := E) (p := p) (n := n) res hsub (by simpa using hnd) ?_ ?_
        · intro r hr
          obtain ⟨a, _, h1, h2, h3⟩ := hres3 r hr
          rw [h1, h2]; exact IH h3
        · intro hr
          apply defaultErr_none
          cases hd : defaultErr E n _ (resVals res)
          · rfl
          · rw [hres2] at hd; exact (hne _ hr hd).elim
      · rw [hres1]; exact ((List.mergeSort_perm found _).map _).symm
      · intro hd
        have := sortedB_pairwise' (R := fun a b : Node => Tag.lt a.tag b.tag = true) (fun _ _ h => h)
          (fun a b c => Tag.lt_trans a.tag b.tag c.tag) (andNot_true hder (by simp [hd]))
        rw [← hch, List.pairwise_map] at this
        rw [List.pairwise_map]; exact this
      · intro hc
        have hs := andNot_true hcer (by simp [hc])
        let key : Fin (compTys E n sc r e r2).length × Node → Tag := fun a =>
          (cerKey E n (compTys E n sc r e r2)[a.1].1.scope (compTys E n sc r e r2)[a.1].2).getD a.2.tag
        have := sortedB_pairwise' (R := fun a b => Tag.lt (key a) (key b) = true) (fun _ _ h => h)
          (fun a b c => Tag.lt_trans (key a) (key b) (key c)) hs
        rw [List.pairwise_map]; exact this
    next => -- SET OF
      obtain ⟨vs, hvs, h⟩ := except_bind_ok h
      split at h
      · cases h
      rename_i hc
      cases h
      refine ⟨_, _, _, rfl, ((mapM_ok hvs).imp fun _ _ hh => IH hh).flip, List.Perm.refl _, fun hr => ?_⟩
      have := andNot_true hc hr
      exact sortedB_pairwise' (R := fun (a b : Node) => octLe a.octets b.octets)
        (fun a b h => octLeB_spec a.octets b.octets h) (fun a b c => octLe_trans a.octets b.octets c.octets) this
    next => -- CHOICE
      obtain ⟨alt, hmem, h⟩ := firstOk_spec h
      obtain ⟨x, hx, rfl⟩ := except_map_ok h
      exact ⟨alt, (List.mem_filter.mp hmem).1, rfl, IH hx⟩
    next => -- selection
      simp only [ber]
      split at h
      · rename_i sc' root ext hb
        rw [hb]; dsimp only
        split at h
        · rename_i alt ha; rw [ha]; exact IH h
        · cases h
      · cases h
    next => -- OBJECT IDENTIFIER
      split at h
      · rename_i a ha; cases h; exact ⟨_, _, rfl, by simpa using decOidArcs_spec ha⟩
      · cases h
    next => -- RELATIVE-OID
      split at h
      · rename_i a ha; cases h; exact ⟨_, _, rfl, by simpa using decOidArcs_spec ha⟩
      · cases h
    next => -- OID-IRI
      split at h
      · rename_i a ha; cases h; exact ⟨_, _, rfl, by simpa using decIri_spec ha⟩
      · cases h
    next => -- RELATIVE-OID-IRI
      split at h
      · rename_i a ha; cases h; exact ⟨_, _, rfl, by simpa using decIri_spec ha⟩
      · cases h
    next => exact IH h -- EMBEDDED PDV
    next => exact IH h -- CHARACTER STRING
    next => -- EXTERNAL
      rename_i len ch _
      dsimp only at h
      obtain ⟨enc, henc, h⟩ := except_bind_ok h
      obtain ⟨o, ho, h⟩ := except_bind_ok h
      obtain ⟨i, hi, h⟩ := except_bind_ok h
      obtain ⟨id, hid, h⟩ := except_bind_ok h
      obtain ⟨d, hd, h⟩ := except_bind_ok h
      obtain ⟨dv, hdv, h⟩ := except_bind_ok h
      cases h
      have e1 := extTake_spec (isPrimWith (univ 6)) ch
      have e2 := extTake_spec (isPrimWith (univ 2)) (extTake (isPrimWith (univ 6)) ch).2
      have e3 := extTake_spec (fun c => c.tag == univ 7)
        (extTake (isPrimWith (univ 2)) (extTake (isPrimWith (univ 6)) ch).2).2
      have hs3 : (extTake (fun c => c.tag == univ 7)
          (extTake (isPrimWith (univ 2)) (extTake (isPrimWith (univ 6)) ch).2).2).2 = [enc] := by
        unfold extEnc at henc
        split at henc
        · cases henc; assumption
        · cases henc
      simp only [ber, extVal]
      refine ⟨len, id, d, dv, (o, i), by simp, by cases d <;> rfl, by cases d <;> rfl, extId_spec hid,
        (extTake (isPrimWith (univ 6)) ch).1, (extTake (isPrimWith (univ 2)) (extTake (isPrimWith (univ 6)) ch).2).1,
        (extTake (fun c => c.tag == univ 7) (extTake (isPrimWith (univ 2)) (extTake (isPrimWith (univ 6)) ch).2).2).1,
        enc, ?_, ?_, ?_, ?_, extData_spec hdv⟩
      · rw [← hs3, List.append_assoc, List.append_assoc, e3.1, e2.1, e1.1]; rfl
      · have := extOid_spec ho e1.2
        cases o
        · exact this.2 rfl
        · exact this.1 _ rfl
      · have := extInt_spec hi e2.2
        cases i
        · exact this.2 rfl
        · exact this.1 _ rfl
      · rcases e3.2 with h3 | ⟨c, h3, _⟩
        · rw [h3] at hd; simp only [extDesc, Except.ok.injEq] at hd; subst hd; exact h3
        · rw [h3] at hd
          obtain ⟨x, hx, rfl⟩ := except_map_ok hd
          exact ⟨c, h3, IH hx⟩
    next => -- restricted character strings
      rename_i k _
      obtain ⟨tg, htg⟩ := restricted_universalTag k
      dsimp only at h
      rw [htg] at h
      obtain ⟨os, hos, h⟩ := except_bind_ok h
      exact ⟨os, decString_spec h, tg, htg, decOctets_spec p _ _ _ _ hos⟩
    next => -- GeneralizedTime
      obtain ⟨os, hos, h⟩ := except_bind_ok h
      obtain ⟨x, hx, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨hb, rfl⟩ := guardE_ok h
        refine ⟨fun hr => genTimeCanonB_spec (by simpa [hr] using hb), os, decString_spec hx,
          decOctets_spec p _ _ _ _ hos⟩
      · cases h
    next => -- UTCTime
      obtain ⟨os, hos, h⟩ := except_bind_ok h
      obtain ⟨x, hx, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨hb, rfl⟩ := guardE_ok h
        refine ⟨fun hr => utcTimeCanonB_spec (by simpa [hr] using hb), os, decString_spec hx,
          decOctets_spec p _ _ _ _ hos⟩
      · cases h
    next => -- ObjectDescriptor
      obtain ⟨os, hos, h⟩ := except_bind_ok h
      exact ⟨os, decString_spec h, decOctets_spec p _ _ _ _ hos⟩
    next => -- references
      simp only [ber]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact IH h
      · cases h
    next =>
      simp only [ber]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact IH h
      · cases h
    next =>
      simp only [ber]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact IH h
      · cases h
    next => -- tagging
      split at h
      · rename_i hx
        split at h
        · rename_i tg' f c
          split at h
          · rename_i heq
            refine ⟨c, IH h, ?_⟩
            simp only [hx, ↓reduceIte, eq_of_beq heq]; exact ⟨f, rfl⟩
          · cases h
        · cases h
      · rename_i hx
        split at h
        · cases h
        · rename_i htg
          split at h
          · refine ⟨_, IH h, ?_⟩
            simp only [hx, Bool.false_eq_true, ↓reduceIte, Node.retag_retag]
            exact (Node.retag_eq_self (by simpa using htg)).symm
          · cases h
    next => -- constraints
      obtain ⟨v0, hv0, h⟩ := except_bind_ok h
      have : v = v0 := by
        dsimp only at h
        repeat' split at h
        all_goals first | (cases h <;> rfl) | (obtain ⟨_, rfl⟩ := guardE_ok h; rfl)
      subst this; exact IH hv0
    next => -- open type
      split at h
      · obtain ⟨w, hw, h⟩ := except_bind_ok h
        split at h
        · cases h; exact ⟨_, IH hw⟩
        · cases h
      · split at h
        · obtain ⟨w, hw, rfl⟩ := except_map_ok h; exact ⟨_, IH hw⟩
        · cases h
    next => -- class field
      simp only [ber]
      split at h
      all_goals (try cases h)
      all_goals (rename_i hb; rw [hb]; exact IH h)
    next => -- object set column
      simp only [ber]
      split at h
      · rename_i csc cls hs
        rw [hs]; dsimp only
        split at h
        · rename_i hb; rw [hb]; exact IH h
        · rename_i hb; rw [hb]; exact IH h
        · rename_i fs n1 n2 hb
          rw [hb]
          cases fs
          all_goals first | exact IH h | exact (n1 _ _ _ _ rfl).elim | exact (n2 _ _ _ rfl).elim
        · cases h
      · cases h
    next => exact IH h -- INSTANCE OF
    next => -- time types
      split at h
      · rename_i k u hk hu
        split at h
        · cases h
        · rename_i htg
          obtain ⟨w, hw, rfl⟩ := except_map_ok h
          exact ber_time hk hu (by simpa using htg) (decTime_spec hw)
      · cases h
    next => cases h

/-- X.690: what `decode` returns is encoded by the octets: they are the layout (8.1) of an encoding
the relation `ber` relates to the value, with length forms the profile allows (8.1.3, 9.1, 10.1). -/
theorem decode_sound {E : Env} {p : Profile} {fuel : Nat} {m : Module} {t : Ty} {os : Octets} {v : Val}
    (h : decode E p fuel m t os = .ok v) :
    ∃ nd, ber E p fuel (.ofModule m) t v nd ∧ nd.LenOk p ∧ os = nd.octets := by
  unfold decode at h
  split at h
  · cases h
  rename_i nd rest hp
  split at h
  · cases h
  rename_i hrest
  split at h
  · cases h
  rename_i hlen
  obtain ⟨v0, hv0, h⟩ := except_bind_ok h
  obtain ⟨_, h⟩ := ite_err_ok h
  obtain ⟨_, h⟩ := ite_err_ok h
  cases h
  have hr : rest = [] := by simpa using hrest
  subst hr
  refine ⟨nd, dec_sound E p _ _ _ _ _ _ _ hv0, lenOkB_spec p nd (by simpa using hlen), ?_⟩
  simpa using (parseNode_octets _ _ _ _ hp).symm

end Asn1.X690
