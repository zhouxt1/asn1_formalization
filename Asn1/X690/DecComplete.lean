import Asn1.X690.ParseComplete
import Asn1.X680.Monotone

/-!
# The decoder accepts what `ber` relates

`dec_complete`: when `ber E p n sc t v nd` holds and `v` is `Decodable` (conditions a valid schema
and a value of the type meet: distinct names and enumeration numbers, IMPLICIT only on types with one
tag, well-formed OBJECT IDENTIFIER and REAL values, characters that fit, simple DEFAULTs under CER
and DER), `dec` returns a value, and returns `v` itself when the type's values are equal only when
the same (`eqIsEq`). `decode_complete` adds parsing (`parse_octets_self`): `decode` accepts the
octets of such an encoding unless its value checks reject what `dec` returned.

With `dec_sound` and `decode_sound`, the decoder accepts exactly the encodings `ber` relates to
`Decodable` values. What remains for "decodes every encoding of every value of the type to that
value": that `Has` (the value set) gives `Decodable` and the value checks; that BER is unambiguous
(two values with one encoding are `eqv`), which is where X.690 needs X.680's tag rules; and the
types `Decodable` does not cover yet (open types, contents constraints, EXTERNAL, OID-IRI, TIME).

The searches matter here: `dec` tries every component and alternative whose tags match
(`decSeqComps`, `firstOk`, `setSearch`), so it accepts an encoding even under a schema whose tags
X.680 would reject, and `encTags` follows `ber`'s own fuel (`ber_encTags`).
-/
namespace Asn1.X690
open Asn1.X680

theorem octetsEnc_tag {p : Profile} : ∀ {n : Nat} {tg : Tag} {os : Octets} {nd : Node},
    octetsEnc p n tg os nd → nd.tag = tg
  | 0, _, _, _, h => h.elim
  | _ + 1, _, _, _, h => by
    rcases h with ⟨f, rfl, _⟩ | ⟨f, ch, segs, rfl, _⟩ <;> rfl

theorem bitsEnc_tag {p : Profile} : ∀ {n : Nat} {b : Bool} {tg : Tag} {bs : Bits} {nd : Node},
    bitsEnc p n b tg bs nd → nd.tag = tg
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, _, _, _, h => by
    rcases h with ⟨f, cs, rfl, _⟩ | ⟨f, ch, segs, rfl, _⟩ <;> rfl

theorem prim_tag {tg : Tag} {P : Octets → Prop} {nd : Node} (h : Prim tg P nd) : nd.tag = tg := by
  obtain ⟨f, cs, rfl, _⟩ := h; rfl

theorem ber_tagged_tag {E : Env} {p : Profile} {n : Nat} {sc : Scope} {tg : Tag} {k : TagKind} {t : Ty}
    {v : Val} {nd : Node} (h : ber E p n sc (.tagged tg k t) v nd) : nd.tag = tg := by
  cases n with
  | zero => exact h.elim
  | succ n =>
    simp only [ber] at h
    obtain ⟨base, _, hb⟩ := h
    split at hb
    · obtain ⟨f, rfl⟩ := hb; rfl
    · subst hb; exact Node.tag_retag _ _

theorem foldr_tags_mem {α : Type} {g : α → Option (List Tag)} :
    ∀ {l : List α} {ts : List Tag}, l.foldr (fun a acc => match g a, acc with
      | some x, some y => some (x ++ y)
      | _, _ => none) (some []) = some ts → ∀ a ∈ l, ∃ ts', g a = some ts' ∧ ∀ t ∈ ts', t ∈ ts
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | b :: l, ts, h, a, ha => by
    simp only [List.foldr_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨x, hx, fun t ht => List.mem_append_left _ ht⟩
      · obtain ⟨ts', h1, h2⟩ := foldr_tags_mem hy a ha
        exact ⟨ts', h1, fun t ht => List.mem_append_right _ (h2 t ht)⟩
    · cases h

theorem encTags_time {E : Env} {n : Nat} {sc : Scope} {t : Ty} {k : TimeKind} {tg : Nat} {ts : List Tag}
    (hk : timeKind? t = some k) (hu : t.universalTag? = some tg) (ht : encTags E (n + 1) sc t = some ts) :
    ts = [univ tg] := by
  cases t <;> simp_all [timeKind?, encTags, Ty.universalTag?]

set_option maxHeartbeats 4000000 in
/-- The tag of an encoding is one `encTags` gives (or the type is an open type). -/
theorem ber_encTags (E : Env) (p : Profile) : ∀ (n : Nat) (sc : Scope) (t : Ty) (v : Val) (nd : Node)
    (ts : List Tag), ber E p n sc t v nd → encTags E n sc t = some ts → nd.tag ∈ ts
  | 0, _, _, _, _, _, h, _ => h.elim
  | n + 1, sc, t, v, nd, ts, h, ht => by
    have IH : ∀ {sc t v nd ts}, ber E p n sc t v nd → encTags E n sc t = some ts → nd.tag ∈ ts :=
      fun h ht => ber_encTags E p n _ _ _ _ _ h ht
    unfold ber at h
    split at h
    all_goals try (have hn := Nat.succ_injective (by assumption : n + 1 = _); subst hn)
    next => exact h.elim
    all_goals first
      | (simp only [encTags, Ty.universalTag?, Option.map_some, Option.getD_some, Option.some.injEq] at ht
         subst ht
         first
          | (rw [prim_tag h]; simp)
          | (obtain ⟨_, _, hb⟩ := h; rw [bitsEnc_tag hb]; simp)
          | (rw [octetsEnc_tag h]; simp)
          | (obtain ⟨_, _, rfl, _⟩ := h; simp [Node.tag])
          | (obtain ⟨_, _, _, rfl, _⟩ := h; simp [Node.tag])
          | (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := h; simp [Node.tag])
          | (obtain ⟨_, _, hp⟩ := h; rw [prim_tag hp]; simp)
          | (obtain ⟨_, _, _, _, ho⟩ := h; rw [octetsEnc_tag ho]; simp)
          | (obtain ⟨_, _, ho⟩ := h; rw [octetsEnc_tag ho]; simp)
          | (obtain ⟨_, _, _, hu, ho⟩ := h; rw [octetsEnc_tag ho]; revert hu; cases ‹StrType› <;> simp [Ty.universalTag?] <;> rintro rfl <;> rfl)
          | (rw [ber_tagged_tag h]; simp))
      | skip
    case h_13 =>
      obtain ⟨alt, halt, _, hb⟩ := h
      simp only [encTags] at ht
      obtain ⟨ts', h1, h2⟩ := foldr_tags_mem ht alt halt
      exact h2 _ (IH hb h1)
    case h_14 =>
      simp only [encTags] at ht
      split at h
      · rename_i sc' root ext hb
        rw [hb] at ht; dsimp only at ht
        split at h
        · rename_i alt ha; rw [ha] at ht; exact IH h ht
        · exact h.elim
      · exact h.elim
    case h_23 =>
      obtain ⟨_, os, _, ho⟩ := h
      simp only [encTags, Ty.universalTag?, Option.map_some, Option.getD_some, Option.some.injEq] at ht
      subst ht; rw [octetsEnc_tag ho]; simp
    case h_24 =>
      obtain ⟨_, os, _, ho⟩ := h
      simp only [encTags, Ty.universalTag?, Option.map_some, Option.getD_some, Option.some.injEq] at ht
      subst ht; rw [octetsEnc_tag ho]; simp
    case h_26 =>
      simp only [encTags] at ht
      split at h
      · rename_i sc' t' hr; rw [hr] at ht; exact IH h ht
      · exact h.elim
    case h_27 =>
      simp only [encTags] at ht
      split at h
      · rename_i sc' t' hr; rw [hr] at ht; exact IH h ht
      · exact h.elim
    case h_28 =>
      simp only [encTags] at ht
      split at h
      · rename_i sc' t' hr; rw [hr] at ht; exact IH h ht
      · exact h.elim
    case h_29 =>
      simp only [encTags, Option.some.injEq] at ht
      subst ht
      obtain ⟨base, _, hb⟩ := h
      split at hb
      · obtain ⟨f, rfl⟩ := hb; simp [Node.tag]
      · subst hb; rw [Node.tag_retag]; simp
    case h_30 =>
      simp only [encTags] at ht; exact IH h ht
    case h_31 =>
      simp [encTags] at ht
    case h_32 =>
      simp only [encTags] at ht
      split at h
      all_goals first
        | exact h.elim
        | (rename_i hcf; rw [hcf] at ht; first | exact IH h ht | simp at ht)
    case h_33 =>
      simp only [encTags] at ht
      split at h
      · rename_i csc cls hs
        rw [hs] at ht; dsimp only at ht
        split at h
        all_goals first
          | exact h.elim
          | (rename_i hcf; rw [hcf] at ht; first | exact IH h ht | simp at ht)
          | (rename_i fs n1 n2 hcf; rw [hcf] at ht; cases fs <;> first | simp at ht | exact (n1 _ _ _ _ rfl).elim | exact (n2 _ _ _ rfl).elim)
      · exact h.elim
    case h_35 =>
      split at h
      · rename_i k tg hk hu
        have := encTags_time hk hu ht
        subst this; rw [prim_tag h]; simp
      · exact h.elim
    case h_36 => exact h.elim

/-! ## Contents octets, read back -/

theorem mapM_complete {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, List.Forall₂ (fun x y => f x = .ok y) l ys → l.mapM f = .ok ys
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.mapM_cons, h, mapM_complete hs]; rfl

theorem intContentsB_complete {i : Int} {cs : Octets} (h : IntContents i cs) :
    intContentsB cs = true ∧ tcValue (bitsOf cs) = i := by
  obtain ⟨⟨h8, hpos, hv, hmin⟩, hne⟩ := h
  refine ⟨?_, hv⟩
  simp only [intContentsB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨hne, ?_⟩
  rcases hmin with hm | hm
  · left; rw [bitsOf_length] at hm; omega
  · right; exact hm

theorem decBitsPrim_complete {p : Profile} {bs : Bits} {cs : Octets} (h : BitsPrim p bs cs) :
    decBitsPrim p cs = .ok bs := by
  obtain ⟨u, pad, hu, hpl, h8, hbs0, rfl, hr⟩ := h
  have hlen8 : (bs ++ pad).length % 8 = 0 := by simp [hpl, h8]
  have hall : bitsOf (bitsToOctets (bs ++ pad)) = bs ++ pad := bitsOf_bitsToOctets _ hlen8
  have huv : (octet u).val = u := by simp only [octet]; omega
  unfold decBitsPrim
  simp only [huv, show ¬ (u > 7) by omega, ite_false]
  have hemp : ¬ ((bitsToOctets (bs ++ pad)).isEmpty && decide (u ≠ 0)) = true := by
    intro he
    simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at he
    have := congrArg List.length he.1
    rw [bitsToOctets_length hlen8] at this
    simp only [List.length_nil, List.length_append, hpl] at this
    have hb : bs = [] := by
      apply List.eq_nil_of_length_eq_zero; omega
    exact he.2 (hbs0 hb)
  simp only [hemp, ite_false, hall, List.length_append, hpl, Nat.add_sub_cancel]
  rw [List.take_left' rfl, List.drop_left' rfl]
  have hpad : (p.restricted && pad != List.replicate u false) = false := by
    cases hp : p.restricted
    · rfl
    · simp [hr hp]
  simp only [hpad, Bool.false_eq_true, ↓reduceIte]

theorem cerFragmentsB_complete {ch : List Node} (h : CerFragments ch) : decOctets.cerFragmentsB ch = true := by
  obtain ⟨h1, h2, ⟨nd, hl, h3, h4⟩⟩ := h
  simp only [decOctets.cerFragmentsB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', hl,
    decide_eq_true_eq]
  refine ⟨⟨h1, fun x hx => ?_⟩, h3, h4⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i + 1 < ch.length := by simp at hi; omega
  simp only [beq_iff_eq]
  exact h2 i _ (by rw [List.getElem_dropLast]; exact List.getElem?_eq_getElem _) hi'

theorem decOctets_complete (p : Profile) : ∀ (n : Nat) (tg : Tag) (os : Octets) (nd : Node),
    octetsEnc p n tg os nd → decOctets p n tg nd = .ok os
  | 0, _, _, _, h => h.elim
  | n + 1, tg, os, nd, h => by
    rcases h with ⟨f, rfl, hc⟩ | ⟨f, ch, segs, rfl, hd, rfl, hseg, hc⟩
    · simp only [decOctets, bne_self_eq_false, Bool.false_eq_true, ite_false]
      split
      · rename_i hcer
        simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcer
        exact absurd (hc hcer.1) (by omega)
      · rfl
    · simp only [decOctets, bne_self_eq_false, Bool.false_eq_true, ite_false, hd, decide_false,
        ite_false]
      have hm : ch.mapM (decOctets p n (univ 4)) = .ok segs :=
        mapM_complete (hseg.flip.imp fun _ _ hh => decOctets_complete p n _ _ _ hh)
      simp only [hm]
      have hx : (decide (p = .cer) && !(decide (1000 < segs.flatten.length) && decOctets.cerFragmentsB ch)) = false := by
        cases hp : decide (p = .cer)
        · rfl
        · obtain ⟨h1, h2⟩ := hc (of_decide_eq_true hp)
          simp only [decide_eq_true h1, cerFragmentsB_complete h2, Bool.and_self, Bool.not_true, Bool.and_false]
      show (do let segs ← Except.ok segs; _) = _
      simp only [bind, Except.bind]
      simp only [hx, Bool.false_eq_true, ↓reduceIte]

theorem forall₂_zipIdx_unflip {α β : Type} {R : α × Nat → β → Prop} :
    ∀ {segs : List β} {ch : List α} (k : Nat), List.Forall₂ (fun (si : β × Nat) c => R (c, si.2) si.1) (segs.zipIdx k) ch →
      List.Forall₂ R (ch.zipIdx k) segs
  | [], ch, k, h => by
    simp only [List.zipIdx_nil] at h; cases h; exact .nil
  | s :: segs, ch, k, h => by
    simp only [List.zipIdx_cons] at h
    cases h with
    | cons h1 h2 =>
      simp only [List.zipIdx_cons]
      exact .cons h1 (forall₂_zipIdx_unflip (k + 1) h2)

theorem decBits_complete (p : Profile) : ∀ (n : Nat) (isLast : Bool) (tg : Tag) (bs : Bits) (nd : Node),
    bitsEnc p n isLast tg bs nd → decBits p n isLast tg nd = .ok bs
  | 0, _, _, _, _, h => h.elim
  | n + 1, isLast, tg, bs, nd, h => by
    rcases h with ⟨f, cs, rfl, hb, hl, hc⟩ | ⟨f, ch, segs, rfl, hd, rfl, hseg, hc⟩
    · simp only [decBits, bne_self_eq_false, Bool.false_eq_true, ite_false]
      split
      · rename_i hcer
        simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcer
        exact absurd (hc hcer.1) (by omega)
      · simp only [decBitsPrim_complete hb]
        show (if (!isLast && bs.length % 8 != 0) = true then _ else _) = _
        split
        · rename_i hx
          simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hx
          exact absurd (hl hx.1) hx.2
        · rfl
    · simp only [decBits, bne_self_eq_false, Bool.false_eq_true, ite_false, hd, decide_false, ite_false]
      have hlen : segs.length = ch.length := by
        have := hseg.length_eq; simpa using this
      have hf := forall₂_zipIdx_unflip (R := fun (ci : Node × Nat) s =>
          bitsEnc p n (isLast && ci.2 + 1 == ch.length) (univ 3) s ci.1) 0
        (hseg.imp fun si c hh => by rw [hlen] at hh; exact hh)
      have hm := mapM_complete (hf.imp fun ci s hh => decBits_complete p n _ _ _ _ hh)
      simp only [hm]
      have hx : (decide (p = .cer) && !(decide (1000 < (segs.flatten.length + 7) / 8 + 1) &&
          decOctets.cerFragmentsB ch)) = false := by
        cases hp : decide (p = .cer)
        · rfl
        · obtain ⟨h1, h2⟩ := hc (of_decide_eq_true hp)
          simp only [decide_eq_true h1, cerFragmentsB_complete h2, Bool.and_self, Bool.not_true, Bool.and_false]
      simp only [bind, Except.bind]
      simp only [hx, Bool.false_eq_true, ↓reduceIte]

/-! ## Character strings (8.23) -/

theorem utf8_length_pos (c : Nat) : 1 ≤ (utf8 c).length := by
  unfold utf8; split <;> (try split) <;> (try split) <;> simp

theorem utf8String_length (cs : List Nat) : cs.length ≤ (utf8String cs).length := by
  induction cs with
  | nil => simp [utf8String]
  | cons c cs ih =>
    have := utf8_length_pos c
    simp only [utf8String, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢; omega

theorem decUtf8_go_utf8 : ∀ (cs : List Nat) (k : Nat), (∀ c ∈ cs, c < 0x200000) → cs.length < k →
    decUtf8.go k ((utf8String cs).map (·.val)) = some cs
  | [], k, _, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    rfl
  | c :: cs, k, hc, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hc0 : c < 0x200000 := hc c (by simp)
    have ih := decUtf8_go_utf8 cs k (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (by simp at hk; omega)
    have hs : utf8String (c :: cs) = utf8 c ++ utf8String cs := by simp [utf8String]
    rw [hs, List.map_append]
    unfold utf8
    by_cases h1 : c < 0x80
    · simp only [h1, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have hv : (octet c).val = c := by simp only [octet]; omega
      simp only [decUtf8.go, hv, h1, ↓reduceIte, ih, Option.map_some]
    by_cases h2 : c < 0x800
    · simp only [h1, h2, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have hv1 : (octet (0xC0 + c / 64)).val = 0xC0 + c / 64 := by simp only [octet]; omega
      have hv2 : (octet (0x80 + c % 64)).val = 0x80 + c % 64 := by simp only [octet]; omega
      rw [decUtf8.go, hv1, hv2]
      simp only [show ¬ (0xC0 + c / 64 < 0x80) by omega, show 0xC0 + c / 64 < 0xE0 by omega, ↓reduceIte, ih,
        Option.map_some]
      congr 2; omega
    by_cases h3 : c < 0x10000
    · simp only [h1, h2, h3, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have hv1 : (octet (0xE0 + c / 4096)).val = 0xE0 + c / 4096 := by simp only [octet]; omega
      have hv2 : (octet (0x80 + c / 64 % 64)).val = 0x80 + c / 64 % 64 := by simp only [octet]; omega
      have hv3 : (octet (0x80 + c % 64)).val = 0x80 + c % 64 := by simp only [octet]; omega
      rw [decUtf8.go, hv1, hv2, hv3]
      simp only [show ¬ (0xE0 + c / 4096 < 0x80) by omega, show ¬ (0xE0 + c / 4096 < 0xE0) by omega,
        show 0xE0 + c / 4096 < 0xF0 by omega, ↓reduceIte, ih, Option.map_some]
      congr 2; omega
    · simp only [h1, h2, h3, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have hv1 : (octet (0xF0 + c / 262144)).val = 0xF0 + c / 262144 := by simp only [octet]; omega
      have hv2 : (octet (0x80 + c / 4096 % 64)).val = 0x80 + c / 4096 % 64 := by simp only [octet]; omega
      have hv3 : (octet (0x80 + c / 64 % 64)).val = 0x80 + c / 64 % 64 := by simp only [octet]; omega
      have hv4 : (octet (0x80 + c % 64)).val = 0x80 + c % 64 := by simp only [octet]; omega
      rw [decUtf8.go, hv1, hv2, hv3, hv4]
      simp only [show ¬ (0xF0 + c / 262144 < 0x80) by omega, show ¬ (0xF0 + c / 262144 < 0xE0) by omega,
        show ¬ (0xF0 + c / 262144 < 0xF0) by omega, ↓reduceIte, ih, Option.map_some]
      congr 2; omega

theorem decUtf8_utf8String {cs : List Nat} (hc : ∀ c ∈ cs, c < 0x200000) :
    decUtf8 (utf8String cs) = some cs := by
  unfold decUtf8
  rw [decUtf8_go_utf8 cs _ hc (by have := utf8String_length cs; omega)]
  simp

theorem flatMap_beOctets_chunk {w : Nat} : ∀ (cs : List Nat) (i : Nat), i < cs.length →
    ((cs.flatMap fun c => beOctets w c).drop (w * i)).take w = beOctets w cs[i]!
  | [], i, h => absurd h (Nat.not_lt_zero _)
  | c :: cs, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero]
    rw [List.take_left' (beOctets_length w c)]; rfl
  | c :: cs, i + 1, h => by
    simp only [List.flatMap_cons]
    rw [show w * (i + 1) = (beOctets w c).length + w * i by rw [beOctets_length]; ring, List.drop_append]
    simp only [List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]
    rw [flatMap_beOctets_chunk cs i (by simp at h; omega)]
    rfl

theorem flatMap_beOctets_length (w : Nat) (cs : List Nat) :
    (cs.flatMap fun c => beOctets w c).length = w * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.flatMap_cons, List.length_append, beOctets_length, ih, List.length_cons]; ring

theorem decWide_complete {w : Nat} {cs : List Nat} (hw : 0 < w) (hc : ∀ c ∈ cs, c < 256 ^ w) :
    decWide w (cs.flatMap fun c => beOctets w c) = some cs := by
  unfold decWide
  rw [flatMap_beOctets_length]
  have hcs : ((List.range (w * cs.length / w)).map fun i =>
      beValue (((cs.flatMap fun c => beOctets w c).drop (w * i)).take w)) = cs := by
    rw [Nat.mul_div_cancel_left _ hw]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [flatMap_beOctets_chunk cs i h2, beValue_beOctets (by
      rw [getElem!_pos cs i h2]; exact hc _ (List.getElem_mem h2))]
    exact (getElem!_pos cs i h2)
  simp only [Nat.mul_mod_right, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hcs]; simp

/-- The characters of a string value fit its encoding (X.680 41, Table 8: BMPString's characters are
below 2^16, UniversalString's below 2^32, and ISO/IEC 10646's below 2^21, as UTF-8 writes them). -/
def StrBound : StrType → Val → Prop
  | .universal, .chars cs => ∀ c ∈ cs, c < 256 ^ 4
  | .bmp, .chars cs => ∀ c ∈ cs, c < 256 ^ 2
  | .utf8, .chars cs => ∀ c ∈ cs, c < 0x200000
  | _, _ => True

theorem decString_complete {p : Profile} {k : StrType} {v : Val} {os : Octets} (h : StringOctets p k v os)
    (hb : StrBound k v) : decString p k os = .ok v := by
  have hascii : ∀ cs : List Nat, os = cs.map octet → (∀ c ∈ cs, c < 128) →
      (if os.all (·.val < 128) then Except.ok (Val.chars (os.map (·.val))) else Except.error "8.23.5: octet above 7F") =
        (Except.ok (Val.chars cs) : Except String Val) := by
    intro cs hos hc
    subst hos
    have hall : (cs.map octet).all (·.val < 128) = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
      intro c hc'; have := hc c hc'; simp only [octet]; omega
    simp only [hall, ↓reduceIte, List.map_map]
    congr 2
    conv_rhs => rw [← List.map_id cs]
    apply List.map_congr_left
    intro c hc'; have := hc c hc'; simp only [Function.comp_apply, octet, id]; omega
  cases v with
  | chars cs =>
    cases k <;> simp only [StringOctets] at h <;> simp only [decString]
    all_goals first
      | exact h.elim
      | (obtain ⟨hos, hc⟩ := h; exact hascii cs hos hc)
      | skip
    · subst h; simp only [StrBound] at hb
      rw [show bmpOctets cs = cs.flatMap fun c => beOctets 2 c from rfl, decWide_complete (by norm_num) hb]
    · subst h; simp only [StrBound] at hb
      rw [show universalOctets cs = cs.flatMap fun c => beOctets 4 c from rfl, decWide_complete (by norm_num) hb]
    · subst h; simp only [StrBound] at hb; rw [decUtf8_utf8String hb]
  | regChars cs =>
    obtain ⟨hr, he⟩ := h
    cases k <;> simp only [StrType.isRegister, Bool.false_eq_true, reduceCtorEq] at hr
    all_goals (simp only [decString]; rw [show iso2022Decode _ _ _ _ _ _ = _ from he])
  | _ => exact h.elim

/-! ## Object identifiers (8.19, 8.20) -/

theorem base128_length_pos (n : Nat) : 1 ≤ (base128 n).length := by
  have hs := base128_go_spec (n + 1) n (by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 128 ^ (n + 1 + 1) := by
        calc 2 ^ n ≤ 2 ^ (7 * (n + 1 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 128 ^ (n + 1 + 1) := by rw [pow_mul]; norm_num)
  have := List.length_pos_iff.mpr hs.2.2
  simp only [base128, List.length_map, List.length_zipIdx, List.length_reverse]; omega

theorem decOidArcs_go_flatMap : ∀ (arcs : List Nat) (k : Nat), arcs.length < k →
    decOidArcs.go k (arcs.flatMap base128) = some arcs
  | [], k, _ => by cases k <;> rfl
  | a :: arcs, k, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hne : base128 a ++ arcs.flatMap base128 ≠ [] := by
      intro he
      have h1 := congrArg List.length he
      have h2 := base128_length_pos a
      simp only [List.length_append, List.length_nil] at h1; omega
    simp only [List.flatMap_cons]
    obtain ⟨o, os, ho⟩ := List.exists_cons_of_ne_nil hne
    rw [ho]; simp only [decOidArcs.go]; rw [← ho, readSubId_base128]
    simp only [decOidArcs_go_flatMap arcs k (by simp at hk; omega), Option.map_some]

theorem flatMap_base128_length (arcs : List Nat) : arcs.length ≤ (arcs.flatMap base128).length := by
  induction arcs with
  | nil => simp
  | cons a arcs ih =>
    have := base128_length_pos a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

/-- X.660: an object identifier's first arc is 0, 1 or 2, and under 0 or 1 the second is below 40;
there are at least two arcs (X.690 8.19.4). -/
def OidWf : List Nat → Prop
  | x :: y :: _ => x ≤ 2 ∧ (x < 2 → y < 40)
  | _ => False

theorem decOidArcs_complete {arcs : List Nat} (h : OidWf arcs) : decOidArcs false (oidContents arcs) = some arcs := by
  match arcs, h with
  | x :: y :: rest, ⟨hx, hy⟩ =>
    unfold decOidArcs
    have hgo := decOidArcs_go_flatMap ((40 * x + y) :: rest) ((oidContents (x :: y :: rest)).length + 1)
      (by have := flatMap_base128_length ((40 * x + y) :: rest); simp [oidContents] at this ⊢; omega)
    simp only [List.flatMap_cons] at hgo
    simp only [oidContents] at hgo ⊢
    rw [hgo]
    dsimp only
    have harcs : (if 40 * x + y < 40 then [0, 40 * x + y] else if 40 * x + y < 80 then [1, 40 * x + y - 40]
        else [2, 40 * x + y - 80]) = [x, y] := by
      by_cases h0 : x = 0
      · subst h0; simp; omega
      by_cases h1 : x = 1
      · subst h1; simp; omega
      · have : x = 2 := by omega
        subst this; simp; omega
    rw [harcs]
    simp [oidContents]

theorem decOidArcs_rel_complete (arcs : List Nat) : decOidArcs true (relOidContents arcs) = some arcs := by
  unfold decOidArcs relOidContents
  rw [decOidArcs_go_flatMap arcs _ (by have := flatMap_base128_length arcs; omega)]
  simp

/-! ## GeneralizedTime and UTCTime (11.7, 11.8) -/

theorem utcTimeCanonB_complete {s : List Char} (h : UtcTimeCanon s) : utcTimeCanonB s = true := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [utcTimeCanonB, h1, h2, h3]

theorem genTimeCanonB_complete {s : List Char} (h : GenTimeCanon s) : genTimeCanonB s = true := by
  obtain ⟨hz, ymdhms, fr, rfl, hl, hd, hf, hlast⟩ := h
  have ht : (ymdhms ++ (if fr = [] then [] else '.' :: fr) ++ ['Z']).take 14 = ymdhms := by
    rw [List.append_assoc, List.take_left' hl]
  have hr : ((ymdhms ++ (if fr = [] then [] else '.' :: fr) ++ ['Z']).drop 14).dropLast =
      (if fr = [] then [] else '.' :: fr) := by
    rw [List.append_assoc, List.drop_left' hl, List.dropLast_append_cons, List.dropLast_singleton,
      List.append_nil]
  simp only [genTimeCanonB, ht, hr, hz, hd, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq]
  refine ⟨by split <;> simp [hl] <;> omega, ?_⟩
  by_cases hf0 : fr = []
  · simp [hf0]
  · right
    obtain ⟨c, fr', rfl⟩ := List.exists_cons_of_ne_nil hf0
    simp only [reduceCtorEq, ↓reduceIte] at hr ⊢
    simp only [List.head?_cons, List.length_cons, List.drop_succ_cons, List.drop_zero, hf, List.getLast?_cons_cons]
    simpa using hlast

/-! ## REAL (8.5, 11.3) -/

theorem digVal_append (l : List Char) (c : Char) : digVal (l ++ [c]) = 10 * digVal l + (c.toNat - '0'.toNat) := by
  simp [digVal, List.foldl_append]

theorem digitChar_spec {d : Nat} (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d ∧ isDig (Nat.digitChar d) = true := by
  interval_cases d <;> decide

theorem toDigits_spec : ∀ (m : Nat), digVal (Nat.toDigits 10 m) = m ∧ ∀ c ∈ Nat.toDigits 10 m, isDig c = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.toDigits_eq_if (by norm_num)]
    split
    · rename_i hm
      obtain ⟨h1, h2⟩ := digitChar_spec hm
      refine ⟨by simpa [digVal] using h1, by simpa using h2⟩
    · rename_i hm
      obtain ⟨ih1, ih2⟩ := ih (m / 10) (by omega)
      obtain ⟨h1, h2⟩ := digitChar_spec (show m % 10 < 10 by omega)
      refine ⟨by rw [digVal_append, ih1, h1]; omega, ?_⟩
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih2 c hc
      · simp at hc; subst hc; exact h2

theorem takeWhile_toDigits (m : Nat) (rest : List Char) (hr : ∀ c, rest.head? = some c → isDig c = false) :
    (Nat.toDigits 10 m ++ rest).takeWhile isDig = Nat.toDigits 10 m := by
  rw [List.takeWhile_append_of_pos (fun a ha => (toDigits_spec m).2 a ha)]
  cases rest with
  | nil => simp
  | cons c r => simp [List.takeWhile_cons, hr c rfl]

theorem toDigits_head_ne (m : Nat) (c : Char) (hc : isDig c = false) : (Nat.toDigits 10 m).head? ≠ some c := by
  intro h
  have hm := List.mem_of_mem_head? h
  rw [(toDigits_spec m).2 c hm] at hc; cases hc

theorem nr3Exp_spec (e : Int) : nr3Exp (if e = 0 then ['+', '0'] else if e < 0 then '-' :: Nat.toDigits 10 e.natAbs
    else Nat.toDigits 10 e.natAbs) = e := by
  unfold nr3Exp
  by_cases h0 : e = 0
  · simp [h0, digVal]
  by_cases hl : e < 0
  · simp only [h0, hl, ↓reduceIte, List.head?_cons, beq_self_eq_true, Bool.true_or, List.drop_succ_cons,
      List.drop_zero]
    rw [(toDigits_spec _).1]; omega
  · simp only [h0, hl, ↓reduceIte]
    have h1 : ((Nat.toDigits 10 e.natAbs).head? == some '-') = false := by
      simpa using toDigits_head_ne e.natAbs '-' (by decide)
    have h2 : ((Nat.toDigits 10 e.natAbs).head? == some '+') = false := by
      simpa using toDigits_head_ne e.natAbs '+' (by decide)
    simp only [h1, h2, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [(toDigits_spec _).1]; omega

theorem nr3CanonB_complete {q : ℚ} {s : List Char} (h : Nr3Canon q s) : nr3CanonB q s = true := by
  obtain ⟨neg, m, e, hm, hm10, hq, rfl⟩ := h
  have hdig := toDigits_spec m
  have hne := @Nat.toDigits_ne_nil m 10
  generalize hX : (if e = 0 then ['+', '0'] else if e < 0 then '-' :: Nat.toDigits 10 e.natAbs
    else Nat.toDigits 10 e.natAbs) = X
  have hXe : nr3Exp X = e := by rw [← hX]; exact nr3Exp_spec e
  have hneg : (((if neg then ['-'] else []) ++ Nat.toDigits 10 m ++ ['.', 'E'] ++ X).head? == some '-') = neg := by
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_assoc]
      obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hne
      rw [hc]
      have : c ≠ '-' := fun e => toDigits_head_ne m '-' (by decide) (by rw [hc, e]; rfl)
      simp [this]
    · simp
  have hr : (if neg then ((if neg then ['-'] else []) ++ Nat.toDigits 10 m ++ ['.', 'E'] ++ X).drop 1
      else ((if neg then ['-'] else []) ++ Nat.toDigits 10 m ++ ['.', 'E'] ++ X)) =
      Nat.toDigits 10 m ++ ('.' :: 'E' :: X) := by
    cases neg <;> simp
  have hmd : (Nat.toDigits 10 m ++ ('.' :: 'E' :: X)).takeWhile isDig = Nat.toDigits 10 m :=
    takeWhile_toDigits m _ (fun c hc => by simp at hc; subst hc; decide)
  have hex : ((Nat.toDigits 10 m ++ ('.' :: 'E' :: X)).drop (Nat.toDigits 10 m).length).drop 2 = X := by
    simp
  unfold nr3CanonB
  simp only [hneg, hr, hmd, hex, hdig.1, hXe]
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨hm, hm10⟩, hq⟩, ?_⟩
  rw [← hX]; rfl

theorem expField_fmt {e : Int} {fmt : Nat} {os : Octets} (h : ExpField e fmt os) : fmt ≤ 3 := by
  match fmt, h with
  | 0, _ | 1, _ | 2, _ | 3, _ => omega
  | k + 4, h => exact h.elim

theorem expFieldB_complete {e : Int} {fmt : Nat} {os : Octets} (h : ExpField e fmt os) : expFieldB e fmt os = true := by
  match fmt, h with
  | 0, h | 1, h | 2, h => simp only [ExpField] at h; simp [expFieldB, h.1, h.2]
  | 3, h =>
    obtain ⟨x, ex, rfl, h1, h2, h3, h4, h5⟩ := h
    have hv : (octet x).val = x := by simp only [octet]; omega
    simp only [expFieldB, hv, h3, h4, beq_self_eq_true, Bool.and_true, Bool.true_and, decide_eq_true h1]
    rcases h5 with h5 | ⟨h5a, h5b⟩
    · simp [h5]
    · simp only [Bool.or_eq_true]; right; simpa using ⟨h5a, h5b⟩
  | k + 4, h => exact h.elim

theorem realSplit_ef {e : Int} {fmt : Nat} {ef nf : Octets} (h : ExpField e fmt ef) :
    realSplit fmt (ef ++ nf) = (ef, nf) ∧ tcValue (bitsOf (realExpOctets fmt ef)) = e := by
  match fmt, h with
  | 0, h | 1, h | 2, h =>
    simp only [ExpField] at h
    refine ⟨?_, by simpa [realExpOctets] using h.2⟩
    simp only [realSplit, List.take_left' h.1, List.drop_left' h.1]
  | 3, h =>
    obtain ⟨x, ex, rfl, h1, h2, h3, h4, _⟩ := h
    have hv : (octet x).val = x := by simp only [octet]; omega
    refine ⟨?_, by simpa [realExpOctets] using h4⟩
    simp only [List.cons_append, realSplit, hv]
    rw [List.take_left' h3, List.drop_left' h3]
  | k + 4, h => exact h.elim

theorem decReal_complete {p : Profile} {r : RealVal} {cs : Octets} (h : RealContents p r cs) (hw : r.Wf) :
    decReal p cs = .ok r := by
  cases r with
  | plusZero => simp only [RealContents] at h; subst h; rfl
  | plusInfinity => simp only [RealContents] at h; subst h; rfl
  | minusInfinity => simp only [RealContents] at h; subst h; rfl
  | notANumber => simp only [RealContents] at h; subst h; rfl
  | minusZero => simp only [RealContents] at h; subst h; rfl
  | num b q =>
    cases b with
    | two =>
      obtain ⟨neg, bb, f, e, nn, fmt, ef, nf, hbb, hf, hnn, hq, rfl, hnf, hnv, hr⟩ := h
      have hef : ExpField e fmt ef := by
        split at hr
        · exact expFieldMin_expField hr.2.2.2.2
        · exact hr
      have hfmt := expField_fmt hef
      obtain ⟨hsplit, he⟩ := realSplit_ef (nf := nf) hef
      have hov : (octet (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt)).val =
          128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt := by
        simp only [octet]; split <;> omega
      have h1 : (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) / 128 = 1 := by split <;> omega
      have h2 : ((128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) / 64 % 2 == 1) = neg := by
        cases neg <;> simp <;> omega
      have h3 : (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) / 16 % 4 = bb := by split <;> omega
      have h4 : (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) / 4 % 4 = f := by split <;> omega
      have h5 : (128 + (if neg then 64 else 0) + 16 * bb + 4 * f + fmt) % 4 = fmt := by split <;> omega
      unfold decReal
      rw [List.cons_append]
      dsimp only
      simp only [hov, h1, h2, h3, h4, h5, ↓reduceIte, show bb ≠ 3 by omega, hsplit, he, hnv]
      have hnz : (nf.isEmpty || decide (nn = 0)) = false := by
        simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff, decide_eq_false_iff_not]; exact ⟨hnf, by omega⟩
      simp only [hnz, Bool.false_eq_true, ↓reduceIte, expFieldB_complete hef, Bool.not_true]
      have hres : (p.restricted && !(bb == 0 && f == 0 && nn % 2 == 1 && nf == bitsToOctets (nnbMinFn nn) &&
          decide (ExpFieldMin e fmt ef))) = false := by
        split at hr
        · rename_i hp
          obtain ⟨r1, r2, r3, r4, r5⟩ := hr
          simp [hp, r1, r2, r3, r4, r5]
        · rename_i hp; simp [hp]
      simp only [hres, Bool.false_eq_true, ↓reduceIte, hq]
    | ten =>
      obtain ⟨form, s, rfl, hs, hf1, hf3, hv, hr⟩ := h
      have hov : (octet form).val = form := by simp only [octet]; omega
      have hs' : (s.map fun c => octet c.toNat).map (fun c => Char.ofNat c.val) = s := by
        simp only [List.map_map]
        conv_rhs => rw [← List.map_id s]
        apply List.map_congr_left
        intro c hc
        have := hs c hc
        simp only [Function.comp_apply, octet, Nat.mod_eq_of_lt (show c.toNat < 256 by omega), Char.ofNat_toNat, id]
      have hall : (s.map fun c => octet c.toNat).all (·.val < 128) = true := by
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
        intro c hc; have := hs c hc; simp only [octet]; omega
      unfold decReal
      dsimp only
      simp only [hov, show ¬ (form / 128 = 1) by omega, show ¬ (form / 64 = 1) by omega, ↓reduceIte,
        Nat.mod_eq_of_lt (show form < 64 by omega), hs', hall, Bool.not_true, Bool.false_or,
        show ¬ (form < 1) by omega, show ¬ (form > 3) by omega, decide_false, Bool.or_false, Bool.false_eq_true, hv]
      have hq0 : q ≠ 0 := hw.1
      simp only [hq0, ↓reduceIte]
      have hres : (p.restricted && !(form == 3 && nr3CanonB q s)) = false := by
        cases hp : p.restricted
        · rfl
        · obtain ⟨h3, hc⟩ := hr hp
          simp [h3, nr3CanonB_complete hc]
      simp only [hres, Bool.false_eq_true, ↓reduceIte]

/-! ## DEFAULT values (11.5) -/

theorem evalLit_evalVal (E : Env) : ∀ (n : Nat) (sc : Scope) (d d' : Val),
    evalLit E n sc d = some d' → evalVal E n sc d d'
  | 0, _, _, _, h => by simp [evalLit] at h
  | n + 1, sc, d, d', h => by
    cases d with
    | ref mn name args =>
      simp only [evalLit] at h
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [evalVal, hr]
      exact evalLit_evalVal E n sc' v d' h
    | bool _ | int _ | enum _ | oid _ | chars _ | octets _ | bits _ =>
      simp only [evalLit, Option.some.injEq] at h; subst h; simp [evalVal]
    | _ => simp [evalLit] at h

/-- Under CER and DER, what the decoder needs to see that an encoded DEFAULT component `x` is not its
default value: the default is a simple value, of a type whose values are equal when the same, and
it differs from `x` visibly (`litNeq`) unless it is the same abstract value. -/
def DefaultDec (E : Env) (n : Nat) (en : Entry) (x : Val) : Prop :=
  match en.presence with
  | .default_ d => ∃ d', evalLit E n en.scope d = some d' ∧ eqIsEq E n en.scope en.ty = true ∧
      (litNeq x d' = true ∨ eqv E n en.scope en.ty x d')
  | _ => True

theorem notDefaultB_complete {E : Env} {n : Nat} {en : Entry} {x : Val} (hd : DefaultDec E n en x)
    (hn : ¬ IsDefault E n en x) : notDefaultB E n en x = true := by
  unfold DefaultDec at hd
  unfold IsDefault at hn
  unfold notDefaultB
  split
  · rename_i d hp
    rw [hp] at hd hn
    obtain ⟨d', hl, heq, hx⟩ := hd
    rw [hl]
    simp only [heq, Bool.true_and]
    rcases hx with hx | hx
    · exact hx
    · exact absurd ⟨d', evalLit_evalVal E n _ _ _ hl, hx⟩ hn
  · rfl

theorem defaultErr_none_complete {E : Env} {n : Nat} {comps : List (Entry × Ty)} {cs : List (String × Val)}
    (h : ∀ c ∈ comps, ∀ x, cs.lookup c.1.name = some x → notDefaultB E n c.1 x = true) :
    defaultErr E n comps cs = none := by
  unfold defaultErr
  split
  · rename_i en ty hf
    have hp := List.find?_some hf
    simp only at hp
    split at hp
    · rename_i x hx
      have := h _ (List.mem_of_find?_eq_some hf) x hx
      simp [this] at hp
    · cases hp
  · rfl

/-! ## The searches find what there is -/

theorem firstOk_complete {α β : Type} {f : α → Except String β} {err : String} :
    ∀ {l : List α} {a : α} {b : β}, a ∈ l → f a = .ok b → ∃ b', firstOk f err l = .ok b'
  | [], _, _, ha, _ => absurd ha List.not_mem_nil
  | c :: rest, a, b, ha, hf => by
    simp only [firstOk]
    split
    · exact ⟨_, rfl⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · rename_i e he; rw [hf] at he; cases he
      · obtain ⟨b', hb'⟩ := firstOk_complete ha hf
        rw [hb']; exact ⟨b', rfl⟩

theorem setSearch_complete {L : Nat} {β : Type} {cand : Node → List (Fin L)} {k : List (Fin L × Node) → Except String β} :
    ∀ (ext : List (Fin L × Node)) (acc : List (Fin L × Node)) (b : β),
      (∀ a ∈ ext, a.1 ∈ cand a.2) → ((acc.reverse ++ ext).map (·.1)).Nodup →
      k (acc.reverse ++ ext) = .ok b → ∃ b', setSearch cand k (ext.map (·.2)) acc = .ok b'
  | [], acc, b, _, _, hk => ⟨b, by simpa [setSearch] using hk⟩
  | (i, nd) :: ext, acc, b, hc, hnd, hk => by
    simp only [List.map_cons, setSearch]
    have hmem : i ∈ (cand nd).filter fun j => !(acc.any (·.1 == j)) := by
      refine List.mem_filter.mpr ⟨hc _ (List.mem_cons_self ..), ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro a ha hai
      have : (acc.reverse ++ (i, nd) :: ext).map (·.1) = (acc.reverse.map (·.1)) ++ i :: ext.map (·.1) := by simp
      rw [this, List.nodup_append] at hnd
      exact hnd.2.2 _ (List.mem_map.mpr ⟨a, List.mem_reverse.mpr ha, rfl⟩) _ (List.mem_cons_self ..) hai
    obtain ⟨b', hb'⟩ := setSearch_complete ext ((i, nd) :: acc) b (fun a ha => hc a (List.mem_cons_of_mem _ ha))
      (by simpa using hnd) (by simpa using hk)
    exact firstOk_complete hmem hb'

theorem decSeqComps_complete {β : Type} {E : Env} {n : Nat} {rec : DFrame → Scope → Ty → Node → Except String Val}
    {all : List (String × Scope × Ty)} {fin : List (String × Val) → Except String β}
    {P : ((Entry × Ty) × Node × Val) → Val → Prop} :
    ∀ (comps : List (Entry × Ty)) (res : List ((Entry × Ty) × Node × Val)) (acc : List (String × Val)),
      (res.map (·.1)).Sublist comps →
      (∀ r ∈ res, tagMatches E n r.1.1.scope r.1.2 r.2.1.tag = true) →
      (∀ r ∈ res, ∀ fr, ∃ x, rec fr r.1.1.scope r.1.2 r.2.1 = .ok x ∧ P r x) →
      (∀ cs', List.Forall₂ (fun r q => q.1 = r.1.1.name ∧ P r q.2) res cs' → ∃ b, fin (acc ++ cs') = .ok b) →
      ∃ b, decSeqComps E n rec all fin comps (res.map (·.2.1)) acc = .ok b
  | [], res, acc, hs, _, _, hf => by
    have : res = [] := by simpa using List.sublist_nil.mp hs
    subst this
    obtain ⟨b, hb⟩ := hf [] .nil
    exact ⟨b, by simpa [decSeqComps] using hb⟩
  | (en, ty) :: comps, [], acc, _, _, _, hf => by
    simp only [List.map_nil, decSeqComps]
    exact decSeqComps_complete comps [] acc (by simp) (by simp) (by simp) hf
  | (en, ty) :: comps, r :: res, acc, hs, ht, hr, hf => by
    simp only [List.map_cons, decSeqComps]
    have skip : (r.1 :: res.map (·.1)).Sublist comps →
        ∃ b, decSeqComps E n rec all fin comps (r.2.1 :: res.map (·.2.1)) acc = .ok b := fun hs' =>
      by simpa using decSeqComps_complete comps (r :: res) acc (by simpa using hs') ht hr hf
    rcases List.sublist_cons_iff.mp (by simpa using hs) with hs' | ⟨l, hl, hs'⟩
    · obtain ⟨b, hb⟩ := skip hs'
      split
      · split
        · exact ⟨_, rfl⟩
        · rw [hb]; exact ⟨b, rfl⟩
      · exact ⟨b, hb⟩
    · simp only [List.cons.injEq] at hl
      obtain ⟨hrc, rfl⟩ := hl
      have htm : tagMatches E n en.scope ty r.2.1.tag = true := by
        have := ht r (List.mem_cons_self ..); rw [hrc] at this; exact this
      rw [if_pos htm]
      obtain ⟨x, hx, hpx⟩ := hr r (List.mem_cons_self ..) ⟨.seq, all, acc, en.name⟩
      rw [hrc] at hx
      obtain ⟨b, hb⟩ := decSeqComps_complete comps res (acc ++ [(en.name, x)]) hs'
        (fun r' hr' => ht r' (List.mem_cons_of_mem _ hr')) (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
        (fun cs' hcs => by
          obtain ⟨b, hb⟩ := hf ((en.name, x) :: cs') (.cons ⟨by rw [hrc], hpx⟩ hcs)
          exact ⟨b, by simpa using hb⟩)
      simp only [hx, bind, Except.bind]
      rw [hb]
      exact ⟨b, rfl⟩

/-! ## What the decoder needs of a type and a value -/

mutual
  /-- `Decodable E p n sc t v`: the conditions, beyond `ber`, under which the decoder reads back an
  encoding of `v`. They are properties of a valid schema and of a value of the type:
  - component names are distinct (X.680 25.1, 27.1, 29.1), and so are an enumeration's identifiers
    and numbers (X.680 20.3);
  - IMPLICIT is applied to a type with one tag (X.680 31.2.9: not an untagged CHOICE or open type);
  - an OBJECT IDENTIFIER value has well-formed arcs (X.660), a REAL value is `Wf` (X.680 21.3), a
    character string's characters fit (X.680 41);
  - under CER and DER, an encoded DEFAULT component's default is a simple value (`DefaultDec`).
  Not covered yet: open types, contents constraints, EXTERNAL, the OID-IRI types and the TIME types
  (`False`). -/
  def Decodable (E : Env) (p : Profile) : Nat → Scope → Ty → Val → Prop
    | 0, _, _, _ => True
    | _ + 1, _, .enumerated r e, _ =>
      ((enumNumbers r e).map (·.1)).Nodup ∧ ((enumNumbers r e).map (·.2)).Nodup
    | _ + 1, _, .real, .real r => r.Wf
    | n + 1, sc, .sequence r e r2, .seq cs => CompsDec E p n (compTys E n sc r e r2) cs
    | n + 1, sc, .set r e r2, .seq cs => CompsDec E p n (compTys E n sc r e r2) cs
    | n + 1, sc, .sequenceOf el, .seqOf vs => ∀ x ∈ vs, Decodable E p n sc el x
    | n + 1, sc, .setOf el, .setOf vs => ∀ x ∈ vs, Decodable E p n sc el x
    | n + 1, sc, .choice r e, .choice a x =>
      ∀ alt ∈ altTys E n sc r e, alt.1.name = a → Decodable E p n sc alt.2 x
    | n + 1, sc, .selection nm t, v => match builtin E n sc t with
      | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
        | some alt => Decodable E p n sc' alt.ty v
        | none => True
      | _ => True
    | _ + 1, _, .objectIdentifier, .oid arcs => OidWf arcs
    | _ + 1, _, .oidIri, _ | _ + 1, _, .relativeOidIri, _ => False
    | n + 1, _, .embeddedPdv, v =>
      Decodable E p n (.ofModule assocModule) (.tagged (univ 11) .implicit embeddedPdvAssoc) v
    | n + 1, _, .characterString, v =>
      Decodable E p n (.ofModule assocModule) (.tagged (univ 29) .implicit characterStringAssoc) v
    | _ + 1, _, .external, _ => False
    | _ + 1, _, .restricted k, v => StrBound k v
    | n + 1, sc, .ref name, v => match resolveTy E n sc none name [] with
      | some (sc', t) => Decodable E p n sc' t v
      | none => True
    | n + 1, sc, .extRef mn name, v => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => Decodable E p n sc' t v
      | none => True
    | n + 1, sc, .paramRef mn name args, v => match resolveTy E n sc mn name args with
      | some (sc', t) => Decodable E p n sc' t v
      | none => True
    | n + 1, sc, .tagged _ kind t, v =>
      Decodable E p n sc t v ∧ (isExplicit E n sc kind t = false → ∃ tb, encTags E n sc t = some [tb])
    | n + 1, sc, .constrained t c, v => Decodable E p n sc t v ∧ ∀ ct enc, c ≠ .contents (some ct) enc
    | _ + 1, _, .openType, _ => False
    | n + 1, sc, .classField cls path, v =>
      match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => Decodable E p n sc' t v
      | _ => False
    | n + 1, sc, .fromObjects src path, v => match objSetClass E n sc src with
      | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
        | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => Decodable E p n sc' t v
        | _ => False
      | none => False
    | _ + 1, _, .instanceOf _, _ => False
    | _ + 1, _, .time, _ | _ + 1, _, .date, _ | _ + 1, _, .timeOfDay, _ | _ + 1, _, .dateTime, _
    | _ + 1, _, .duration, _ => False
    | _ + 1, _, _, _ => True

  /-- The components of a SEQUENCE or SET: distinct names; each component of the value, and each
  default value BER may encode for one the value leaves out, is `Decodable`; under CER and DER an
  encoded DEFAULT component satisfies `DefaultDec`. -/
  def CompsDec (E : Env) (p : Profile) (n : Nat) (comps : List (Entry × Ty)) (cs : List (String × Val)) : Prop :=
    (comps.map (·.1.name)).Nodup ∧
    ∀ c ∈ comps, (∀ x, cs.lookup c.1.name = some x → Decodable E p n c.1.scope c.2 x ∧
        (p.restricted = true → DefaultDec E n c.1 x)) ∧
      (∀ x, IsDefault E n c.1 x → Decodable E p n c.1.scope c.2 x)
end

theorem dropWhile_idem {α : Type} (q : α → Bool) : ∀ (l : List α), (l.dropWhile q).dropWhile q = l.dropWhile q
  | [] => rfl
  | a :: l => by
    simp only [List.dropWhile_cons]
    split
    · exact dropWhile_idem q l
    · rename_i h; simp [List.dropWhile_cons, h]

theorem strip_idem (bs : Bits) : stripTrailingZeros (stripTrailingZeros bs) = stripTrailingZeros bs := by
  simp [stripTrailingZeros, dropWhile_idem]

theorem octLeB_complete : ∀ (a b : Octets), octLe a b → octLeB a b = true
  | [], _, _ => rfl
  | x :: as, [], ⟨h1, h2⟩ => by simp [octLeB, h1, octLeB_complete as [] h2]
  | x :: as, y :: bs, h => by
    rcases h with h | ⟨rfl, h⟩
    · simp [octLeB, h]
    · simp [octLeB, octLeB_complete as bs h]

theorem sortedB_of_pairwise {α : Type} {r : α → α → Bool} {R : α → α → Prop} (hR : ∀ a b, R a b → r a b = true) :
    ∀ {l : List α}, l.Pairwise R → sortedB r l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [sortedB, Bool.and_eq_true]
    exact ⟨hR _ _ (List.rel_of_pairwise_cons h (List.mem_cons_self ..)), sortedB_of_pairwise hR h.of_cons⟩

theorem mapM_exists {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := mapM_exists (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]; rfl⟩

theorem tagMatches_of_ber {E : Env} {p : Profile} {n : Nat} {sc : Scope} {t : Ty} {v : Val} {nd : Node}
    (h : ber E p n sc t v nd) : tagMatches E n sc t nd.tag = true := by
  unfold tagMatches
  split
  · rename_i ts hts; exact List.contains_iff_mem.mpr (ber_encTags E p n sc t v nd ts h hts)
  · rfl

theorem eqIsEq_mono (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty), eqIsEq E n sc t = true → eqIsEq E (n + 1) sc t = true
  | 0, _, _, h => by simp [eqIsEq] at h
  | n + 1, sc, t, h => by
    cases t with
    | ref name =>
      simp only [eqIsEq] at h ⊢
      split at h
      · rename_i sc' t' hr; rw [resolveTy_mono hr (Nat.le_succ n)]; exact eqIsEq_mono E n sc' t' h
      · cases h
    | extRef mn name =>
      simp only [eqIsEq] at h ⊢
      split at h
      · rename_i sc' t' hr; rw [resolveTy_mono hr (Nat.le_succ n)]; exact eqIsEq_mono E n sc' t' h
      · cases h
    | paramRef mn name args =>
      simp only [eqIsEq] at h ⊢
      split at h
      · rename_i sc' t' hr; rw [resolveTy_mono hr (Nat.le_succ n)]; exact eqIsEq_mono E n sc' t' h
      · cases h
    | tagged tg k t => simp only [eqIsEq] at h ⊢; exact eqIsEq_mono E n sc t h
    | constrained t c => simp only [eqIsEq] at h ⊢; exact eqIsEq_mono E n sc t h
    | _ => simpa [eqIsEq] using h

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {b : β}, List.Forall₂ R l1 l2 → b ∈ l2 → ∃ a ∈ l1, R a b
  | _, _, _, .nil, hb => absurd hb List.not_mem_nil
  | a :: _, _ :: _, b, .cons h hs, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right hs hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem compTys_ty {E : Env} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)} {r2 : List Comp}
    {c : Entry × Ty} (hc : c ∈ compTys E n sc r e r2) :
    c.2 = c.1.ty ∨ ∃ tg kind, c.2 = .tagged tg kind c.1.ty := by
  unfold compTys at hc
  obtain ⟨⟨en, ts⟩, _, rfl⟩ := List.mem_map.mp hc
  dsimp only
  split
  · split
    · right; exact ⟨_, _, rfl⟩
    · left; rfl
  · left; rfl

theorem eqIsEq_compTy {E : Env} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)} {r2 : List Comp}
    {c : Entry × Ty} (hc : c ∈ compTys E n sc r e r2) (h : eqIsEq E n c.1.scope c.1.ty = true) :
    eqIsEq E (n + 1) c.1.scope c.2 = true := by
  rcases compTys_ty hc with h2 | ⟨tg, kind, h2⟩
  · rw [h2]; exact eqIsEq_mono E n _ _ h
  · rw [h2]; simpa [eqIsEq] using h

/-- The components a SEQUENCE or SET value encodes (X.690 8.9.2, 8.11.2), as `CompEncs` selects
them: in the order of the type, each with its value. -/
theorem compSel_spec {E : Env} {p : Profile} {n : Nat} {cs : List (String × Val)} :
    ∀ {comps : List (Entry × Ty)} {sel : List (Option Val)},
      List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) comps sel →
      (((comps.zip sel).filterMap fun (c, o) => o.map (c, ·)).map (·.1)).Sublist comps ∧
      ∀ q ∈ (comps.zip sel).filterMap (fun (c, o) => o.map (c, ·)), q.1 ∈ comps ∧ CompChoice E p n q.1.1 cs (some q.2)
  | _, _, .nil => ⟨by simp, by simp⟩
  | c :: comps, o :: sel, .cons h hs => by
    obtain ⟨h1, h2⟩ := compSel_spec hs
    cases o with
    | none =>
      simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_none]
      exact ⟨h1.cons _, fun q hq => ⟨List.mem_cons_of_mem _ (h2 q hq).1, (h2 q hq).2⟩⟩
    | some x =>
      simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_some, List.map_cons]
      refine ⟨h1.cons₂ _, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨List.mem_cons_self .., h⟩
      · exact ⟨List.mem_cons_of_mem _ (h2 q hq).1, (h2 q hq).2⟩

theorem forall₂_zip_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ x ∈ l1.zip l2, R x.1 x.2
  | _, _, .nil, x, hx => by simp at hx
  | _, _, .cons h hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h
    · exact forall₂_zip_mem hs x hx

/-- The encodings `CompEncs` relates, with their components and values. -/
theorem sel_res {E : Env} {p : Profile} {n : Nat} :
    ∀ {L : List ((Entry × Ty) × Val)} {out : List ((Entry × Ty) × Node)},
    List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
      r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) L out →
    ∃ res : List ((Entry × Ty) × Node × Val), res.map (·.1) = L.map (·.1) ∧ res.map (·.2.1) = out.map (·.2) ∧
      ∀ r ∈ res, ∃ q ∈ L, ber E p n q.1.1.scope q.1.2 q.2 r.2.1 ∧ r = (q.1, r.2.1, q.2)
  | _, _, .nil => ⟨[], rfl, rfl, by simp⟩
  | q :: L, o :: out, .cons ⟨_, hb⟩ hs => by
    obtain ⟨res, h1, h2, h3⟩ := sel_res hs
    refine ⟨(q.1, o.2, q.2) :: res, by simp [h1], by simp [h2], ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨q, List.mem_cons_self .., hb, rfl⟩
    · obtain ⟨q', hq', h⟩ := h3 r hr
      exact ⟨q', List.mem_cons_of_mem _ hq', h⟩

theorem decodable_sel {E : Env} {p : Profile} {n : Nat} {comps : List (Entry × Ty)} {cs : List (String × Val)}
    {L : List ((Entry × Ty) × Val)}
    (hcomp : ∀ c ∈ comps, (∀ x, cs.lookup c.1.name = some x → Decodable E p n c.1.scope c.2 x ∧
        (p.restricted = true → DefaultDec E n c.1 x)) ∧ (∀ x, IsDefault E n c.1 x → Decodable E p n c.1.scope c.2 x))
    (hmem : ∀ q ∈ L, q.1 ∈ comps ∧ CompChoice E p n q.1.1 cs (some q.2)) :
    ∀ q ∈ L, Decodable E p n q.1.1.scope q.1.2 q.2 := by
  intro q hq
  obtain ⟨hc, hch⟩ := hmem q hq
  simp only [CompChoice] at hch
  split at hch
  · rename_i y hy
    rw [hch.1]; exact ((hcomp _ hc).1 y hy).1
  · exact (hcomp _ hc).2 _ hch.2

theorem forall₂_lookup {α : Type} {Q : α → Val → Prop} {name : α → String} :
    ∀ {res : List α} {cs' : List (String × Val)} {k : String} {x : Val},
      List.Forall₂ (fun r q => q.1 = name r ∧ Q r q.2) res cs' → cs'.lookup k = some x →
      ∃ r ∈ res, name r = k ∧ Q r x
  | _, _, _, _, .nil, h => by simp at h
  | r :: res, (nm, y) :: cs', k, x, .cons ⟨h1, h2⟩ hs, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨r, List.mem_cons_self .., by simp only at h1; rw [← h1]; exact (eq_of_beq hk).symm, h2⟩
    · obtain ⟨r', hr', h3, h4⟩ := forall₂_lookup hs h
      exact ⟨r', List.mem_cons_of_mem _ hr', h3, h4⟩

theorem notDefault_of_sel {E : Env} {p : Profile} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)}
    {r2 : List Comp} {cs : List (String × Val)} {c : Entry × Ty} {x x' : Val}
    (hp : p.restricted = true) (hch : CompChoice E p n c.1 cs (some x))
    (hcomp : ∀ c ∈ compTys E n sc r e r2, (∀ x, cs.lookup c.1.name = some x → Decodable E p n c.1.scope c.2 x ∧
        (p.restricted = true → DefaultDec E n c.1 x)) ∧ (∀ x, IsDefault E n c.1 x → Decodable E p n c.1.scope c.2 x))
    (hc : c ∈ compTys E n sc r e r2) (hP : eqIsEq E (n + 1) c.1.scope c.2 = true → x' = x) :
    notDefaultB E n c.1 x' = true := by
  simp only [CompChoice] at hch
  split at hch
  · rename_i y hy
    obtain ⟨rfl, hnot⟩ := hch
    have hdd := ((hcomp c hc).1 x hy).2 hp
    have hnot := hnot hp
    have hx := notDefaultB_complete hdd hnot
    unfold DefaultDec at hdd
    unfold notDefaultB at hx ⊢
    split
    · rename_i d hd
      rw [hd] at hdd
      obtain ⟨d', _, heq, _⟩ := hdd
      rw [hP (eqIsEq_compTy hc heq)]
      rw [hd] at hx; exact hx
    · rfl
  · rw [hp] at hch; exact absurd hch.1 (by simp)

theorem mapM_exists' {ε α β : Type} {f : α → Except ε β} {Q : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b ∧ Q a b) → ∃ bs, l.mapM f = .ok bs ∧ List.Forall₂ Q l bs
  | [], _ => ⟨[], rfl, .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb, hq⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs, hf⟩ := mapM_exists' (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]; rfl, .cons hq hf⟩

/-- Components of `comps`, by index. -/
theorem exists_indices {β : Type} {comps : List (Entry × Ty)} :
    ∀ {l : List ((Entry × Ty) × β)}, (∀ a ∈ l, a.1 ∈ comps) →
      ∃ found : List (Fin comps.length × β), found.map (fun a => (comps[a.1], a.2)) = l
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨i, hi, hc⟩ := List.mem_iff_getElem.mp (h a (List.mem_cons_self ..))
    obtain ⟨found, hf⟩ := exists_indices (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨(⟨i, hi⟩, a.2) :: found, ?_⟩
    rw [List.map_cons, hf]
    simp [hc]

theorem forall₂_map_fst {α β γ : Type} :
    ∀ {L : List (α × β)} {out : List (α × γ)}, List.Forall₂ (fun q r => r.1 = q.1) L out → out.map (·.1) = L.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [h, forall₂_map_fst hs]

theorem setSearch_complete' {L : Nat} {β : Type} {cand : Node → List (Fin L)} {k : List (Fin L × Node) → Except String β}
    (ext : List (Fin L × Node)) (acc : List (Fin L × Node)) (hc : ∀ a ∈ ext, a.1 ∈ cand a.2)
    (hnd : ((acc.reverse ++ ext).map (·.1)).Nodup) (hk : ∃ b, k (acc.reverse ++ ext) = .ok b) :
    ∃ b', setSearch cand k (ext.map (·.2)) acc = .ok b' := by
  obtain ⟨b, hb⟩ := hk
  exact setSearch_complete ext acc b hc hnd hb

theorem decodable_time {E : Env} {p : Profile} {n : Nat} {sc : Scope} {t : Ty} {v : Val} {k : TimeKind}
    (hk : timeKind? t = some k) (hD : Decodable E p (n + 1) sc t v) : False := by
  cases t <;> simp_all [timeKind?, Decodable]

set_option maxHeartbeats 8000000 in
/-- **Completeness**: an encoding `ber` relates to a `Decodable` value is decoded, to that value if
the type's values are equal only when the same (`eqIsEq`). -/
theorem dec_complete (E : Env) (p : Profile) : ∀ (n : Nat) (frames : List DFrame) (hint : Option (Scope × Ty))
    (sc : Scope) (t : Ty) (v : Val) (nd : Node), ber E p n sc t v nd → Decodable E p n sc t v →
    ∃ v', dec E p n frames hint sc t nd = .ok v' ∧ (eqIsEq E (n + 1) sc t = true → v' = v)
  | 0, _, _, _, _, _, _, h, _ => h.elim
  | n + 1, frames, hint, sc, t, v, nd, h, hD => by
    have IH : ∀ {fr hi sc t v nd}, ber E p n sc t v nd → Decodable E p n sc t v →
        ∃ v', dec E p n fr hi sc t nd = .ok v' ∧ (eqIsEq E (n + 1) sc t = true → v' = v) :=
      fun h hD => dec_complete E p n _ _ _ _ _ _ h hD
    unfold ber at h
    split at h
    all_goals try (have hn := Nat.succ_injective (by assumption : n + 1 = _); subst hn)
    next => exact h.elim
    next => -- BOOLEAN
      rename_i b _
      obtain ⟨f, cs, rfl, o, rfl, hb⟩ := h
      simp only [univ, dec]
      refine ⟨.bool (o.val != 0), ?_, fun _ => ?_⟩
      · have : (p.restricted && o.val != 0 && o.val != 255) = false := by
          cases hp : p.restricted
          · rfl
          · cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hb
            · simp [hb]
            · rw [hb.2 hp]; simp
        simp only [this, Bool.false_eq_true, ↓reduceIte]
      · cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hb
        · simp [hb]
        · simp only [Val.bool.injEq, bne_iff_ne, ne_eq]; intro h0; exact hb.1 (Fin.ext h0)
    next => -- INTEGER
      obtain ⟨f, cs, rfl, hi⟩ := h
      obtain ⟨h1, h2⟩ := intContentsB_complete hi
      simp only [univ, dec, h1, ↓reduceIte, h2]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- ENUMERATED
      obtain ⟨k, hk, f, cs, rfl, hi⟩ := h
      simp only [Decodable] at hD
      obtain ⟨h1, h2⟩ := intContentsB_complete hi
      simp only [univ, dec, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2]
      rename_i r e id _
      have hmem : (id, k) ∈ enumNumbers r e := by
        obtain ⟨l1, l2, hl, _⟩ := List.lookup_eq_some_iff.mp hk
        rw [hl]; simp
      obtain ⟨⟨id', k'⟩, hf⟩ : ∃ q, (enumNumbers r e).find? (·.2 == k) = some q :=
        Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(id, k), hmem, by simp⟩)
      have hq := List.find?_some hf
      simp only [beq_iff_eq] at hq
      subst hq
      have hmem' := List.mem_of_find?_eq_some hf
      have hid : id' = id := by
        have := List.inj_on_of_nodup_map hD.2 hmem' hmem rfl
        simp only [Prod.mk.injEq] at this; exact this.1
      subst hid
      simp only [hf, guardE, hk, beq_self_eq_true, ↓reduceIte]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- REAL
      obtain ⟨f, cs, rfl, hr⟩ := h
      simp only [Decodable] at hD
      simp only [univ, dec, decReal_complete hr hD]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- BIT STRING
      obtain ⟨bs', hbs, he⟩ := h
      rename_i named bs _
      simp only [dec, decBits_complete p _ _ _ _ _ he, bind, Except.bind]
      have hc : (named != [] && p.restricted && bs' != stripTrailingZeros bs') = false := by
        by_cases hn : named = []
        · simp [hn]
        · cases hp : p.restricted
          · simp
          · simp only [hn, ↓reduceIte, hp] at hbs
            subst hbs; simp [strip_idem]
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, fun hq => ?_⟩
      simp only [eqIsEq, List.isEmpty_iff] at hq
      simp only [hq, ↓reduceIte] at hbs
      rw [hbs]
    next => -- OCTET STRING
      simp only [dec, decOctets_complete p _ _ _ _ h]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- NULL
      obtain ⟨f, cs, rfl, rfl⟩ := h
      simp only [univ, dec]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- SEQUENCE
      rename_i sc nd _ _ _ _ _ r e r2 cs _
      obtain ⟨f, out, rfl, _, sel, hsel, hout⟩ := h
      simp only [Decodable, CompsDec] at hD
      obtain ⟨hnd, hcomp⟩ := hD
      obtain ⟨hsub, hmem⟩ := compSel_spec hsel
      have hlen := hout.length_eq
      obtain ⟨res, hres1, hres2, hres3⟩ := sel_res hout
      have hval : ∀ q ∈ (((compTys E n sc r e r2).zip sel).filterMap fun (c, o) => o.map (c, ·)),
          Decodable E p n q.1.1.scope q.1.2 q.2 := fun q hq => decodable_sel hcomp hmem q hq
      simp only [univ, dec, decide_eq_true hnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← hres2]
      obtain ⟨b, hb⟩ := decSeqComps_complete (P := fun r x => eqIsEq E (n + 1) r.1.1.scope r.1.2 = true → x = r.2.2)
        (rec := fun fr sc' t nd => dec E p n (fr :: frames) none sc' t nd)
        (all := (compTys E n sc r e r2).map fun (en, ty) => (en.name, en.scope, ty))
        (fin := fun cs => match p.restricted, defaultErr E n (compTys E n sc r e r2) cs with
          | true, some m => .error m
          | _, _ => .ok (Val.seq cs))
        (compTys E n sc r e r2) res [] (by rw [hres1]; exact hsub)
        (fun r hr => by
          obtain ⟨q, hq, hb, hr'⟩ := hres3 r hr
          have e1 : r.1 = q.1 := by rw [hr']
          rw [e1]; exact tagMatches_of_ber hb)
        (fun r hr fr => by
          obtain ⟨q, hq, hb, hr'⟩ := hres3 r hr
          have e1 : r.1 = q.1 := by rw [hr']
          have e2 : r.2.2 = q.2 := by rw [hr']
          obtain ⟨y, hy, hy'⟩ := IH (fr := fr :: frames) (hi := none) hb (hval q hq)
          rw [e1, e2]; exact ⟨y, hy, hy'⟩)
        (fun cs' hcs => by
          simp only [List.nil_append]
          cases hp : p.restricted
          · exact ⟨_, rfl⟩
          · rw [defaultErr_none_complete]
            · exact ⟨_, rfl⟩
            intro c hc x' hx'
            obtain ⟨r', hr', hname, hP⟩ := forall₂_lookup (name := fun r : (Entry × Ty) × Node × Val => r.1.1.name)
              (Q := fun r x => eqIsEq E (n + 1) r.1.1.scope r.1.2 = true → x = r.2.2) hcs hx'
            obtain ⟨q, hq, _, hr''⟩ := hres3 r' hr'
            have e1 : r'.1 = q.1 := by rw [hr'']
            have e2 : r'.2.2 = q.2 := by rw [hr'']
            rw [e1] at hname hP; rw [e2] at hP
            have hqc : q.1 = c := by
              have h1 : q.1 ∈ compTys E n sc r e r2 := (hmem q hq).1
              exact List.inj_on_of_nodup_map hnd h1 hc hname
            subst hqc
            exact notDefault_of_sel hp (hmem q hq).2 hcomp (hmem q hq).1 hP)
      exact ⟨b, hb, fun hq => by simp [eqIsEq] at hq⟩
    next => -- SEQUENCE OF
      obtain ⟨f, ch, rfl, hf⟩ := h
      simp only [Decodable] at hD
      obtain ⟨ys, hys⟩ := mapM_exists (f := fun c => dec E p n (⟨.seqOf, [], [], ""⟩ :: frames) none _ _ c)
        (fun c hc => by
          obtain ⟨x, hx, hb⟩ := forall₂_mem_right hf hc
          obtain ⟨y, hy, _⟩ := IH hb (hD x hx)
          exact ⟨y, hy⟩)
      simp only [univ, dec, hys]
      exact ⟨_, rfl, fun hq => by simp [eqIsEq] at hq⟩
    next => -- SET
      rename_i sc nd _ _ _ _ _ r e r2 cs _
      obtain ⟨f, out, out', rfl, ⟨_, sel, hsel, hout⟩, hperm, hder, hcer⟩ := h
      simp only [Decodable, CompsDec] at hD
      obtain ⟨hnd, hcomp⟩ := hD
      obtain ⟨hsub, hmem⟩ := compSel_spec hsel
      have hval := decodable_sel hcomp hmem
      generalize ((compTys E n sc r e r2).zip sel).filterMap (fun (c, o) => o.map (c, ·)) = L at hout hsub hmem hval
      have hcnd : (compTys E n sc r e r2).Nodup := List.Nodup.of_map _ hnd
      -- each encoding with the component it is, and its value
      have hout1 : out'.map (·.1) = L.map (·.1) :=
        forall₂_map_fst (hout.imp (fun _ _ h => h.1))
      have hin : ∀ a ∈ out, ∃ q ∈ L,
          q.1 = a.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 a.2 := by
        intro a ha
        obtain ⟨q, hq, h1, h2⟩ := forall₂_mem_right hout (hperm.subset ha)
        exact ⟨q, hq, h1.symm, h2⟩
      obtain ⟨found, hfound⟩ := exists_indices (comps := compTys E n sc r e r2) (l := out) (fun a ha => by
        obtain ⟨q, hq, h1, _⟩ := hin a ha; rw [← h1]; exact (hmem q hq).1)
      have hch : found.map (·.2) = out.map (·.2) := by rw [← hfound]; simp
      have hnodup : (found.map (·.1)).Nodup := by
        have h1 : (out'.map (·.1)).Nodup := by rw [hout1]; exact hsub.nodup hcnd
        have h2 : (out.map (·.1)).Nodup := (hperm.map _).nodup_iff.mpr h1
        rw [← hfound, List.map_map] at h2
        have h3 : List.map ((fun x => x.1) ∘ fun a => ((compTys E n sc r e r2)[a.1], a.2)) found =
            (found.map (·.1)).map (fun i => (compTys E n sc r e r2)[i]) := by simp [Function.comp_def]
        rw [h3] at h2
        exact List.Nodup.of_map _ h2
      simp only [univ, dec, decide_eq_true hnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← hch]
      refine (fun ⟨b', hb'⟩ => ⟨b', hb', fun hq => by simp [eqIsEq] at hq⟩)
        (setSearch_complete' found [] ?_ (by simpa using hnodup) ?_)
      · intro a ha
        refine List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩
        have hao : ((compTys E n sc r e r2)[a.1], a.2) ∈ out := by rw [← hfound]; exact List.mem_map_of_mem ha
        obtain ⟨q, _, h1, h2⟩ := hin _ hao
        rw [h1] at h2
        exact tagMatches_of_ber h2
      · simp only [List.reverse_nil, List.nil_append]
        have hperm' := List.mergeSort_perm found (fun a b => decide (a.1 ≤ b.1))
        have hsorted : sortedB (fun a b => decide (a < b))
            ((found.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.1)) = true := by
          have hp1 := List.pairwise_mergeSort (le := fun (a b : Fin (compTys E n sc r e r2).length × Node) =>
            decide (a.1 ≤ b.1)) (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
            (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) found
          have hp2 : ((found.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.1)).Nodup :=
            (hperm'.map _).nodup_iff.mpr hnodup
          refine sortedB_of_pairwise (R := fun a b => a < b) (fun a b h => decide_eq_true h) ?_
          rw [List.pairwise_map]
          rw [List.Nodup, List.pairwise_map] at hp2
          exact (hp1.and hp2).imp fun h => by
            have := h.1; simp only [decide_eq_true_eq] at this; exact lt_of_le_of_ne this h.2
        simp only [hsorted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨cs', hcs', hF⟩ := mapM_exists' (l := found.mergeSort fun a b => decide (a.1 ≤ b.1))
          (Q := fun (a : Fin (compTys E n sc r e r2).length × Node) (b : String × Val) =>
            b.1 = (compTys E n sc r e r2)[a.1].1.name ∧
            ∃ q ∈ L,
              q.1 = (compTys E n sc r e r2)[a.1] ∧
              (eqIsEq E (n + 1) (compTys E n sc r e r2)[a.1].1.scope (compTys E n sc r e r2)[a.1].2 = true → b.2 = q.2))
          (f := fun (x : Fin (compTys E n sc r e r2).length × Node) => do
            let x_1 ← dec E p n ((⟨FrameKind.set, List.map (fun x => (x.1.name, x.1.scope, x.2))
              (compTys E n sc r e r2), [], (compTys E n sc r e r2)[x.1].1.name⟩ : DFrame) :: frames) none
              (compTys E n sc r e r2)[x.1].1.scope (compTys E n sc r e r2)[x.1].2 x.2
            Except.ok ((compTys E n sc r e r2)[x.1].1.name, x_1))
          (fun a ha => by
            have hao : ((compTys E n sc r e r2)[a.1], a.2) ∈ out := by
              rw [← hfound]; exact List.mem_map_of_mem (hperm'.subset ha)
            obtain ⟨q, hq, h1, h2⟩ := hin _ hao
            simp only at h1
            rw [h1] at h2
            obtain ⟨y, hy, hy'⟩ := IH (fr := (⟨FrameKind.set, List.map (fun x => (x.1.name, x.1.scope, x.2))
              (compTys E n sc r e r2), [], (compTys E n sc r e r2)[a.1].1.name⟩ : DFrame) :: frames)
              (hi := none) h2 (by rw [← h1]; exact hval q hq)
            refine ⟨_, by simp only [hy, bind, Except.bind]; rfl, rfl, q, hq, h1, ?_⟩
            exact hy')
        rw [hcs']
        simp only [bind, Except.bind]
        have hd : (decide (p = Profile.der) && !sortedB (fun a b => a.tag.lt b.tag) (found.map (·.2))) = false := by
          cases hp : decide (p = Profile.der)
          · rfl
          · simp only [Bool.true_and, Bool.not_eq_false']
            rw [hch]
            have := hder (of_decide_eq_true hp)
            exact sortedB_of_pairwise (R := fun a b : Node => Tag.lt a.tag b.tag = true) (fun _ _ h => h)
              (by rw [List.pairwise_map]; exact this)
        have hc : (decide (p = Profile.cer) && !sortedB (fun (a b : Fin (compTys E n sc r e r2).length × Node) =>
            ((cerKey E n (compTys E n sc r e r2)[a.1].1.scope (compTys E n sc r e r2)[a.1].2).getD a.2.tag).lt
              ((cerKey E n (compTys E n sc r e r2)[b.1].1.scope (compTys E n sc r e r2)[b.1].2).getD b.2.tag))
            found) = false := by
          cases hp : decide (p = Profile.cer)
          · rfl
          · simp only [Bool.true_and, Bool.not_eq_false']
            have := hcer (of_decide_eq_true hp)
            rw [← hfound, List.pairwise_map] at this
            exact sortedB_of_pairwise (fun _ _ h => h) this
        simp only [hd, hc, Bool.false_eq_true, ↓reduceIte]
        cases hp : p.restricted
        · exact ⟨_, rfl⟩
        · rw [defaultErr_none_complete]
          · exact ⟨_, rfl⟩
          intro c hc' x' hx'
          obtain ⟨a, _, hname, q, hq, hqa, hP⟩ := forall₂_lookup
            (name := fun a : Fin (compTys E n sc r e r2).length × Node => (compTys E n sc r e r2)[a.1].1.name)
            (Q := fun (a : Fin (compTys E n sc r e r2).length × Node) (x : Val) => ∃ q ∈ L,
              q.1 = (compTys E n sc r e r2)[a.1] ∧
              (eqIsEq E (n + 1) (compTys E n sc r e r2)[a.1].1.scope (compTys E n sc r e r2)[a.1].2 = true → x = q.2))
            hF hx'
          have hac : (compTys E n sc r e r2)[a.1] = c :=
            List.inj_on_of_nodup_map hnd (List.getElem_mem _) hc' hname
          rw [hac] at hqa hP
          subst hqa
          exact notDefault_of_sel hp (hmem q hq).2 hcomp (hmem q hq).1 hP
    next => -- SET OF
      obtain ⟨f, ch, ch', rfl, hf, hperm, hord⟩ := h
      simp only [Decodable] at hD
      obtain ⟨ys, hys⟩ := mapM_exists (f := fun c => dec E p n (⟨.setOf, [], [], ""⟩ :: frames) none _ _ c)
        (fun c hc => by
          obtain ⟨x, hx, hb⟩ := forall₂_mem_right hf (hperm.subset hc)
          obtain ⟨y, hy, _⟩ := IH hb (hD x hx)
          exact ⟨y, hy⟩)
      simp only [univ, dec, hys, bind, Except.bind]
      have hc : (p.restricted && !sortedB (fun a b => octLeB a.octets b.octets) ch) = false := by
        cases hp : p.restricted
        · rfl
        · simp only [Bool.true_and, Bool.not_eq_false']
          exact sortedB_of_pairwise (fun a b h => octLeB_complete _ _ h) (hord hp)
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, fun hq => by simp [eqIsEq] at hq⟩
    next => -- CHOICE
      rename_i sc nd _ _ _ _ _ r e a x _
      obtain ⟨alt, halt, hname, hb⟩ := h
      simp only [Decodable] at hD
      obtain ⟨y, hy, _⟩ := IH (fr := ⟨.choice, (choiceAlts r e).map fun a => (a.name, sc, a.ty), [], alt.1.name⟩ :: frames) (hi := none) hb (hD alt halt hname)
      have hmem : alt ∈ (altTys E n sc r e).filter fun alt => tagMatches E n sc alt.2 nd.tag :=
        List.mem_filter.mpr ⟨halt, tagMatches_of_ber hb⟩
      obtain ⟨v', hv'⟩ := firstOk_complete (err := s!"8.13: no alternative has tag {repr nd.tag}")
        (f := fun (alt : Alt × Ty) => (dec E p n (⟨.choice, (choiceAlts r e).map fun a => (a.name, sc, a.ty), [], alt.1.name⟩ :: frames) none sc alt.2 nd).map
          (Val.choice alt.1.name)) hmem (by simp only [hy]; rfl)
      simp only [dec]
      exact ⟨v', hv', fun hq => by simp [eqIsEq] at hq⟩
    next => -- selection
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      · rename_i sc' root ext hb
        rw [hb] at hD ⊢; dsimp only at hD ⊢
        split at h
        · rename_i alt ha
          rw [ha] at hD ⊢
          obtain ⟨y, hy, _⟩ := IH h hD
          exact ⟨y, hy, fun hq => by simp [eqIsEq] at hq⟩
        · exact h.elim
      · exact h.elim
    next => -- OBJECT IDENTIFIER
      obtain ⟨f, cs, rfl, rfl⟩ := h
      simp only [Decodable] at hD
      simp only [univ, dec, decOidArcs_complete hD]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- RELATIVE-OID
      obtain ⟨f, cs, rfl, rfl⟩ := h
      simp only [univ, dec, decOidArcs_rel_complete]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => simp [Decodable] at hD
    next => simp [Decodable] at hD
    next => -- EMBEDDED PDV
      simp only [Decodable] at hD
      obtain ⟨y, hy, _⟩ := IH (fr := []) (hi := none) h hD
      simp only [dec]
      exact ⟨y, hy, fun hq => by simp [eqIsEq] at hq⟩
    next => -- CHARACTER STRING
      simp only [Decodable] at hD
      obtain ⟨y, hy, _⟩ := IH (fr := []) (hi := none) h hD
      simp only [dec]
      exact ⟨y, hy, fun hq => by simp [eqIsEq] at hq⟩
    next => simp [Decodable] at hD
    next => -- restricted character strings
      obtain ⟨os, hso, tg, hu, ho⟩ := h
      simp only [Decodable] at hD
      simp only [dec, hu, Option.getD_some, decOctets_complete p _ _ _ _ ho, bind, Except.bind,
        decString_complete hso hD]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- GeneralizedTime
      obtain ⟨hcan, os, hso, ho⟩ := h
      simp only [dec, decOctets_complete p _ _ _ _ ho, bind, Except.bind, decString_complete hso trivial, guardE]
      rename_i cs _
      have : (!p.restricted || genTimeCanonB (List.map Char.ofNat cs)) = true := by
        cases hp : p.restricted
        · rfl
        · simp [genTimeCanonB_complete (hcan hp)]
      simp only [this, ↓reduceIte]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- UTCTime
      obtain ⟨hcan, os, hso, ho⟩ := h
      simp only [dec, decOctets_complete p _ _ _ _ ho, bind, Except.bind, decString_complete hso trivial, guardE]
      rename_i cs _
      have : (!p.restricted || utcTimeCanonB (List.map Char.ofNat cs)) = true := by
        cases hp : p.restricted
        · rfl
        · simp [utcTimeCanonB_complete (hcan hp)]
      simp only [this, ↓reduceIte]
      exact ⟨_, rfl, fun _ => rfl⟩
    next => -- ObjectDescriptor
      obtain ⟨os, hso, ho⟩ := h
      simp only [dec, decOctets_complete p _ _ _ _ ho, bind, Except.bind, decString_complete hso trivial]
      exact ⟨_, rfl, fun hq => by simp [eqIsEq] at hq⟩
    next => -- reference
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      · rename_i sc' t' hr
        rw [hr] at hD ⊢; dsimp only at hD ⊢
        obtain ⟨y, hy, hq⟩ := IH h hD
        refine ⟨y, hy, fun he => hq ?_⟩
        simp only [eqIsEq, resolveTy_mono hr (Nat.le_succ n)] at he; exact he
      · exact h.elim
    next => -- reference
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      · rename_i sc' t' hr
        rw [hr] at hD ⊢; dsimp only at hD ⊢
        obtain ⟨y, hy, hq⟩ := IH h hD
        refine ⟨y, hy, fun he => hq ?_⟩
        simp only [eqIsEq, resolveTy_mono hr (Nat.le_succ n)] at he; exact he
      · exact h.elim
    next => -- reference
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      · rename_i sc' t' hr
        rw [hr] at hD ⊢; dsimp only at hD ⊢
        obtain ⟨y, hy, hq⟩ := IH h hD
        refine ⟨y, hy, fun he => hq ?_⟩
        simp only [eqIsEq, resolveTy_mono hr (Nat.le_succ n)] at he; exact he
      · exact h.elim
    next => -- tagging
      rename_i tg kind t _
      simp only [Decodable] at hD
      obtain ⟨hD, himp⟩ := hD
      obtain ⟨base, hb, hnd⟩ := h
      simp only [dec]
      split
      · rename_i hx
        simp only [hx, ↓reduceIte] at hnd
        obtain ⟨f, rfl⟩ := hnd
        simp only [beq_self_eq_true, ↓reduceIte]
        obtain ⟨y, hy, hq⟩ := IH hb hD
        exact ⟨y, hy, fun he => hq (by simpa [eqIsEq] using he)⟩
      · rename_i hx
        simp only [hx, Bool.false_eq_true, ↓reduceIte] at hnd
        subst hnd
        obtain ⟨tb, htb⟩ := himp (by simpa using hx)
        have hbt : base.tag = tb := by simpa using ber_encTags E p n _ t _ base [tb] hb htb
        simp only [Node.tag_retag, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, htb, Node.retag_retag]
        rw [← hbt, Node.retag_tag]
        obtain ⟨y, hy, hq⟩ := IH hb hD
        exact ⟨y, hy, fun he => hq (by simpa [eqIsEq] using he)⟩
    next => -- constraints
      rename_i t c _
      simp only [Decodable] at hD
      obtain ⟨hD, hc⟩ := hD
      obtain ⟨y, hy, hq⟩ := IH (fr := frames) (hi := tableHint E n frames _ t c) h hD
      simp only [dec]
      rw [show (dec E p n frames (tableHint E n frames _ t c) _ t _) = .ok y from hy]
      refine ⟨y, ?_, fun he => hq (by simpa [eqIsEq] using he)⟩
      cases c with
      | contents ct enc =>
        cases ct with
        | none => rfl
        | some ct => exact absurd rfl (hc ct enc)
      | _ => rfl
    next => simp [Decodable] at hD
    next => -- class field
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      all_goals first
        | exact h.elim
        | (rename_i hcf; rw [hcf] at hD ⊢; dsimp only at hD ⊢
           try (obtain ⟨y, hy, _⟩ := IH h hD; exact ⟨y, hy, fun he => by simp [eqIsEq] at he⟩)
           try exact hD.elim)
    next => -- object set column
      simp only [Decodable] at hD
      simp only [dec]
      split at h
      · rename_i csc cls hs
        rw [hs] at hD ⊢; dsimp only at hD ⊢
        split at h
        · rename_i hcf; rw [hcf] at hD ⊢; dsimp only at hD ⊢
          obtain ⟨y, hy, _⟩ := IH h hD; exact ⟨y, hy, fun he => by simp [eqIsEq] at he⟩
        · rename_i hcf; rw [hcf] at hD ⊢; dsimp only at hD ⊢
          obtain ⟨y, hy, _⟩ := IH h hD; exact ⟨y, hy, fun he => by simp [eqIsEq] at he⟩
        · rename_i fs n1 n2 hcf
          rw [hcf] at hD
          cases fs <;> first | exact hD.elim | exact (n1 _ _ _ _ rfl).elim | exact (n2 _ _ _ rfl).elim
        · exact h.elim
      · exact h.elim
    next => simp [Decodable] at hD
    next => -- time types
      split at h
      · rename_i k tg hk _
        exact (decodable_time hk hD).elim
      · exact h.elim
    next => exact h.elim

/-- **Completeness of `decode`**: the octets of an encoding `ber` relates to a `Decodable` value,
with length forms the profile allows and no primitive UNIVERSAL 0, are decoded by `dec` to a value
`v'` (`v` itself when the type's values are equal only when the same), and `decode` returns `v'`
unless the value checks (`valSemB`, `presentOkB`) reject it. -/
theorem decode_complete {E : Env} {p : Profile} {fuel : Nat} {m : Module} {t : Ty} {v : Val} {nd : Node}
    (h : ber E p fuel (.ofModule m) t v nd) (hl : nd.LenOk p) (hn : nd.NoEoc)
    (hD : Decodable E p fuel (.ofModule m) t v) :
    ∃ v', dec E p fuel [] none (.ofModule m) t nd = .ok v' ∧
      (valSemB E fuel (.ofModule m) t v' = true → presentOkB E fuel (.ofModule m) t v' = true →
        decode E p fuel m t nd.octets = .ok v') ∧
      (eqIsEq E (fuel + 1) (.ofModule m) t = true → v' = v) := by
  obtain ⟨v', hv', hq⟩ := dec_complete E p fuel [] none _ t v nd h hD
  refine ⟨v', hv', fun h1 h2 => ?_, hq⟩
  obtain ⟨hp, hlb⟩ := parse_octets_self hl hn
  unfold decode
  rw [hp]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlb, hv', bind, Except.bind,
    h1, h2]

end Asn1.X690
