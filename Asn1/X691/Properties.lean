import Asn1.X691.Encode
import Asn1.X690.Iso2022
import Asn1.X691.DecCompleteStruct

/-!
# Properties of PER as a relation

X.691 7.5: CANONICAL-PER restricts the options BASIC-PER leaves the sender. `per_canonical_basic`:
every field-list CANONICAL-PER relates to a value, BASIC-PER (same variant otherwise) relates to it
too. The differences are exactly the sender's options: DEFAULT components (19.5), the order of a SET
OF (22.1), and the character string encodings of 30.6 (X.690 11.4 ⊆ 8.23.5, `iso2022Decode_canon`).

OPEN (ledger X691-21): the same statement for `X691.rule` (`EncodingRule.Refines`) is not proved, and
under our reading of X.682 11.4 it fails in general: the value set of a type with a contents
constraint is given by the encodings of the rules in use (`perHook v`), so a type that excludes
such values by set arithmetic (`OCTET STRING (ALL EXCEPT C)`, `C ::= OCTET STRING (CONTAINING T)`)
has values under CANONICAL-PER that it does not have under BASIC-PER.

X.691 7.9: PER encodings are self-delimiting given the type. `per_prefixFree`: for values the
decoder reads back (`PDec`), no complete encoding is a proper prefix of another; as with
`per_unambiguous`, because one run of the decoder on one input has one result.
-/

open Asn1 Asn1.X680
namespace Asn1.X691

theorem stringOctets_basic {k : StrType} {x : Val} {os : Octets} (h : X690.StringOctets .der k x os) :
    X690.StringOctets .ber k x os := by
  unfold X690.StringOctets at h ⊢
  split at h
  · exact h
  · obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    exact X690.iso2022Decode_canon k _ _ _ _ _ h2
  · exact h

theorem otherString_basic {al : Bool} {k : StrType} {x : Val} {fl : FieldList}
    (h : OtherStringFields ⟨al, true⟩ k x fl) : OtherStringFields ⟨al, false⟩ k x fl := by
  obtain ⟨os, h1, h2⟩ := h
  exact ⟨os, stringOctets_basic h1, h2⟩

theorem external_basic {al : Bool} {x : Val} {fl : FieldList}
    (h : ExternalFields ⟨al, true⟩ x fl) : ExternalFields ⟨al, false⟩ x fl := by
  obtain ⟨ident, data, h1, dref, iref, h2, descF, h3, alt, h4, h5⟩ := h
  refine ⟨ident, data, h1, dref, iref, h2, descF, ?_, alt, h4, h5⟩
  revert h3; cases x <;> simp only [imp_self]
  rename_i cs
  split
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, otherString_basic hf, rfl⟩
  · exact id

theorem compOut_basic {E : Env} {al : Bool} {n : Nat} {rec rec' : Scope → Ty → Val → FieldList → Prop}
    (hr : ∀ sc t x fl, rec sc t x fl → rec' sc t x fl) {root : Bool} {cs : List (String × Val)} {en : Entry}
    {out : Option FieldList} (h : CompOut E ⟨al, true⟩ n rec root cs en out) :
    CompOut E ⟨al, false⟩ n rec' root cs en out := by
  unfold CompOut at h ⊢
  have henc : ∀ x, (∃ fl, rec en.scope en.ty x fl ∧ out = some fl) → ∃ fl, rec' en.scope en.ty x fl ∧ out = some fl :=
    fun x ⟨fl, h1, h2⟩ => ⟨fl, hr _ _ _ _ h1, h2⟩
  split at h
  · split at h
    · exact henc _ h
    · exact h
  · split at h
    · exact henc _ h
    · exact h
  · obtain ⟨dv, hdv, h1, h2⟩ := h
    refine ⟨dv, hdv, fun he => ?_, fun hne => henc _ (h2 hne)⟩
    rcases h1 he with h | ⟨hc, _, _⟩
    · exact Or.inl h
    · cases hc

theorem forall₂_mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → List.Forall₂ S l1 l2
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (forall₂_mono h h2)

theorem groupOut_basic {E : Env} {al : Bool} {n : Nat} {rec rec' : Scope → Ty → Val → FieldList → Prop}
    (hr : ∀ sc t x fl, rec sc t x fl → rec' sc t x fl) {cs : List (String × Val)} {es : List Entry}
    {out : Option FieldList} (h : GroupOut E ⟨al, true⟩ n rec cs es out) :
    GroupOut E ⟨al, false⟩ n rec' cs es out := by
  obtain ⟨outs, h1, h2⟩ := h
  exact ⟨outs, forall₂_mono (fun _ _ => compOut_basic hr) h1, h2⟩

theorem seqFields_basic {E : Env} {al : Bool} {n : Nat} {rec rec' : Scope → Ty → Val → FieldList → Prop}
    (hr : ∀ sc t x fl, rec sc t x fl → rec' sc t x fl) {isExt : Bool} {rootEs : List Entry}
    {adds : List (List Entry × Bool)} {cs : List (String × Val)} {fl : FieldList}
    (h : SeqFields E ⟨al, true⟩ n rec isExt rootEs adds cs fl) : SeqFields E ⟨al, false⟩ n rec' isExt rootEs adds cs fl := by
  obtain ⟨h0, rootOuts, addOuts, h1, h2, h3⟩ := h
  refine ⟨h0, rootOuts, addOuts, forall₂_mono (fun _ _ => compOut_basic hr) h1, forall₂_mono ?_ h2, h3⟩
  intro a o ha
  split at ha
  · rw [if_pos (by assumption)]; exact groupOut_basic hr ha
  · rw [if_neg (by assumption)]
    obtain ⟨e, he, hc⟩ := ha; exact ⟨e, he, compOut_basic hr hc⟩

theorem perB_basic {E : Env} {al : Bool} {n : Nat} {rec rec' : Scope → Ty → Val → FieldList → Prop}
    (hr : ∀ sc t x fl, rec sc t x fl → rec' sc t x fl) {sc : Scope} {t : Ty} {sc' : Scope} {bt : Ty} {x : Val}
    {fl : FieldList} (h : perB E ⟨al, true⟩ n rec sc t sc' bt x fl) : perB E ⟨al, false⟩ n rec' sc t sc' bt x fl := by
  unfold perB at h ⊢
  split at h
  all_goals first | exact h | skip
  · exact seqFields_basic hr h
  · exact seqFields_basic hr h
  · obtain ⟨fls, h1, h2⟩ := h; exact ⟨fls, forall₂_mono (hr _ _) h1, h2⟩
  · obtain ⟨ws, fls, h1, h2, _, h4⟩ := h
    exact ⟨ws, fls, h1, forall₂_mono (hr _ _) h2, fun hc => absurd hc (by simp), h4⟩
  · obtain ⟨a, afl, h1, h2⟩ := h; exact ⟨a, afl, hr _ _ _ _ h1, h2⟩
  · split at h
    · rw [if_pos (by assumption)]; exact h
    · rw [if_neg (by assumption)]; exact hr _ _ _ _ h
  · exact external_basic h
  · split at h
    · rw [if_pos (by assumption)]; exact h
    · rw [if_neg (by assumption)]; exact otherString_basic h
  · split at h
    · rw [if_pos (by assumption)]; exact h
    · rw [if_neg (by assumption)]; exact hr _ _ _ _ h
  all_goals first
    | (obtain ⟨name, w, h1, h2⟩ := h; exact ⟨name, w, h1, hr _ _ _ _ h2⟩)
    | exact otherString_basic h
    | (obtain ⟨sc'', afl, h1, h2⟩ := h; exact ⟨sc'', afl, hr _ _ _ _ h1, h2⟩)

/-- X.691 7.5: what CANONICAL-PER relates, BASIC-PER relates (the same variant otherwise). -/
theorem per_canonical_basic (E : Env) (al : Bool) :
    ∀ (n : Nat) (sc : Scope) (t : Ty) (x : Val) (fl : FieldList),
      per E ⟨al, true⟩ n sc t x fl → per E ⟨al, false⟩ n sc t x fl
  | 0, _, _, _, _, h => h
  | n + 1, sc, t, x, fl, h => by
    unfold per at h ⊢
    split at h
    · rename_i sc' bt hb
      exact perB_basic (per_canonical_basic E al n) h
    · exact h.elim

/-- X.691 7.9, for the values the decoder reads back: a complete encoding followed by more bits is
not a complete encoding of a value of the same type (and the two values are the same). -/
theorem per_prefixFree {E : Env} {v : Variant} {n : Nat} {frames : List X690.DFrame} {sc : Scope} {t : Ty}
    {x x' : Val} {fl fl' : FieldList} {rest : Bits}
    (h1 : per E v n sc t x fl) (d1 : PDec E v n frames sc t x fl)
    (h2 : per E v n sc t x' fl') (d2 : PDec E v n frames sc t x' fl')
    (he : complete v .other fl' = complete v .other fl ++ rest) : rest = [] ∧ x = x' := by
  obtain ⟨pad1, e1, _⟩ := complete_other v fl
  obtain ⟨pad2, e2, _⟩ := complete_other v fl'
  have r1 := pdec_complete E v n frames sc t x fl h1 d1 0 (pad1 ++ rest)
  have r2 := pdec_complete E v n frames sc t x' fl' h2 d2 0 pad2
  rw [← List.append_assoc, ← e1, ← he, e2] at r1
  rw [r1] at r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at r2
  obtain ⟨⟨rfl, rfl⟩, _⟩ := r2
  exact ⟨by simpa using he.symm, rfl⟩

end Asn1.X691
