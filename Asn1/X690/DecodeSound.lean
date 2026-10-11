import Asn1.X690.Decode

/-!
# The decoder reads what X.690 lays out

`parseNode_octets`: the `Node` that `parseNode` reads from some octets lays out (`Node.octets`, X.690
8.1) to exactly those octets. So a decoded encoding is a `Node` of the relation `ber`, and the octets
are its octets.
-/
namespace Asn1.X690
open Asn1.X680

theorem readIdent_spec {os r : List (Fin 256)} {t : Tag} {c : Bool} (h : readIdent os = some (t, c, r)) :
    identOctets t c ++ r = os := by
  unfold readIdent at h
  obtain ⟨⟨t', c', r'⟩, -, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : identOctets t' c' ++ r' = os
  · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2; exact hc
  · simp [hc] at h2

theorem readLen_spec {os r : List (Fin 256)} {f : LenForm} {l : Option Nat}
    (h : readLen os = some (f, l, r)) : lenOcts f l ++ r = os ∧ (f = .indefinite ↔ l = none) := by
  unfold readLen at h
  obtain ⟨⟨f', l', r'⟩, -, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : lenOcts f' l' ++ r' = os ∧ (f' = .indefinite ↔ l' = none) ∧ f'.Fits (l'.getD 0)
  · simp only [hc, and_self, ite_true, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2; exact ⟨hc.1, hc.2.1⟩
  · simp only [hc, ite_false] at h2; cases h2

theorem lenOcts_some {f : LenForm} {n : Nat} (hf : f ≠ .indefinite) : lenOcts f (some n) = lengthOctets f n := by
  cases f <;> simp_all [lenOcts]

mutual
  theorem parseNode_octets : ∀ (f : Nat) (os : List (Fin 256)) (nd : Node) (r : List (Fin 256)),
      parseNode f os = some (nd, r) → nd.octets ++ r = os
    | 0, os, nd, r, h => by simp [parseNode] at h
    | f + 1, os, nd, r, h => by
      unfold parseNode at h
      split at h
      · simp at h
      · rename_i tg cons r1 hid
        have hi := readIdent_spec hid
        split at h
        · simp at h
        · rename_i form len r2 hl
          split at h
          · -- primitive, definite
            rename_i l
            obtain ⟨hlo, hind⟩ := readLen_spec hl
            split at h
            · rename_i hle
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              have hf : form ≠ .indefinite := fun e => by simpa using hind.mp e
              rw [lenOcts_some hf] at hlo
              simp only [Node.octets, List.length_take, Nat.min_eq_left hle]
              rw [← hi, ← hlo]; simp
            · simp at h
          · simp at h
          · -- constructed, definite
            rename_i l
            obtain ⟨hlo, hind⟩ := readLen_spec hl
            split at h
            · rename_i hle
              obtain ⟨ch, hch, he⟩ := Option.map_eq_some_iff.mp h
              simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
              have hf : form ≠ .indefinite := fun e => by simpa using hind.mp e
              rw [lenOcts_some hf] at hlo
              have hc := parseAll_octets f _ _ hch
              simp only [Node.octets, hc, List.length_take, Nat.min_eq_left hle, hf, ite_false,
                List.append_nil]
              rw [← hi, ← hlo]; simp
            · simp at h
          · -- constructed, indefinite
            obtain ⟨hlo, hind⟩ := readLen_spec hl
            obtain ⟨⟨ch, r'⟩, hch, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
            have hf : form = .indefinite := hind.mpr rfl
            subst hf
            have hc := parseUntilEoc_octets f _ _ _ hch
            simp only [Node.octets, ite_true]
            rw [← hi, ← hlo, ← hc]; simp [lenOcts, lengthOctets]
  theorem parseAll_octets : ∀ (f : Nat) (os : List (Fin 256)) (ch : List Node),
      parseAll f os = some ch → Node.octetsList ch = os
    | _, [], ch, h => by simp [parseAll] at h; subst h; rfl
    | 0, _ :: _, ch, h => by simp [parseAll] at h
    | f + 1, o :: os, ch, h => by
      unfold parseAll at h
      split at h
      · rename_i nd r hn
        obtain ⟨ch', hch, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [Node.octetsList, parseAll_octets f _ _ hch, parseNode_octets f _ _ _ hn]
      · simp at h
  theorem parseUntilEoc_octets : ∀ (f : Nat) (os : List (Fin 256)) (ch : List Node) (r : List (Fin 256)),
      parseUntilEoc f os = some (ch, r) → Node.octetsList ch ++ eoc ++ r = os
    | 0, os, ch, r, h => by simp [parseUntilEoc] at h
    | f + 1, os, ch, r, h => by
      unfold parseUntilEoc at h
      split at h
      · rename_i a b r0
        split at h
        · rename_i hab
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          have ha : a = octet 0 := by apply Fin.ext; simp [octet, hab.1]
          have hb : b = octet 0 := by apply Fin.ext; simp [octet, hab.2]
          simp [Node.octetsList, eoc, ha, hb]
        · split at h
          · rename_i nd r' hn
            obtain ⟨⟨ch', r''⟩, hch, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
            have := parseUntilEoc_octets f _ _ _ hch
            rw [Node.octetsList, List.append_assoc, List.append_assoc, ← List.append_assoc _ eoc,
              this, parseNode_octets f _ _ _ hn]
          · simp at h
      · simp at h
end
end Asn1.X690
