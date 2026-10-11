import Asn1.X690.DecSound

/-!
# The parser reads back every encoding

`parseNode_complete`: the octets of an encoding (`Node.octets`, X.690 8.1) whose length forms the
profile allows read back, by `parseNode`, as that encoding. With `parseNode_octets` this makes
parsing and layout inverse. The one condition is that no primitive encoding has the tag UNIVERSAL 0
(X.680 8.4, Table 1: reserved for the encoding rules), whose octets `00 00` with the short length
are the end-of-contents octets of 8.1.5.
-/
namespace Asn1.X690
open Asn1.X680

/-! ## Base 128 (8.1.2.4.2, 8.19.2) -/

theorem base128_go_spec : ∀ (k n : Nat), n < 128 ^ (k + 1) →
    (base128.go n k).foldr (fun d acc => acc * 128 + d) 0 = n ∧ (∀ d ∈ base128.go n k, d < 128) ∧
      base128.go n k ≠ []
  | 0, n, h => by simp [base128.go] at h ⊢; omega
  | k + 1, n, h => by
    simp only [base128.go]
    split
    · rename_i hn; simp; omega
    · rename_i hn
      have h' : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h
      obtain ⟨h1, h2, _⟩ := base128_go_spec k (n / 128) h'
      refine ⟨?_, ?_, by simp⟩
      · simp only [List.foldr_cons, h1]; omega
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact h2 d hd

/-- The octets `base128` makes from digits, most significant first, read back by `base128Digits`. -/
theorem base128Digits_enc : ∀ (xs : List Nat) (k L F : Nat) (r : List (Fin 256)),
    k + xs.length = L → (∀ d ∈ xs, d < 128) → xs ≠ [] → xs.length ≤ F →
    base128Digits F ((xs.zipIdx k).map (fun (d, i) => octet (if i + 1 < L then 128 + d else d)) ++ r) =
      some (xs.reverse, r)
  | [], _, _, _, _, _, _, hne, _ => absurd rfl hne
  | [d], k, L, F, r, hL, hd, _, hF => by
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    have hd0 : d < 128 := hd d (by simp)
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.length_singleton] at hL ⊢
    have : ¬ (k + 1 < L) := by omega
    simp only [this, ite_false, base128Digits, octet, Nat.mod_eq_of_lt (show d < 256 by omega), hd0,
      ite_true, List.reverse_singleton]
  | d :: e :: xs, k, L, F, r, hL, hd, _, hF => by
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    have hd0 : d < 128 := hd d (by simp)
    have ih := base128Digits_enc (e :: xs) (k + 1) L F r (by simp at hL ⊢; omega)
      (fun x hx => hd x (List.mem_cons_of_mem _ hx)) (by simp) (by simp at hF ⊢; omega)
    simp only [List.length_cons] at hL
    have hlt : k + 1 < L := by omega
    rw [List.zipIdx_cons, List.map_cons, List.cons_append]
    dsimp only
    simp only [hlt, ↓reduceIte]
    have hv : (octet (128 + d)).val = 128 + d := by simp only [octet]; omega
    simp only [base128Digits, hv, show ¬ (128 + d < 128) by omega, ite_false]
    rw [ih]
    simp

theorem base128Digits_base128 (n : Nat) (r : List (Fin 256)) (F : Nat)
    (hF : (base128 n).length ≤ F) :
    base128Digits F (base128 n ++ r) = some (base128.go n (n + 1), r) := by
  have hs := base128_go_spec (n + 1) n (by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 128 ^ (n + 1 + 1) := by
        calc 2 ^ n ≤ 2 ^ (7 * (n + 1 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 128 ^ (n + 1 + 1) := by rw [pow_mul]; norm_num)
  have h := base128Digits_enc (base128.go n (n + 1)).reverse 0 (base128.go n (n + 1)).length F r
    (by simp) (fun d hd => hs.2.1 d (List.mem_reverse.mp hd)) (by simpa using hs.2.2)
    (by simpa [base128] using hF)
  simpa [base128] using h

theorem readSubId_base128 (n : Nat) (r : List (Fin 256)) : readSubId (base128 n ++ r) = some (n, r) := by
  unfold readSubId
  rw [base128Digits_base128 n r _ (by simp)]
  have hs := base128_go_spec (n + 1) n (by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 128 ^ (n + 1 + 1) := by
        calc 2 ^ n ≤ 2 ^ (7 * (n + 1 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 128 ^ (n + 1 + 1) := by rw [pow_mul]; norm_num)
  simp only [hs.1, ite_true]

/-! ## Identifier octets (8.1.2) -/

theorem ofBits_bits87 (c : TagClass) : TagClass.ofBits c.bits87 = c := by cases c <;> rfl

theorem bits87_le (c : TagClass) : c.bits87 ≤ 3 := by cases c <;> simp [TagClass.bits87]

theorem readIdent_identOctets (tg : Tag) (c : Bool) (r : List (Fin 256)) :
    readIdent (identOctets tg c ++ r) = some (tg, c, r) := by
  have hb := bits87_le tg.cls
  unfold readIdent
  suffices h : identCandidate (identOctets tg c ++ r) = some (tg, c, r) by simp [h]
  obtain ⟨cl, num⟩ := tg
  simp only at hb
  by_cases hn : num ≤ 30
  · have key : ∀ cb : Nat, (cb = 0 ∨ cb = 32) →
        (octet (64 * cl.bits87 + cb + num)).val = 64 * cl.bits87 + cb + num ∧
        (64 * cl.bits87 + cb + num) % 32 = num ∧ (64 * cl.bits87 + cb + num) / 64 = cl.bits87 ∧
        (64 * cl.bits87 + cb + num) / 32 % 2 = cb / 32 := by
      intro cb hcb; simp only [octet]; omega
    cases c
    · obtain ⟨h0, h1, h2, h3⟩ := key 0 (Or.inl rfl)
      simp only [identOctets, hn, ite_true, Bool.false_eq_true, ite_false, List.singleton_append,
        identCandidate, h0, h1, show num < 31 by omega, h2, ofBits_bits87, h3]
      rfl
    · obtain ⟨h0, h1, h2, h3⟩ := key 32 (Or.inr rfl)
      simp only [identOctets, hn, ite_true, List.singleton_append, identCandidate, h0, h1,
        show num < 31 by omega, h2, ofBits_bits87, h3]
      rfl
  · have key : ∀ cb : Nat, (cb = 0 ∨ cb = 32) →
        (octet (64 * cl.bits87 + cb + 31)).val = 64 * cl.bits87 + cb + 31 ∧
        (64 * cl.bits87 + cb + 31) % 32 = 31 ∧ (64 * cl.bits87 + cb + 31) / 64 = cl.bits87 ∧
        (64 * cl.bits87 + cb + 31) / 32 % 2 = cb / 32 := by
      intro cb hcb; simp only [octet]; omega
    cases c
    · obtain ⟨h0, h1, h2, h3⟩ := key 0 (Or.inl rfl)
      simp only [identOctets, hn, ite_false, Bool.false_eq_true, List.cons_append, identCandidate,
        h0, h1, show ¬ (31 < 31) by omega, readSubId_base128, Option.map_some, h2, ofBits_bits87, h3]
      rfl
    · obtain ⟨h0, h1, h2, h3⟩ := key 32 (Or.inr rfl)
      simp only [identOctets, hn, ite_false, ite_true, List.cons_append, identCandidate, h0, h1,
        show ¬ (31 < 31) by omega, readSubId_base128, Option.map_some, h2, ofBits_bits87, h3]
      rfl

/-! ## Length octets (8.1.3) -/

theorem foldl_bits (a : Nat) : ∀ (bs : Bits),
    bs.foldl (fun acc b => 2 * acc + b.toNat) a = a * 2 ^ bs.length + nnbValue bs
  | [] => by simp [nnbValue]
  | b :: bs => by
    rw [List.foldl_cons, foldl_bits _ bs, nnbValue_cons, List.length_cons, pow_succ]
    ring

theorem nnbValue_app (xs ys : Bits) : nnbValue (xs ++ ys) = nnbValue xs * 2 ^ ys.length + nnbValue ys := by
  unfold nnbValue; rw [List.foldl_append, foldl_bits]; rfl

theorem beValue_go (a : Nat) : ∀ (os : Octets),
    os.foldl (fun a o => 256 * a + o.val) a = a * 2 ^ (8 * os.length) + nnbValue (bitsOf os)
  | [] => by simp [bitsOf, nnbValue]
  | o :: os => by
    rw [List.foldl_cons, beValue_go _ os]
    have hb : bitsOf (o :: os) = octetBits o ++ bitsOf os := by simp [bitsOf]
    have hv : nnbValue (octetBits o) = o.val := by
      rw [octetBits, nnbValue_nnbFn]; exact Nat.mod_eq_of_lt o.isLt
    rw [hb, nnbValue_app, hv, bitsOf_length, List.length_cons,
      show 8 * (os.length + 1) = 8 + 8 * os.length by ring, pow_add]
    norm_num; ring

theorem beValue_beOctets {k n : Nat} (h : n < 256 ^ k) : beValue (beOctets k n) = n := by
  unfold beValue beOctets
  rw [beValue_go, bitsOf_bitsToOctets _ (by simp)]
  rw [nnbValue_nnbFn]
  simp only [zero_mul, zero_add]
  apply Nat.mod_eq_of_lt
  calc n < 256 ^ k := h
    _ = 2 ^ (8 * k) := by rw [pow_mul]; norm_num

theorem beOctets_length (k n : Nat) : (beOctets k n).length = k := by
  unfold beOctets; rw [bitsToOctets_length (by simp)]; simp

theorem readLen_lengthOctets {f : LenForm} {n : Nat} (r : List (Fin 256)) (hf : f.Fits n)
    (hi : f ≠ .indefinite) : readLen (lengthOctets f n ++ r) = some (f, some n, r) := by
  unfold readLen
  suffices h : lenCandidate (lengthOctets f n ++ r) = some (f, some n, r) by
    rw [h]; simp only [Option.bind_some]
    have hc : lenOcts f (some n) ++ r = lengthOctets f n ++ r ∧ (f = .indefinite ↔ some n = none) ∧
        f.Fits ((some n).getD 0) :=
      ⟨by rw [lenOcts_some hi], ⟨fun e => absurd e hi, fun e => by cases e⟩, by simpa using hf⟩
    simp only [hc, and_self, ↓reduceIte]
  cases f with
  | indefinite => exact absurd rfl hi
  | short =>
    simp only [LenForm.Fits] at hf
    have hv : (octet n).val = n := by simp only [octet]; omega
    simp [lengthOctets, lenCandidate, hv, show n < 128 by omega]
  | long k =>
    simp only [LenForm.Fits] at hf
    obtain ⟨h1, h2, h3⟩ := hf
    have hv : (octet (128 + k)).val = 128 + k := by simp only [octet]; omega
    simp only [lengthOctets, List.cons_append, lenCandidate, hv, show ¬ (128 + k < 128) by omega,
      show ¬ (128 + k = 128) by omega, ite_false, Nat.add_sub_cancel_left]
    rw [List.take_left' (beOctets_length k n), List.drop_left' (beOctets_length k n), beValue_beOctets h3]

theorem readLen_indefinite (n : Nat) (r : List (Fin 256)) :
    readLen (lengthOctets .indefinite n ++ r) = some (.indefinite, none, r) := by
  simp [readLen, lengthOctets, lenCandidate, octet, lenOcts, LenForm.Fits]

/-! ## Encodings (8.1) -/

mutual
  /-- No primitive encoding in `nd` has the tag UNIVERSAL 0, which X.680 8.4 reserves for the
  encoding rules: `00 00` would read as end-of-contents octets (8.1.5). -/
  def Node.NoEoc : Node → Prop
    | .prim tg _ _ => tg ≠ ⟨.universal, 0⟩
    | .cons _ _ ch => Node.NoEocList ch
  def Node.NoEocList : List Node → Prop
    | [] => True
    | nd :: rest => nd.NoEoc ∧ Node.NoEocList rest
end

theorem allowed_prim {p : Profile} {f : LenForm} {n : Nat} (h : f.Allowed p false n) :
    f.Fits n ∧ f ≠ .indefinite := by
  cases p <;> unfold LenForm.Allowed at h
  · exact ⟨h.1, h.2 rfl⟩
  · refine ⟨h.2, ?_⟩; rw [show f = minLenForm n from h.1]; unfold minLenForm; split <;> simp
  · refine ⟨h.2, ?_⟩; rw [h.1]; unfold minLenForm; split <;> simp

theorem allowed_fits {p : Profile} {c : Bool} {f : LenForm} {n : Nat} (h : f.Allowed p c n) : f.Fits n := by
  cases p <;> unfold LenForm.Allowed at h
  · exact h.1
  · exact h.2
  · exact h.2

/-- The first identifier octet: the class, the form and the number (31 for a larger number). -/
theorem identOctets_cons (tg : Tag) (c : Bool) : ∃ rest, identOctets tg c =
    octet (64 * tg.cls.bits87 + (if c then 32 else 0) + (if tg.num ≤ 30 then tg.num else 31)) :: rest := by
  by_cases hn : tg.num ≤ 30
  · exact ⟨[], by simp [identOctets, hn]⟩
  · exact ⟨base128 tg.num, by simp [identOctets, hn]⟩

theorem identOctets_ne_nil (tg : Tag) (c : Bool) : identOctets tg c ≠ [] := by
  obtain ⟨rest, h⟩ := identOctets_cons tg c; rw [h]; simp

theorem lengthOctets_ne_nil (f : LenForm) (n : Nat) : lengthOctets f n ≠ [] := by
  cases f <;> simp [lengthOctets]

theorem octets_length_ge (nd : Node) : 2 ≤ nd.octets.length := by
  cases nd with
  | prim tg f cs =>
    have := List.length_pos_iff.mpr (identOctets_ne_nil tg false)
    have := List.length_pos_iff.mpr (lengthOctets_ne_nil f cs.length)
    simp only [Node.octets, List.length_append]; omega
  | cons tg f ch =>
    have := List.length_pos_iff.mpr (identOctets_ne_nil tg true)
    have := List.length_pos_iff.mpr (lengthOctets_ne_nil f (Node.octetsList ch).length)
    simp only [Node.octets, List.length_append]; omega

/-- The first octet of an encoding is 0 only for a primitive UNIVERSAL 0. -/
theorem octets_head (nd : Node) (h : nd.NoEoc) : ∃ o rest, nd.octets = o :: rest ∧ o.val ≠ 0 := by
  have key : ∀ (tg : Tag) (c : Bool) (tail : Octets), (c = false → tg ≠ ⟨.universal, 0⟩) →
      ∃ o rest, identOctets tg c ++ tail = o :: rest ∧ o.val ≠ 0 := by
    intro tg c tail hc
    obtain ⟨rest, hr⟩ := identOctets_cons tg c
    refine ⟨_, rest ++ tail, by rw [hr]; rfl, ?_⟩
    have hb := bits87_le tg.cls
    simp only [octet]
    intro h0
    have hv : 64 * tg.cls.bits87 + (if c then 32 else 0) + (if tg.num ≤ 30 then tg.num else 31) = 0 := by
      have : 64 * tg.cls.bits87 + (if c then 32 else 0) + (if tg.num ≤ 30 then tg.num else 31) < 256 := by
        split <;> split <;> omega
      omega
    have hc0 : c = false := by cases c <;> simp_all
    have hcl : tg.cls.bits87 = 0 := by split at hv <;> split at hv <;> omega
    have hnum : tg.num = 0 := by split at hv <;> split at hv <;> omega
    apply hc hc0
    obtain ⟨cl, num⟩ := tg
    cases cl <;> simp_all [TagClass.bits87]
  cases nd with
  | prim tg f cs =>
    simp only [Node.octets, List.append_assoc]
    exact key tg false _ (fun _ => h)
  | cons tg f ch =>
    simp only [Node.octets, List.append_assoc]
    exact key tg true _ (fun e => by cases e)

mutual
  theorem parseNode_complete (p : Profile) : ∀ (f : Nat) (nd : Node) (r : List (Fin 256)),
      nd.LenOk p → nd.NoEoc → nd.octets.length < f → parseNode f (nd.octets ++ r) = some (nd, r)
    | 0, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
    | f + 1, .prim tg len cs, r, hl, _, hf => by
      obtain ⟨hfit, hind⟩ := allowed_prim hl
      unfold parseNode
      simp only [Node.octets, List.append_assoc]
      rw [readIdent_identOctets]
      simp only
      rw [readLen_lengthOctets _ hfit hind]
      simp
    | f + 1, .cons tg len ch, r, hl, hn, hf => by
      obtain ⟨hal, hll⟩ := hl
      have hfit := allowed_fits hal
      have hlen : (Node.octetsList ch).length + 1 < f := by
        have := List.length_pos_iff.mpr (identOctets_ne_nil tg true)
        have := List.length_pos_iff.mpr (lengthOctets_ne_nil len (Node.octetsList ch).length)
        simp only [Node.octets, List.length_append] at hf; omega
      unfold parseNode
      by_cases hi : len = .indefinite
      · subst hi
        simp only [Node.octets, ite_true, List.append_assoc]
        rw [readIdent_identOctets]
        simp only
        rw [readLen_indefinite]
        simp only
        rw [← List.append_assoc, parseUntilEoc_complete p f ch r hll hn hlen]
        rfl
      · simp only [Node.octets, hi, ite_false, List.append_nil, List.append_assoc]
        rw [readIdent_identOctets]
        simp only
        rw [readLen_lengthOctets _ hfit hi]
        simp only [List.length_append, Nat.le_add_right, ite_true, List.take_left', List.drop_left']
        rw [parseAll_complete p f ch hll hn hlen]
        rfl
  theorem parseAll_complete (p : Profile) : ∀ (f : Nat) (ch : List Node),
      Node.LenOkList p ch → Node.NoEocList ch → (Node.octetsList ch).length + 1 < f →
      parseAll f (Node.octetsList ch) = some ch
    | f, [], _, _, _ => by cases f <;> rfl
    | 0, _ :: _, _, _, hf => absurd hf (Nat.not_lt_zero _)
    | f + 1, nd :: rest, hl, hn, hf => by
      have h2 := octets_length_ge nd
      have hlt : nd.octets.length < f := by simp only [Node.octetsList, List.length_append] at hf; omega
      have hlt' : (Node.octetsList rest).length + 1 < f := by
        simp only [Node.octetsList, List.length_append] at hf; omega
      obtain ⟨o, os, ho, _⟩ := octets_head nd hn.1
      unfold parseAll
      simp only [Node.octetsList]
      rw [ho, List.cons_append]
      simp only
      rw [← List.cons_append, ← ho, parseNode_complete p f nd _ hl.1 hn.1 hlt]
      simp only
      rw [parseAll_complete p f rest hl.2 hn.2 hlt']
      rfl
  theorem parseUntilEoc_complete (p : Profile) : ∀ (f : Nat) (ch : List Node) (r : List (Fin 256)),
      Node.LenOkList p ch → Node.NoEocList ch → (Node.octetsList ch).length + 1 < f →
      parseUntilEoc f (Node.octetsList ch ++ eoc ++ r) = some (ch, r)
    | 0, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
    | f + 1, [], r, _, _, _ => by
      simp [parseUntilEoc, Node.octetsList, eoc, octet]
    | f + 1, nd :: rest, r, hl, hn, hf => by
      have h2 := octets_length_ge nd
      have hlt : nd.octets.length < f := by simp only [Node.octetsList, List.length_append] at hf; omega
      have hlt' : (Node.octetsList rest).length + 1 < f := by
        simp only [Node.octetsList, List.length_append] at hf; omega
      obtain ⟨o, os, ho, ho0⟩ := octets_head nd hn.1
      obtain ⟨o2, os', rfl⟩ : ∃ o2 os', os = o2 :: os' := by
        cases os with
        | nil => have := congrArg List.length ho; simp at this; omega
        | cons o2 os' => exact ⟨o2, os', rfl⟩
      have hrw : Node.octetsList (nd :: rest) ++ eoc ++ r = o :: o2 :: (os' ++ (Node.octetsList rest ++ eoc ++ r)) := by
        simp only [Node.octetsList, ho, List.append_assoc, List.cons_append]
      rw [hrw]
      unfold parseUntilEoc
      simp only [ho0, false_and, ↓reduceIte]
      rw [show o :: o2 :: (os' ++ (Node.octetsList rest ++ eoc ++ r)) = nd.octets ++ (Node.octetsList rest ++ eoc ++ r) by
        rw [ho]; rfl]
      rw [parseNode_complete p f nd _ hl.1 hn.1 hlt]
      simp only
      rw [parseUntilEoc_complete p f rest r hl.2 hn.2 hlt']
      rfl
end

mutual
  theorem lenOkB_complete (p : Profile) : ∀ (nd : Node), nd.LenOk p → lenOkB p nd = true
    | .prim _ f cs, h => by simpa [lenOkB, Node.LenOk] using h
    | .cons _ f ch, h => by
      simp only [lenOkB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, lenOkListB_complete p ch h.2⟩
  theorem lenOkListB_complete (p : Profile) : ∀ (ch : List Node), Node.LenOkList p ch → lenOkListB p ch = true
    | [], _ => rfl
    | nd :: rest, h => by
      simp only [lenOkListB, Bool.and_eq_true]
      exact ⟨lenOkB_complete p nd h.1, lenOkListB_complete p rest h.2⟩
end

/-- X.690 8.1: the octets of an encoding read back, with nothing after it, as that encoding, and its
length forms pass the profile's check: the first two steps of `decode`. With `parseNode_octets`,
layout and parsing are inverse. -/
theorem parse_octets_self {p : Profile} {nd : Node} (hl : nd.LenOk p) (hn : nd.NoEoc) :
    parseNode (nd.octets.length + 1) nd.octets = some (nd, []) ∧ lenOkB p nd = true := by
  refine ⟨?_, lenOkB_complete p nd hl⟩
  simpa using parseNode_complete p (nd.octets.length + 1) nd [] hl hn (by omega)

end Asn1.X690
