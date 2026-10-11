import Asn1.X691.Encode
import Asn1.X691.Properties

/-!
# Canonicity of CANONICAL-PER (X.691 3.7.4)

CANONICAL-PER is meant to give each abstract value one encoding (3.7.4, 7.5). `per` is a relation,
so this is a theorem to prove: `per_functional` — under CANONICAL-PER, a value of a type has one
field-list, hence one complete encoding (`per_canonical`) — for the types that meet `CanonT`.

`CanonT` (by fuel, as `per`) excludes exactly what is not functional as read, or not proved here:

Findings (the relation is not functional as written):
- open types (11.2): `perB` encodes `.open_ ty y` in *any* scope `sc''`, and the abstract value does
  not record one. The encoding depends on it: references in `ty` resolve in the scope's module, and
  so do the module's defaults that PER reads (EXTENSIBILITY IMPLIED for the extension bits of 19.1,
  23.5; AUTOMATIC TAGS for the canonical order of 21 and 23). Ledger X691-24.
- EXTERNAL (29): `ExternalFields` allows both single-ASN1-type and octet-aligned (ledger X691-11);
  29.6 chooses by whether the data value is a single ASN.1 type encoded by PER, which the abstract
  value (X.680 37.5) does not record.

Not proved here (believed functional):
- ObjectDescriptor and the ISO 2022 string types (TeletexString, VideotexString, GraphicString,
  GeneralString, 30.6): needs the canonical-mode ISO 2022 encoding (X.690 11.4) to be unique;
- conditions on the schema, not on X.691: distinct item names of an ENUMERATED and alternative names
  of a CHOICE (X.680 20.2, 29.2), and a DEFAULT whose value notation denotes one value (`evalVal` is
  not functional for values taken from object sets, X.681 15);
- SET OF (22.1, ledger X691-17): components sorted by their keys; two orders differ only where keys
  are equal, so `KeyInj` (components with equal keys have equal field-lists) is assumed. It holds
  whenever the decoder reads back every encoding of the component type (`keyInj_of_pdec`, from
  `per_prefixFree` and `per_unambiguous`): equal keys, read both ways, are complete encodings one of
  which is the other followed by zero bits.

`per_canonical` then gives one complete encoding per value. REAL (15) is functional: the CER/DER contents octets of a value are unique (`realContents_der_fun`:
an odd mantissa times a power of two, an NR3 mantissa without trailing zeros times a power of ten,
`scale_unique`). The PER view, `least?`/`greatest?`,
the named bits sent (16.2–16.3), the TIME encoding type and its value (`TimeAs`, 32) and the default
handling of 19.5 under CANONICAL-PER are functional and need nothing.
-/
open Asn1 Asn1.X680
open Classical
namespace Asn1.X691

theorem intFields_fun {v : Variant} {P : PSet Int} {i : Int} {fl fl' : FieldList}
    (h1 : IntFields v P i fl) (h2 : IntFields v P i fl') : fl = fl' := by
  obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases h2 with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> first | rfl | exact absurd a b | exact absurd b a
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    rw [h1.2, h2.2]

theorem bitsFields_fun {v : Variant} {S : PSet Nat} {bs : Bits} {fl fl' : FieldList}
    (h1 : BitsFields v S bs fl) (h2 : BitsFields v S bs fl') : fl = fl' := by
  obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases h2 with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> first | rfl | exact absurd a b | exact absurd b a
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    rw [h1.2, h2.2]

theorem octetsFields_fun {v : Variant} {S : PSet Nat} {os : Octets} {fl fl' : FieldList}
    (h1 : OctetsFields v S os fl) (h2 : OctetsFields v S os fl') : fl = fl' := by
  obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases h2 with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> first | rfl | exact absurd a b | exact absurd b a
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    rw [h1.2, h2.2]

theorem kmFields_fun {v : Variant} {k : StrType} {P : PSet Nat × PSet Nat} {cs : List Nat} {fl fl' : FieldList}
    (h1 : KmFields v k P cs fl) (h2 : KmFields v k P cs fl') : fl = fl' := by
  obtain ⟨_, _, h1⟩ := h1; obtain ⟨_, _, h2⟩ := h2
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases h2 with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> first | rfl | exact absurd a b | exact absurd b a
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    rw [h1.2, h2.2]

theorem seqOfFields_fun {v : Variant} {S : PSet Nat} {fls : List FieldList} {fl fl' : FieldList}
    (h1 : SeqOfFields v S fls fl) (h2 : SeqOfFields v S fls fl') : fl = fl' := by
  obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases h2 with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> first | rfl | exact absurd a b | exact absurd b a
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    rw [h1.2, h2.2]

theorem namedBitsSent_fun {S : PSet Nat} {bs s1 s2 : Bits} (h1 : NamedBitsSent S bs s1)
    (h2 : NamedBitsSent S bs s2) : s1 = s2 := by
  obtain ⟨k1, e1, l1, a1, m1⟩ := h1
  obtain ⟨k2, e2, l2, a2, m2⟩ := h2
  have : k1 = k2 := le_antisymm (m1 k2 l2 a2) (m2 k1 l1 a1)
  subst this; rw [e1, e2]

theorem timeAs_fun {vals : TimeV → Prop} {tv : TimeV} {n1 n2 : String} {w1 w2 : Val}
    (h1 : TimeAs vals tv n1 w1) (h2 : TimeAs vals tv n2 w2) : n1 = n2 ∧ w1 = w2 := by
  obtain ⟨c, hc, h1⟩ := h1; obtain ⟨c', hc', h2⟩ := h2
  rw [hc] at hc'; cases hc'
  rcases h1 with ⟨a1, rfl, rfl⟩ | ⟨a1, rfl, rfl⟩ <;> rcases h2 with ⟨a2, rfl, rfl⟩ | ⟨a2, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd ⟨c, a1⟩ a2
  · exact absurd ⟨c, a2⟩ a1
  · exact ⟨rfl, rfl⟩


theorem enumIndex_mem {items : List (String × Int)} {id : String} {k : Nat} (h : enumIndex items id = some k) :
    ∃ p ∈ items, p.1 = id := by
  unfold enumIndex at h
  cases hf : items.find? (·.1 == id) with
  | none => simp [hf] at h
  | some p =>
    have := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    exact ⟨p, this, by simpa using hp⟩

theorem enumFields_fun {v : Variant} {root : List (String × Option Int)}
    {ext : Option (List (String × Option Int))} {implied : Bool} {id : String} {fl fl' : FieldList}
    (hnd : ((enumNumbers root ext).map (·.1)).Nodup)
    (h1 : EnumFields v root ext implied id fl) (h2 : EnumFields v root ext implied id fl') : fl = fl' := by
  unfold EnumFields at h1 h2
  have disj : ∀ k k', enumIndex ((enumNumbers root ext).take root.length) id = some k →
      enumIndex ((enumNumbers root ext).drop root.length) id = some k' → False := by
    intro k k' a b
    obtain ⟨p, hp, rfl⟩ := enumIndex_mem a
    obtain ⟨q, hq, hpq⟩ := enumIndex_mem b
    rw [← List.take_append_drop root.length (enumNumbers root ext), List.map_append] at hnd
    exact List.disjoint_of_nodup_append hnd (List.mem_map_of_mem hp) (hpq ▸ List.mem_map_of_mem hq)
  split at h1
  · rename_i hx; simp only [hx, ↓reduceIte] at h2
    rcases h1 with ⟨k, a, rfl⟩ | ⟨k, a, rfl⟩ <;> rcases h2 with ⟨k', b, rfl⟩ | ⟨k', b, rfl⟩
    · rw [a] at b; cases b; rfl
    · exact (disj _ _ a b).elim
    · exact (disj _ _ b a).elim
    · rw [a] at b; cases b; rfl
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h2
    obtain ⟨k, a, rfl⟩ := h1; obtain ⟨k', b, rfl⟩ := h2
    rw [a] at b; cases b; rfl

theorem stringOctets_fun {k : StrType} (hk : k.isRegister = false) {x : Val} {os os' : Octets}
    (h1 : X690.StringOctets .der k x os) (h2 : X690.StringOctets .der k x os') : os = os' := by
  unfold X690.StringOctets at h1 h2
  split at h1
  · split at h1 <;> simp_all
  · rw [hk] at h1; exact absurd h1.1 (by simp)
  · exact h1.elim

theorem otherString_fun {v : Variant} (hv : v.canonical = true) {k : StrType} (hk : k.isRegister = false)
    {x : Val} {fl fl' : FieldList}
    (h1 : OtherStringFields v k x fl) (h2 : OtherStringFields v k x fl') : fl = fl' := by
  obtain ⟨os, a, rfl⟩ := h1; obtain ⟨os', b, rfl⟩ := h2
  simp only [hv, ↓reduceIte] at a b
  rw [stringOctets_fun hk a b]

/-- Sorted permutations are equal when the order is antisymmetric on their elements. -/
theorem eq_of_perm_pairwise {α : Type} {r : α → α → Prop} :
    ∀ {l1 l2 : List α}, l1.Perm l2 → l1.Pairwise r → l2.Pairwise r →
      (∀ a ∈ l1, ∀ b ∈ l1, r a b → r b a → a = b) → l1 = l2
  | [], l2, hp, _, _, _ => List.Perm.nil_eq hp
  | a :: t1, [], hp, _, _, _ => absurd hp.length_eq (by simp)
  | a :: t1, b :: t2, hp, h1, h2, ha => by
    have hab : a = b := by
      have hb1 : b ∈ a :: t1 := hp.symm.subset (by simp)
      have ha2 : a ∈ b :: t2 := hp.subset (by simp)
      rcases List.mem_cons.mp hb1 with e | hb1
      · exact e.symm
      rcases List.mem_cons.mp ha2 with e | ha2
      · exact e
      exact ha a (by simp) b (by simp [hb1]) (List.rel_of_pairwise_cons h1 hb1) (List.rel_of_pairwise_cons h2 ha2)
    subst hab
    rw [eq_of_perm_pairwise (List.Perm.cons_inv hp) h1.of_cons h2.of_cons
      (fun x hx y hy => ha x (by simp [hx]) y (by simp [hy]))]


/-- The value notation of a component's DEFAULT denotes one value. -/
def DefaultFun (E : Env) (n : Nat) (en : Entry) : Prop :=
  ∀ d, en.presence = .default_ d → ∀ w w', evalVal E n en.scope d w → evalVal E n en.scope d w' → w = w'

/-! ## REAL: the DER contents octets are a function of the value (X.690 11.3) -/

theorem scale_pos_unique {b : ℕ} (hb : 2 ≤ b) {m1 m2 : ℕ} {e1 e2 : ℤ}
    (n1 : ¬ b ∣ m1) (n2 : ¬ b ∣ m2) (h : (m1 : ℚ) * (b : ℚ) ^ e1 = (m2 : ℚ) * (b : ℚ) ^ e2) :
    m1 = m2 ∧ e1 = e2 := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  -- the case e1 ≤ e2, then symmetric
  have key : ∀ {m1 m2 : ℕ} {e1 e2 : ℤ}, ¬ b ∣ m1 → (m1 : ℚ) * (b : ℚ) ^ e1 = (m2 : ℚ) * (b : ℚ) ^ e2 →
      e1 ≤ e2 → m1 = m2 ∧ e1 = e2 := by
    intro m1 m2 e1 e2 n1 h hle
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e2 = e1 + d := ⟨(e2 - e1).toNat, by omega⟩
    subst hd
    rw [zpow_add₀ hb0, zpow_natCast] at h
    have hpe : (b : ℚ) ^ e1 ≠ 0 := zpow_ne_zero _ hb0
    have h' : (m1 : ℚ) = (m2 : ℚ) * (b : ℚ) ^ d := by
      have := h; field_simp at this; linarith [this]
    have hn : m1 = m2 * b ^ d := by exact_mod_cast h'
    cases d with
    | zero => simp at hn; exact ⟨hn, by simp⟩
    | succ d => exact absurd ⟨m2 * b ^ d, by rw [hn, pow_succ]; ring⟩ n1
  rcases le_total e1 e2 with hle | hle
  · exact key n1 h hle
  · obtain ⟨a, b'⟩ := key n2 h.symm hle; exact ⟨a.symm, b'.symm⟩

theorem scale_unique {b : ℕ} (hb : 2 ≤ b) {s1 s2 : Bool} {m1 m2 : ℕ} {e1 e2 : ℤ} (p1 : 0 < m1) (p2 : 0 < m2)
    (n1 : ¬ b ∣ m1) (n2 : ¬ b ∣ m2)
    (h : (if s1 then -1 else 1) * (m1 : ℚ) * (b : ℚ) ^ e1 = (if s2 then -1 else 1) * (m2 : ℚ) * (b : ℚ) ^ e2) :
    s1 = s2 ∧ m1 = m2 ∧ e1 = e2 := by
  have hb0 : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have q1 : (0 : ℚ) < (m1 : ℚ) * (b : ℚ) ^ e1 := mul_pos (by exact_mod_cast p1) (zpow_pos hb0 _)
  have q2 : (0 : ℚ) < (m2 : ℚ) * (b : ℚ) ^ e2 := mul_pos (by exact_mod_cast p2) (zpow_pos hb0 _)
  have hs : s1 = s2 := by
    cases s1 <;> cases s2 <;> simp at h <;> first | rfl | (nlinarith)
  subst hs
  have h' : (m1 : ℚ) * (b : ℚ) ^ e1 = (m2 : ℚ) * (b : ℚ) ^ e2 := by
    cases s1 <;> simp at h <;> linarith
  exact ⟨rfl, scale_pos_unique hb n1 n2 h'⟩

theorem expFieldMin_fun {e : Int} {f1 f2 : Nat} {o1 o2 : Octets} (h1 : X690.ExpFieldMin e f1 o1)
    (h2 : X690.ExpFieldMin e f2 o2) : f1 = f2 ∧ o1 = o2 := by
  unfold X690.ExpFieldMin at h1 h2
  dsimp only at h1 h2
  split at h1
  · rename_i hk; simp only [hk, ↓reduceIte] at h2; exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
  · rename_i hk; simp only [hk, ↓reduceIte] at h2
    exact ⟨h1.1.trans h2.1.symm, h1.2.2.trans h2.2.2.symm⟩

theorem realContents_der_fun : ∀ {r : X680.RealVal} {o1 o2 : Octets},
    X690.RealContents .der r o1 → X690.RealContents .der r o2 → o1 = o2
  | .plusZero, _, _, h1, h2 | .plusInfinity, _, _, h1, h2 | .minusInfinity, _, _, h1, h2
  | .notANumber, _, _, h1, h2 | .minusZero, _, _, h1, h2 => by
    simp only [X690.RealContents] at h1 h2; rw [h1, h2]
  | .num .two q, _, _, h1, h2 => by
    simp only [X690.RealContents, X690.RealBinary, X690.Profile.restricted, ↓reduceIte] at h1 h2
    obtain ⟨n1, bb1, f1, e1, nn1, fm1, ef1, nf1, _, _, p1, q1, rfl, _, _, rfl, rfl, odd1, rfl, x1⟩ := h1
    obtain ⟨n2, bb2, f2, e2, nn2, fm2, ef2, nf2, _, _, p2, q2, rfl, _, _, rfl, rfl, odd2, rfl, x2⟩ := h2
    simp only [X690.realBase, pow_zero, mul_one] at q1 q2
    obtain ⟨rfl, rfl, rfl⟩ := scale_unique (b := 2) (le_refl 2) p1 p2 (by omega) (by omega)
      (by push_cast at q1 q2 ⊢; rw [← q1, ← q2])
    obtain ⟨rfl, rfl⟩ := expFieldMin_fun x1 x2
    rfl
  | .num .ten q, _, _, h1, h2 => by
    simp only [X690.RealContents, X690.RealDecimal, X690.Profile.restricted, forall_const] at h1 h2
    obtain ⟨fo1, s1, rfl, _, _, _, _, rfl, n1, m1, e1, pm1, d1, q1, rfl⟩ := h1
    obtain ⟨fo2, s2, rfl, _, _, _, _, rfl, n2, m2, e2, pm2, d2, q2, rfl⟩ := h2
    obtain ⟨rfl, rfl, rfl⟩ := scale_unique (b := 10) (by norm_num) pm1 pm2 (by omega) (by omega)
      (by push_cast at q1 q2 ⊢; rw [← q1, ← q2])
    rfl

/-- A relation is functional at a type. -/
def FunAt (rec : Scope → Ty → Val → FieldList → Prop) (sc : Scope) (t : Ty) : Prop :=
  ∀ x fl fl', rec sc t x fl → rec sc t x fl' → fl = fl'

theorem compOut_fun {E : Env} {v : Variant} (hv : v.canonical = true) {n : Nat}
    {rec : Scope → Ty → Val → FieldList → Prop} {root : Bool} {cs : List (String × Val)} {en : Entry}
    (hR : FunAt rec en.scope en.ty) (hd : DefaultFun E n en) {out out' : Option FieldList}
    (h1 : CompOut E v n rec root cs en out) (h2 : CompOut E v n rec root cs en out') : out = out' := by
  have enc : ∀ x, (∃ fl, rec en.scope en.ty x fl ∧ out = some fl) →
      (∃ fl, rec en.scope en.ty x fl ∧ out' = some fl) → out = out' := by
    rintro x ⟨f, a, rfl⟩ ⟨f', b, rfl⟩; rw [hR x f f' a b]
  unfold CompOut at h1 h2
  cases hp : en.presence with
  | mandatory =>
    simp only [hp] at h1 h2
    cases hl : cs.lookup en.name with
    | none => simp only [hl] at h1 h2; rw [h1.2, h2.2]
    | some x => simp only [hl] at h1 h2; exact enc x h1 h2
  | optional =>
    simp only [hp] at h1 h2
    cases hl : cs.lookup en.name with
    | none => simp only [hl] at h1 h2; rw [h1, h2]
    | some x => simp only [hl] at h1 h2; exact enc x h1 h2
  | default_ d =>
    simp only [hp] at h1 h2
    obtain ⟨dv, e1, a1, b1⟩ := h1
    obtain ⟨dv', e2, a2, b2⟩ := h2
    have := hd d hp dv dv' e1 e2
    subst this
    by_cases he : eqv E n en.scope en.ty ((cs.lookup en.name).getD dv) dv
    · rcases a1 he with h | ⟨hc, _⟩
      · rcases a2 he with h' | ⟨hc', _⟩
        · rw [h, h']
        · rw [hv] at hc'; cases hc'
      · rw [hv] at hc; cases hc
    · exact enc _ (b1 he) (b2 he)

theorem forall₂_fun {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m m' : List β}, (∀ a ∈ l, ∀ b b', R a b → R a b' → b = b') →
      List.Forall₂ R l m → List.Forall₂ R l m' → m = m'
  | _, _, _, _, .nil, .nil => rfl
  | a :: l, _, _, h, .cons r1 t1, .cons r2 t2 => by
    rw [h a (by simp) _ _ r1 r2, forall₂_fun (fun x hx => h x (by simp [hx])) t1 t2]

theorem groupOut_fun {E : Env} {v : Variant} (hv : v.canonical = true) {n : Nat}
    {rec : Scope → Ty → Val → FieldList → Prop} {cs : List (String × Val)} {es : List Entry}
    (hR : ∀ en ∈ es, FunAt rec en.scope en.ty ∧ DefaultFun E n en) {out out' : Option FieldList}
    (h1 : GroupOut E v n rec cs es out) (h2 : GroupOut E v n rec cs es out') : out = out' := by
  obtain ⟨outs, f1, g1⟩ := h1
  obtain ⟨outs', f2, g2⟩ := h2
  have := forall₂_fun (fun en hen o o' a b => compOut_fun hv (hR en hen).1 (hR en hen).2 a b) f1 f2
  subst this
  split at g1
  · rename_i hn; simp only [hn, ↓reduceIte] at g2; rw [g1, g2]
  · rename_i hn; simp only [hn, Bool.false_eq_true, ↓reduceIte] at g2; rw [g1.2, g2.2]

theorem seqFields_fun {E : Env} {v : Variant} (hv : v.canonical = true) {n : Nat}
    {rec : Scope → Ty → Val → FieldList → Prop} {isExt : Bool} {rootEs : List Entry}
    {adds : List (List Entry × Bool)} {cs : List (String × Val)}
    (hR : ∀ en ∈ rootEs ++ adds.flatMap (·.1), FunAt rec en.scope en.ty ∧ DefaultFun E n en)
    {fl fl' : FieldList}
    (h1 : SeqFields E v n rec isExt rootEs adds cs fl) (h2 : SeqFields E v n rec isExt rootEs adds cs fl') :
    fl = fl' := by
  obtain ⟨_, ro, ao, r1, a1, e1⟩ := h1
  obtain ⟨_, ro', ao', r2, a2, e2⟩ := h2
  have hro : ro = ro' := forall₂_fun (fun en hen o o' a b =>
    compOut_fun hv (hR en (by simp [hen])).1 (hR en (by simp [hen])).2 a b) r1 r2
  have hao : ao = ao' := by
    refine forall₂_fun (fun a ha o o' x y => ?_) a1 a2
    have hm : ∀ en ∈ a.1, FunAt rec en.scope en.ty ∧ DefaultFun E n en :=
      fun en hen => hR en (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hen⟩))
    split at x
    · rename_i hg; simp only [hg, ↓reduceIte] at y; exact groupOut_fun hv hm x y
    · rename_i hg; simp only [hg, Bool.false_eq_true, ↓reduceIte] at y
      obtain ⟨e, he, cx⟩ := x; obtain ⟨e', he', cy⟩ := y
      rw [he] at he'; cases he'
      exact compOut_fun hv (hm e (by simp [he])).1 (hm e (by simp [he])).2 cx cy
  subst hro; subst hao
  split at e1
  · rename_i hx; simp only [hx, ↓reduceIte] at e2; rw [e1, e2]
  · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at e2; rw [e1.2, e2.2]


/-- `rec` sends components with keys equal both ways (22.1) to the same field-list. -/
def KeyInj (rec : Scope → Ty → Val → FieldList → Prop) (v : Variant) (sc : Scope) (el : Ty) : Prop :=
  ∀ w1 w2 f1 f2, rec sc el w1 f1 → rec sc el w2 f2 → bitsLe (setOfKey v f1) (setOfKey v f2) = true →
    bitsLe (setOfKey v f2) (setOfKey v f1) = true → f1 = f2

def CanonB (E : Env) (n : Nat) (R K : Scope → Ty → Prop) (sc' : Scope) (bt : Ty) : Prop :=
  match bt with
  | .enumerated root ext => ((enumNumbers root ext).map (·.1)).Nodup
  | .sequence r e r2 => ∀ en ∈ entries E n sc' r e r2, R en.scope en.ty ∧ DefaultFun E n en
  | .set r e r2 => ∀ p ∈ entryTags E n sc' r e r2, R p.1.scope p.1.ty ∧ DefaultFun E n p.1
  | .sequenceOf el => R sc' el
  | .setOf el => R sc' el ∧ K sc' el
  | .choice root ext => ((altTags E n sc' root ext).map (·.1.name)).Nodup ∧
      ∀ p ∈ altTags E n sc' root ext, R sc' p.1.ty
  | .embeddedPdv => R (.ofModule assocModule) (pdvGeneral "data-value")
  | .characterString => R (.ofModule assocModule) (pdvGeneral "string-value")
  | .external => False
  | .restricted k => k.knownMultiplier = true ∨ k.isRegister = false
  | .objectDescriptor => False
  | .time | .date | .timeOfDay | .dateTime | .duration => ∀ name, R (.ofModule timeEncModule) (.ref name)
  | .openType => False
  | _ => True

theorem splitEntries_mem {es : List Entry} {ext : Option (List ExtAdd)} {en : Entry}
    (h : en ∈ (splitEntries es ext).1 ++ (splitEntries es ext).2.flatMap (·.1)) : en ∈ es := by
  simp only [splitEntries, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨h, _⟩ | ⟨a, ⟨⟨b, i⟩, _, rfl⟩, h⟩
  · exact h
  · exact (List.mem_filter.mp h).1

/-- 22: the field-lists of two CANONICAL-PER orderings of one SET OF value. -/
theorem setOf_sorted {v : Variant} {rec : Scope → Ty → Val → FieldList → Prop} {sc : Scope} {el : Ty}
    (hR : FunAt rec sc el) (hK : KeyInj rec v sc el) {vs ws ws' : List Val} {fls fls' : List FieldList}
    (p1 : ws.Perm vs) (a1 : List.Forall₂ (rec sc el) ws fls)
    (s1 : fls.Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b) = true)
    (p2 : ws'.Perm vs) (a2 : List.Forall₂ (rec sc el) ws' fls')
    (s2 : fls'.Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b) = true) : fls = fls' := by
  -- the field-list of each component, chosen
  let f : Val → FieldList := fun w => if h : ∃ fl, rec sc el w fl then h.choose else []
  have hf : ∀ {ws : List Val} {fls : List FieldList}, List.Forall₂ (rec sc el) ws fls → fls = ws.map f := by
    intro ws fls h
    induction h with
    | nil => rfl
    | @cons w fl _ _ r _ ih =>
      have hex : ∃ fl, rec sc el w fl := ⟨fl, r⟩
      simp only [List.map_cons, ih, f, dif_pos hex]
      rw [hR w fl _ r hex.choose_spec]
  have hm : ∀ {ws : List Val} {fls : List FieldList}, List.Forall₂ (rec sc el) ws fls →
      ∀ a ∈ fls, ∃ w, rec sc el w a := by
    intro ws fls h
    induction h with
    | nil => intro a ha; cases ha
    | cons r _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, r⟩
      · exact ih a ha
  refine eq_of_perm_pairwise ?_ s1 s2 ?_
  · rw [hf a1, hf a2]; exact (p1.trans p2.symm).map f
  · intro a ha b hb hab hba
    obtain ⟨w1, r1⟩ := hm a1 a ha
    obtain ⟨w2, r2⟩ := hm a1 b hb
    exact hK w1 w2 a b r1 r2 hab hba

theorem idxOf?_mem {l : List String} {x : String} {k : Nat} (h : l.idxOf? x = some k) : x ∈ l := by
  have : (l.idxOf? x).isSome := by rw [h]; rfl
  simpa using this

/-- 23: the alternative, its index and the field-list of a CHOICE value. -/
theorem choice_fun {v : Variant} {rec : Scope → Ty → Val → FieldList → Prop} {sc' : Scope}
    {xs rootS addS : List (Alt × Option (List Tag))} {m : Nat} {isExt : Bool} {nm : String} {y : Val}
    {fl fl' : FieldList}
    (hnd : (xs.map (·.1.name)).Nodup) (hR : ∀ p ∈ xs, FunAt rec sc' p.1.ty)
    (hr : ∀ p ∈ rootS, p ∈ xs.take m) (ha : ∀ p ∈ addS, p ∈ xs.drop m)
    (h1 : ∃ a afl, rec sc' a.ty y afl ∧
      ((∃ k, (rootS.map (·.1.name)).idxOf? nm = some k ∧ rootS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inl k) afl fl) ∨
       (∃ k, (addS.map (·.1.name)).idxOf? nm = some k ∧ addS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inr k) afl fl)))
    (h2 : ∃ a afl, rec sc' a.ty y afl ∧
      ((∃ k, (rootS.map (·.1.name)).idxOf? nm = some k ∧ rootS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inl k) afl fl') ∨
       (∃ k, (addS.map (·.1.name)).idxOf? nm = some k ∧ addS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inr k) afl fl'))) : fl = fl' := by
  have disj : ∀ k k', (rootS.map (·.1.name)).idxOf? nm = some k → (addS.map (·.1.name)).idxOf? nm = some k' →
      False := by
    intro k k' a b
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (idxOf?_mem a)
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp (idxOf?_mem b)
    rw [← List.take_append_drop m xs, List.map_append] at hnd
    exact List.disjoint_of_nodup_append hnd (List.mem_map_of_mem (hr p hp))
      (hpn.trans hqn.symm ▸ List.mem_map_of_mem (ha q hq))
  have get : ∀ (S : List (Alt × Option (List Tag))) (k : Nat) (a : Alt), (∀ p ∈ S, p ∈ xs) →
      S[k]?.map (·.1) = some a → FunAt rec sc' a.ty := by
    intro S k a hS h
    cases hk : S[k]? with
    | none => rw [hk] at h; cases h
    | some p =>
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      exact hR p (hS p (List.mem_of_getElem? hk))
  obtain ⟨a, afl, r1, c1⟩ := h1
  obtain ⟨a', afl', r2, c2⟩ := h2
  rcases c1 with ⟨k, i1, g1, f1⟩ | ⟨k, i1, g1, f1⟩ <;> rcases c2 with ⟨k', i2, g2, f2⟩ | ⟨k', i2, g2, f2⟩
  · rw [i1] at i2; cases i2
    rw [g1] at g2; cases g2
    have := get rootS k a (fun p hp => List.mem_of_mem_take (hr p hp)) g1 y afl afl' r1 r2
    subst this; simp only [ChoiceFields] at f1 f2; rw [f1, f2]
  · exact (disj _ _ i1 i2).elim
  · exact (disj _ _ i2 i1).elim
  · rw [i1] at i2; cases i2
    rw [g1] at g2; cases g2
    have := get addS k a (fun p hp => List.mem_of_mem_drop (ha p hp)) g1 y afl afl' r1 r2
    subst this; simp only [ChoiceFields] at f1 f2; rw [f1.2, f2.2]

theorem perB_fun {E : Env} {al : Bool} {n : Nat} {rec : Scope → Ty → Val → FieldList → Prop}
    {R K : Scope → Ty → Prop} (hR : ∀ sc t, R sc t → FunAt rec sc t)
    (hK : ∀ sc t, K sc t → KeyInj rec ⟨al, true⟩ sc t)
    {sc : Scope} {t : Ty} {sc' : Scope} {bt : Ty} {x : Val} {fl fl' : FieldList}
    (hc : CanonB E n R K sc' bt) (h1 : perB E ⟨al, true⟩ n rec sc t sc' bt x fl)
    (h2 : perB E ⟨al, true⟩ n rec sc t sc' bt x fl') : fl = fl' := by
  unfold perB at h1 h2
  unfold CanonB at hc
  split at h1
  all_goals first | (rw [h1, h2]) | skip
  all_goals try simp only at h2 hc
  case h_2 => exact intFields_fun h1 h2
  case h_3 => exact enumFields_fun hc h1 h2
  case h_4 =>
    obtain ⟨o1, a, rfl⟩ := h1; obtain ⟨o2, b, rfl⟩ := h2
    rw [realContents_der_fun a b]
  case h_5 =>
    obtain ⟨s1, a1, b1⟩ := h1; obtain ⟨s2, a2, b2⟩ := h2
    have : s1 = s2 := by
      split at a1
      · rename_i hn; simp only [hn, ↓reduceIte] at a2; rw [a1, a2]
      · rename_i hn; simp only [hn, ↓reduceIte] at a2; exact namedBitsSent_fun a1 a2
    subst this; exact bitsFields_fun b1 b2
  case h_6 => exact octetsFields_fun h1 h2
  case h_8 r e r2 cs =>
    rcases hs : splitEntries (entries E n sc' r e r2) e with ⟨rootEs, adds⟩
    rw [hs] at h1 h2
    refine seqFields_fun rfl (fun en hen => ?_) h1 h2
    have hm := splitEntries_mem (es := entries E n sc' r e r2) (ext := e) (by rw [hs]; exact hen)
    exact ⟨hR _ _ (hc en hm).1, (hc en hm).2⟩
  case h_9 r e r2 cs =>
    refine seqFields_fun rfl (fun en hen => ?_) h1 h2
    simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hen
    rcases hen with ⟨p, hp, rfl⟩ | ⟨a, ha, hen⟩
    · have hp' := (List.mem_filter.mp (List.mem_mergeSort.mp (by unfold sortByTag at hp; exact hp))).1
      exact ⟨hR _ _ (hc p hp').1, (hc p hp').2⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (splitEntries_mem (es := (entryTags E n sc' r e r2).map (·.1))
        (ext := e) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hen⟩)))
      exact ⟨hR _ _ (hc q hq).1, (hc q hq).2⟩
  case h_10 el vs =>
    obtain ⟨fls, a1, b1⟩ := h1; obtain ⟨fls', a2, b2⟩ := h2
    have := forall₂_fun (fun w _ f f' x y => hR _ _ hc w f f' x y) a1 a2
    subst this; exact seqOfFields_fun b1 b2
  case h_11 el vs =>
    obtain ⟨ws, fls, p1, a1, s1, b1⟩ := h1; obtain ⟨ws', fls', p2, a2, s2, b2⟩ := h2
    have := setOf_sorted (hR _ _ hc.1) (hK _ _ hc.2) p1 a1 (s1 rfl) p2 a2 (s2 trivial)
    subst this; exact seqOfFields_fun b1 b2
  case h_12 root ext nm y =>
    refine choice_fun (m := root.length) hc.1 (fun p hp => hR _ _ (hc.2 p hp)) ?_ ?_ h1 h2
    · intro p hp; unfold sortByTag at hp; exact List.mem_mergeSort.mp hp
    · intro p hp; unfold sortByTag at hp; exact List.mem_mergeSort.mp hp
  case h_17 cs =>
    split at h1
    · rename_i hp; simp only [hp, ↓reduceIte] at h2
      obtain ⟨os, l1, o1⟩ := h1; obtain ⟨os', l2, o2⟩ := h2
      rw [l1] at l2; cases l2; exact octetsFields_fun o1 o2
    · rename_i hp; simp only [hp, ↓reduceIte] at h2; exact hR _ _ hc _ _ _ h1 h2
  case h_20 cs =>
    split at h1
    · rename_i hp; simp only [hp, ↓reduceIte] at h2
      obtain ⟨os, l1, o1⟩ := h1; obtain ⟨os', l2, o2⟩ := h2
      rw [l1] at l2; cases l2; exact octetsFields_fun o1 o2
    · rename_i hp; simp only [hp, ↓reduceIte] at h2; exact hR _ _ hc _ _ _ h1 h2
  case h_19 k =>
    split at h1
    · rename_i hk; simp only [hk, ↓reduceIte] at h2
      obtain ⟨cs, rfl, k1⟩ := h1; obtain ⟨cs', e, k2⟩ := h2
      cases e; exact kmFields_fun k1 k2
    · rename_i hk; simp only [hk, Bool.false_eq_true, ↓reduceIte] at h2
      have hr : k.isRegister = false := by
        rcases hc with h | h
        · exact absurd h hk
        · exact h
      exact otherString_fun rfl hr h1 h2
  all_goals first
    | (obtain ⟨cs, rfl, _, k1⟩ := h1; obtain ⟨cs', e, _, k2⟩ := h2; cases e; exact kmFields_fun k1 k2)
    | (obtain ⟨nm1, w1, t1, r1⟩ := h1; obtain ⟨nm2, w2, t2, r2⟩ := h2
       obtain ⟨rfl, rfl⟩ := timeAs_fun t1 t2
       exact hR _ _ (hc nm1) _ _ _ r1 r2)


/-- What CANONICAL-PER needs of a type to be functional (`per_functional`), by fuel as `per`: at each
built-in type `CanonB`, the components needing `CanonT` at one less fuel. -/
def CanonT (E : Env) (al : Bool) : Nat → Scope → Ty → Prop
  | 0, _, _ => True
  | n + 1, sc, t => match builtin E n sc t with
    | some (sc', bt) => CanonB E n (CanonT E al n) (KeyInj (per E ⟨al, true⟩ n) ⟨al, true⟩) sc' bt
    | none => True

/-- **Canonicity** (X.691 3.7.4), as the functionality of CANONICAL-PER: a value of a type that meets
`CanonT` has one field-list, so one complete encoding. -/
theorem per_functional (E : Env) (al : Bool) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x : Val) (fl fl' : FieldList),
    CanonT E al n sc t → per E ⟨al, true⟩ n sc t x fl → per E ⟨al, true⟩ n sc t x fl' → fl = fl'
  | 0, _, _, _, _, _, _, h, _ => h.elim
  | n + 1, sc, t, x, fl, fl', hc, h1, h2 => by
    unfold per at h1 h2
    unfold CanonT at hc
    split at h1
    · rename_i sc' bt hb
      rw [hb] at h2 hc
      exact perB_fun (fun sc t hct x fl fl' a b => per_functional E al n sc t x fl fl' hct a b)
        (fun _ _ h => h) hc h1 h2
    · exact h1.elim

theorem per_canonical {E : Env} {al : Bool} {n : Nat} {sc : Scope} {t : Ty} {x : Val} {fl fl' : FieldList}
    (hc : CanonT E al n sc t) (h1 : per E ⟨al, true⟩ n sc t x fl) (h2 : per E ⟨al, true⟩ n sc t x fl') :
    complete ⟨al, true⟩ .other fl = complete ⟨al, true⟩ .other fl' := by
  rw [per_functional E al n sc t x fl fl' hc h1 h2]

/-! ## SET OF ties, for the values the decoder reads back -/

theorem bitsLe_both : ∀ (a b : Bits), bitsLe a b = true → bitsLe b a = true →
    (∃ z, a = b ++ List.replicate z false) ∨ (∃ z, b = a ++ List.replicate z false)
  | [], b, _, h2 => by
    right; refine ⟨b.length, ?_⟩
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [bitsLe, List.all_eq_true, beq_iff_eq] at h2
      simp only [List.nil_append]
      exact List.eq_replicate_iff.mpr ⟨rfl, h2⟩
  | x :: xs, [], h1, _ => by
    left; refine ⟨(x :: xs).length, ?_⟩
    simp only [bitsLe, List.all_eq_true, beq_iff_eq] at h1
    exact List.eq_replicate_iff.mpr ⟨rfl, h1⟩
  | x :: xs, y :: ys, h1, h2 => by
    have e1 : bitsLe (x :: xs) (y :: ys) = (if x == y then bitsLe xs ys else (!x && y)) := rfl
    have e2 : bitsLe (y :: ys) (x :: xs) = (if y == x then bitsLe ys xs else (!y && x)) := rfl
    rw [e1] at h1; rw [e2] at h2

    cases x <;> cases y
    · simp only [beq_self_eq_true, ↓reduceIte] at h1 h2
      rcases bitsLe_both xs ys h1 h2 with ⟨z, hz⟩ | ⟨z, hz⟩
      · left; exact ⟨z, by rw [hz]; rfl⟩
      · right; exact ⟨z, by rw [hz]; rfl⟩
    · simp at h2
    · simp at h1
    · simp only [beq_self_eq_true, ↓reduceIte] at h1 h2
      rcases bitsLe_both xs ys h1 h2 with ⟨z, hz⟩ | ⟨z, hz⟩
      · left; exact ⟨z, by rw [hz]; rfl⟩
      · right; exact ⟨z, by rw [hz]; rfl⟩

theorem pad8_nil : pad8 [] = [] := by simp [pad8]

theorem pad8_len (c : Bits) : (pad8 c).length % 8 = 0 := by
  simp only [pad8, List.length_append, List.length_replicate]; omega

theorem pad8_ge (c : Bits) (h : c ≠ []) : 8 ≤ (pad8 c).length := by
  have := List.length_pos_of_ne_nil h
  have := pad8_len c
  simp only [pad8, List.length_append, List.length_replicate] at *; omega

theorem complete_key (v : Variant) (f : FieldList) :
    complete v .other f = if concatFields v.aligned [] f = [] then List.replicate 8 false else setOfKey v f := by
  have : (!v.aligned && (Carrier.other == Carrier.bitString)) = false := by cases v.aligned <;> rfl
  simp only [complete, this, Bool.false_eq_true, ↓reduceIte, setOfKey]

/-- Equal keys, read both ways, make one complete encoding a prefix of the other followed by zeros. -/
theorem complete_of_keys (v : Variant) {f1 f2 : FieldList} (z : Nat)
    (h : setOfKey v f1 = setOfKey v f2 ++ List.replicate z false) :
    ∃ z', complete v .other f1 = complete v .other f2 ++ List.replicate z' false := by
  rw [complete_key, complete_key]
  set c1 := concatFields v.aligned [] f1
  set c2 := concatFields v.aligned [] f2
  have k1 : setOfKey v f1 = pad8 c1 := rfl
  have k2 : setOfKey v f2 = pad8 c2 := rfl
  by_cases e2 : c2 = []
  · rw [k2, e2, pad8_nil, List.nil_append] at h
    by_cases e1 : c1 = []
    · exact ⟨0, by simp [e1, e2]⟩
    · simp only [e1, e2, ↓reduceIte, k1]
      have hl := pad8_ge c1 e1
      rw [k1] at h
      have hz : 8 ≤ z := by have := congrArg List.length h; simp at this; omega
      refine ⟨z - 8, ?_⟩
      rw [h, List.replicate_append_replicate]; congr 1; omega
  · have e1 : c1 ≠ [] := by
      intro e1; rw [k1, e1, pad8_nil] at h
      have := pad8_ge c2 e2
      have := congrArg List.length h; simp at this; rw [k2] at *; omega
    simp only [e1, e2, ↓reduceIte]
    exact ⟨z, h⟩

/-- SET OF ties are harmless for the values the decoder reads back: `KeyInj` holds for a component
type all of whose encodings are `PDec`. -/
theorem keyInj_of_pdec {E : Env} {v : Variant} {n : Nat} {frames : List X690.DFrame} {sc : Scope} {el : Ty}
    (hd : ∀ w f, per E v n sc el w f → PDec E v n frames sc el w f) : KeyInj (per E v n) v sc el := by
  intro w1 w2 f1 f2 r1 r2 a b
  have hc : complete v .other f1 = complete v .other f2 := by
    rcases bitsLe_both _ _ a b with ⟨z, hz⟩ | ⟨z, hz⟩
    · obtain ⟨z', h⟩ := complete_of_keys v z hz
      obtain ⟨hr, _⟩ := per_prefixFree r2 (hd _ _ r2) r1 (hd _ _ r1) h
      rw [h, hr, List.append_nil]
    · obtain ⟨z', h⟩ := complete_of_keys v z hz
      obtain ⟨hr, _⟩ := per_prefixFree r1 (hd _ _ r1) r2 (hd _ _ r2) h
      rw [h, hr, List.append_nil]
  exact (per_unambiguous r1 (hd _ _ r1) r2 (hd _ _ r2) hc).2

end Asn1.X691
