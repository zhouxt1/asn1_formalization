import Asn1.X690.DecComplete
import Asn1.X690.DecSound
import Asn1.X680.SoundValues

/-!
# X.690 is unambiguous

Two values that `ber` relates to the same encoding are the same abstract value (`eqv`, X.680):
`ber_unambiguous`, and for octets, `octets_unambiguous`. Not literal equality: BER leaves out a
DEFAULT component or encodes its default, sends SET components and SET OF elements in any order,
and adds or drops trailing 0 bits of a named bit string; CER and DER fix those choices, but a
SET or SET OF value is still unordered and an omitted DEFAULT the same as its default.

What is needed beyond `Decodable` (`UnambV`), all properties of a valid schema and of a value of
the type:
- distinct tags (X.680 25.6 in a SEQUENCE, 27.3 in a SET, 29.3 in a CHOICE): without them two
  alternatives or components can have the same encoding;
- a value has its mandatory root components (X.680 25.7; `ber` relates values without them, and
  `decode` checks them, `presentOkB`);
- COMPONENTS OF is expanded at the fuel (`entriesKnown`);
- a DEFAULT is a simple value, of a type whose values are equal when the same (as `DefaultDec`
  asks under CER and DER);
- a fixed-type field of a class is of such a type too, and not covered: open types, EXTERNAL,
  INSTANCE OF (as `Decodable`).
-/

namespace Asn1.X690
open Asn1.X680

/-! ## What unambiguity needs -/

/-- X.680 25.7: a component a value of the type may leave out: not a mandatory root component. -/
def _root_.Asn1.X680.Entry.mayAbsent (en : Entry) : Bool := !en.presence.isMandatory || en.addition.isSome

/-- Two sets of tags, both known, with no tag in common. -/
def TagsDisj (a b : Option (List Tag)) : Prop :=
  ∃ ta tb, a = some ta ∧ b = some tb ∧ ∀ tg ∈ ta, tg ∉ tb

/-- The components up to and including the first that every value has. -/
def untilMust : List (Entry × Ty) → List (Entry × Ty)
  | [] => []
  | c :: rest => if c.1.mayAbsent then c :: untilMust rest else [c]

/-- X.680 25.6: the tags of a component that may be left out differ from those of the components
after it, up to and including the next one every value has. -/
def SeqTagsOk (E : Env) (n : Nat) : List (Entry × Ty) → Prop
  | [] => True
  | c :: rest =>
    (c.1.mayAbsent = true → ∀ c' ∈ untilMust rest,
      TagsDisj (encTags E n c.1.scope c.2) (encTags E n c'.1.scope c'.2)) ∧ SeqTagsOk E n rest

/-- X.680 27.3: the components of a SET have distinct tags. -/
def SetTagsOk (E : Env) (n : Nat) (comps : List (Entry × Ty)) : Prop :=
  comps.Pairwise fun a b => TagsDisj (encTags E n a.1.scope a.2) (encTags E n b.1.scope b.2)

/-- X.680 29.3: the alternatives of a CHOICE have distinct tags. -/
def AltTagsOk (E : Env) (n : Nat) (sc : Scope) (alts : List (Alt × Ty)) : Prop :=
  alts.Pairwise fun a b => TagsDisj (encTags E n sc a.2) (encTags E n sc b.2)

mutual
  /-- `UnambV E p n sc t v`: what `ber_unambiguous` needs of the type `t` and the value `v`, beyond
  `Decodable`: distinct tags, mandatory components present, COMPONENTS OF expanded, simple
  DEFAULTs, fixed-type fields of a type whose values are equal when the same. -/
  def UnambV (E : Env) (p : Profile) : Nat → Scope → Ty → Val → Prop
    | 0, _, _, _ => True
    | n + 1, sc, .ref name, v => match resolveTy E n sc none name [] with
      | some (sc', t) => UnambV E p n sc' t v
      | none => True
    | n + 1, sc, .extRef mn name, v => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => UnambV E p n sc' t v
      | none => True
    | n + 1, sc, .paramRef mn name args, v => match resolveTy E n sc mn name args with
      | some (sc', t) => UnambV E p n sc' t v
      | none => True
    | n + 1, sc, .tagged _ _ t, v => UnambV E p n sc t v
    | n + 1, sc, .constrained t _, v => UnambV E p n sc t v
    | n + 1, sc, .selection nm t, v => match builtin E n sc t with
      | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
        | some alt => UnambV E p n sc' alt.ty v
        | none => True
      | _ => True
    | n + 1, sc, .sequence r e r2, .seq cs =>
      CompsU E p n sc r e r2 cs ∧ SeqTagsOk E n (compTys E n sc r e r2)
    | n + 1, sc, .set r e r2, .seq cs =>
      CompsU E p n sc r e r2 cs ∧ SetTagsOk E n (compTys E n sc r e r2)
    | n + 1, sc, .sequenceOf el, .seqOf vs => ∀ x ∈ vs, UnambV E p n sc el x
    | n + 1, sc, .setOf el, .setOf vs => ∀ x ∈ vs, UnambV E p n sc el x
    | n + 1, sc, .choice r e, .choice a x =>
      AltTagsOk E n sc (altTys E n sc r e) ∧
      (∀ alt ∈ altTys E n sc r e, alt.1.name = a → UnambV E p n sc alt.2 x) ∧
      (∀ alt ∈ choiceAlts r e, alt.name = a → UnambV E p n sc alt.ty x)
    | n + 1, _, .embeddedPdv, v =>
      UnambV E p n (.ofModule assocModule) (.tagged (univ 11) .implicit embeddedPdvAssoc) v ∧
      UnambV E p n (.ofModule assocModule) embeddedPdvAssoc v
    | n + 1, _, .characterString, v =>
      UnambV E p n (.ofModule assocModule) (.tagged (univ 29) .implicit characterStringAssoc) v ∧
      UnambV E p n (.ofModule assocModule) characterStringAssoc v
    | _ + 1, _, .objectDescriptor, v => StrBound .graphic v
    | n + 1, sc, .classField cls path, _ =>
      match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => eqIsEq E n sc' t = true
      | _ => False
    | n + 1, sc, .fromObjects src path, _ => match objSetClass E n sc src with
      | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
        | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => eqIsEq E n sc' t = true
        | _ => False
      | none => False
    | _ + 1, _, .openType, _ | _ + 1, _, .instanceOf _, _ | _ + 1, _, .external, _ => False
    | _ + 1, _, _, _ => True

  /-- The components of a SEQUENCE or SET value `cs`: COMPONENTS OF expanded, every mandatory root
  component present, each DEFAULT a simple value of a type whose values are equal when the same,
  and each component of the value `UnambV`, as encoded and as written. -/
  def CompsU (E : Env) (p : Profile) (n : Nat) (sc : Scope) (r : List Comp) (e : Option (List ExtAdd))
      (r2 : List Comp) (cs : List (String × Val)) : Prop :=
    entriesKnown E n sc r e r2 = true ∧
    (∀ en ∈ entries E n sc r e r2, en.mayAbsent = false → (cs.lookup en.name).isSome) ∧
    ∀ c ∈ compTys E n sc r e r2,
      (∀ d, c.1.presence = .default_ d →
        (evalLit E n c.1.scope d).isSome ∧ eqIsEq E n c.1.scope c.1.ty = true) ∧
      ∀ x, cs.lookup c.1.name = some x → UnambV E p n c.1.scope c.2 x ∧ UnambV E p n c.1.scope c.1.ty x
end

/-! ## Types whose values are equal when the same -/

/-- For these types `eqv` is equality (on values of the right kind). -/
theorem eq_of_eqv_eqIsEq (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    eqIsEq E n sc t = true → eqv E n sc t x y → x = y
  | 0, _, _, _, _, h, _ => by simp [eqIsEq] at h
  | n + 1, sc, t, x, y, h, he => by
    cases t with
    | ref name =>
      simp only [eqIsEq] at h; simp only [eqv] at he
      split at h
      · rename_i sc' t' hr; rw [hr] at he; exact eq_of_eqv_eqIsEq E n sc' t' x y h he
      · cases h
    | extRef mn name =>
      simp only [eqIsEq] at h; simp only [eqv] at he
      split at h
      · rename_i sc' t' hr; rw [hr] at he; exact eq_of_eqv_eqIsEq E n sc' t' x y h he
      · cases h
    | paramRef mn name args =>
      simp only [eqIsEq] at h; simp only [eqv] at he
      split at h
      · rename_i sc' t' hr; rw [hr] at he; exact eq_of_eqv_eqIsEq E n sc' t' x y h he
      · cases h
    | tagged tg k t => simp only [eqIsEq] at h; simp only [eqv] at he; exact eq_of_eqv_eqIsEq E n sc t x y h he
    | constrained t c => simp only [eqIsEq] at h; simp only [eqv] at he; exact eq_of_eqv_eqIsEq E n sc t x y h he
    | bitString named =>
      simp only [eqIsEq, List.isEmpty_iff] at h; subst h
      simp only [eqv] at he
      split at he
      · simp only [↓reduceIte] at he; rw [he]
      · exact he.elim
    | _ => first | (simp only [eqv] at he; exact he) | simp [eqIsEq] at h

/-- For these types `eqv` holds at more fuel. -/
theorem eqv_mono_eqIsEq (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    eqIsEq E n sc t = true → eqv E n sc t x y → eqv E (n + 1) sc t x y
  | 0, _, _, _, _, h, _ => by simp [eqIsEq] at h
  | n + 1, sc, t, x, y, h, he => by
    cases t with
    | ref name =>
      simp only [eqIsEq] at h; simp only [eqv] at he ⊢
      split at h
      · rename_i sc' t' hr; rw [hr] at he; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact eqv_mono_eqIsEq E n sc' t' x y h he
      · cases h
    | extRef mn name =>
      simp only [eqIsEq] at h; simp only [eqv] at he ⊢
      split at h
      · rename_i sc' t' hr; rw [hr] at he; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact eqv_mono_eqIsEq E n sc' t' x y h he
      · cases h
    | paramRef mn name args =>
      simp only [eqIsEq] at h; simp only [eqv] at he ⊢
      split at h
      · rename_i sc' t' hr; rw [hr] at he; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact eqv_mono_eqIsEq E n sc' t' x y h he
      · cases h
    | tagged tg k t =>
      simp only [eqIsEq] at h; simp only [eqv] at he ⊢; exact eqv_mono_eqIsEq E n sc t x y h he
    | constrained t c =>
      simp only [eqIsEq] at h; simp only [eqv] at he ⊢; exact eqv_mono_eqIsEq E n sc t x y h he
    | _ => first | (simp only [eqv] at he ⊢; exact he) | simp [eqIsEq] at h

/-- A value `ber` relates, of such a type, is the same as itself. -/
theorem ber_eqv_refl (E : Env) (p : Profile) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x : Val) (nd : Node),
    ber E p n sc t x nd → eqIsEq E (n + 1) sc t = true → eqv E (n + 1) sc t x x
  | 0, _, _, _, _, h, _ => h.elim
  | n + 1, sc, t, x, nd, hb, h => by
    cases t with
    | ref name =>
      simp only [ber] at hb; simp only [eqIsEq] at h; simp only [eqv]
      split at hb
      · rename_i sc' t' hr
        rw [resolveTy_mono hr (Nat.le_succ n)] at h ⊢
        exact ber_eqv_refl E p n sc' t' x nd hb h
      · exact hb.elim
    | extRef mn name =>
      simp only [ber] at hb; simp only [eqIsEq] at h; simp only [eqv]
      split at hb
      · rename_i sc' t' hr
        rw [resolveTy_mono hr (Nat.le_succ n)] at h ⊢
        exact ber_eqv_refl E p n sc' t' x nd hb h
      · exact hb.elim
    | paramRef mn name args =>
      simp only [ber] at hb; simp only [eqIsEq] at h; simp only [eqv]
      split at hb
      · rename_i sc' t' hr
        rw [resolveTy_mono hr (Nat.le_succ n)] at h ⊢
        exact ber_eqv_refl E p n sc' t' x nd hb h
      · exact hb.elim
    | tagged tg k t =>
      simp only [ber] at hb; simp only [eqIsEq] at h; simp only [eqv]
      obtain ⟨base, hb, _⟩ := hb
      exact ber_eqv_refl E p n sc t x base hb h
    | constrained t c =>
      simp only [ber] at hb; simp only [eqIsEq] at h; simp only [eqv]
      exact ber_eqv_refl E p n sc t x nd hb h
    | bitString named =>
      cases x with
      | bits bs => simp [eqv]
      | _ => simp [ber, timeKind?] at hb
    | _ => first | (simp [eqv]; done) | simp [eqIsEq] at h

theorem evalLit_mono (E : Env) : ∀ (n : Nat) (sc : Scope) (d d' : Val),
    evalLit E n sc d = some d' → evalLit E (n + 1) sc d = some d'
  | 0, _, _, _, h => by simp [evalLit] at h
  | n + 1, sc, d, d', h => by
    cases d with
    | ref mn name args =>
      simp only [evalLit] at h ⊢
      obtain ⟨⟨sc', v⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
      rw [resolveVal_mono hr (Nat.le_succ n)]
      exact evalLit_mono E n sc' v d' h
    | _ => simpa [evalLit] using h

/-- Two values `ber` relates to the same encoding, of a type whose values are equal when the same,
are equal: the decoder reads both (`dec_complete`). -/
theorem ber_eq_of_eqIsEq {E : Env} {p : Profile} {n : Nat} {sc : Scope} {t : Ty} {x y : Val} {nd : Node}
    (hx : ber E p n sc t x nd) (hy : ber E p n sc t y nd) (dx : Decodable E p n sc t x)
    (dy : Decodable E p n sc t y) (h : eqIsEq E (n + 1) sc t = true) : x = y := by
  obtain ⟨v1, h1, e1⟩ := dec_complete E p n [] none sc t x nd hx dx
  obtain ⟨v2, h2, e2⟩ := dec_complete E p n [] none sc t y nd hy dy
  rw [h1] at h2
  cases h2
  rw [← e1 h, ← e2 h]

/-! ## Components and alternatives -/

theorem autoNumber_length (l : List Bool) : (autoNumber l).length = l.length := by
  unfold autoNumber
  suffices ∀ (r : Nat) (acc : List Nat × Nat × Nat) (l : List Bool),
      (l.foldl (fun (acc : List Nat × Nat × Nat) add =>
        if add then (acc.1 ++ [r + acc.2.2], acc.2.1, acc.2.2 + 1) else (acc.1 ++ [acc.2.1], acc.2.1 + 1, acc.2.2))
        acc).1.length = acc.1.length + l.length from by simpa using this _ ([], 0, 0) l
  intro r acc l
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => cases b <;> simp [ih] <;> omega

/-- The entries `compTys` lists are those of `entries`, in order. -/
theorem compTys_fst {E : Env} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)} {r2 : List Comp} :
    (compTys E n sc r e r2).map (·.1) = entries E n sc r e r2 := by
  have h1 : (compTys E n sc r e r2).map (·.1) = (entryTags E n sc r e r2).map (·.1) := by
    unfold compTys; rw [List.map_map]; apply List.map_congr_left
    intro ⟨en, ts⟩ _; simp only [Function.comp]; split
    · split <;> rfl
    · rfl
  rw [h1]; unfold entryTags; simp only
  split
  · rw [List.map_map]
    have : ((fun x : Entry × Option (List Tag) => x.1) ∘ fun (x : Entry × Nat) =>
        (x.1, some [(⟨.context, x.2⟩ : Tag)])) = (·.1) := rfl
    rw [this, List.map_fst_zip]
    simp [autoNumber_length]
  · simp [Function.comp_def]

theorem mem_compTys {E : Env} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)} {r2 : List Comp}
    {en : Entry} (h : en ∈ entries E n sc r e r2) : ∃ c ∈ compTys E n sc r e r2, c.1 = en := by
  rw [← compTys_fst] at h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  exact ⟨c, hc, rfl⟩

/-- An alternative `altTys` lists is one of the CHOICE's, with its type or that type tagged. -/
theorem altTys_mem {E : Env} {n : Nat} {sc : Scope} {r : List Alt} {e : Option (List AltAdd)} {alt : Alt × Ty}
    (h : alt ∈ altTys E n sc r e) :
    alt.1 ∈ choiceAlts r e ∧ (alt.2 = alt.1.ty ∨ ∃ tg kind, alt.2 = .tagged tg kind alt.1.ty) := by
  unfold altTys at h
  obtain ⟨⟨a, ts⟩, ha, rfl⟩ := List.mem_map.mp h
  have hm : a ∈ choiceAlts r e := by
    cases n with
    | zero => simp [altTags] at ha
    | succ n =>
      simp only [altTags] at ha
      split at ha
      · obtain ⟨⟨a', k⟩, hz, he⟩ := List.mem_map.mp ha
        simp only [Prod.mk.injEq] at he; rw [← he.1]; exact List.of_mem_zip hz |>.1
      · obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
        simp only [Prod.mk.injEq] at he; rw [← he.1]; exact ha'
  refine ⟨?_, ?_⟩
  · dsimp only; split
    · split <;> exact hm
    · exact hm
  · dsimp only; split
    · split
      · right; exact ⟨_, _, rfl⟩
      · left; rfl
    · left; rfl

/-! ## More fuel, the same values -/

/-- The built-in types whose values are equal when the same (`eqIsEq`). -/
def EqLeaf : Ty → Prop
  | .boolean | .integer _ | .enumerated _ _ | .null | .objectIdentifier | .relativeOid
  | .octetString | .restricted _ | .utcTime | .generalizedTime => True
  | .bitString named => named = []
  | _ => False

theorem builtin_of_eqIsEq (E : Env) : ∀ (n : Nat) (sc : Scope) (t : Ty), eqIsEq E n sc t = true →
    ∃ sc' b, builtin E n sc t = some (sc', b) ∧ EqLeaf b
  | 0, _, _, h => by simp [eqIsEq] at h
  | n + 1, sc, t, h => by
    cases t with
    | ref name =>
      simp only [eqIsEq] at h; simp only [builtin]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact builtin_of_eqIsEq E n sc' t' h
      · cases h
    | extRef mn name =>
      simp only [eqIsEq] at h; simp only [builtin]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact builtin_of_eqIsEq E n sc' t' h
      · cases h
    | paramRef mn name args =>
      simp only [eqIsEq] at h; simp only [builtin]
      split at h
      · rename_i sc' t' hr; rw [hr]; exact builtin_of_eqIsEq E n sc' t' h
      · cases h
    | tagged tg k t => simp only [eqIsEq] at h; simp only [builtin]; exact builtin_of_eqIsEq E n sc t h
    | constrained t c => simp only [eqIsEq] at h; simp only [builtin]; exact builtin_of_eqIsEq E n sc t h
    | bitString named =>
      simp only [eqIsEq, List.isEmpty_iff] at h
      exact ⟨sc, _, rfl, h⟩
    | _ => first | exact ⟨sc, _, rfl, trivial⟩ | simp [eqIsEq] at h

theorem eqv_leaf {E : Env} {sc : Scope} {b : Ty} (hb : EqLeaf b) {m m' : Nat} {x y : Val}
    (h : eqv E (m + 1) sc b x y) : eqv E (m' + 1) sc b x y := by
  cases b <;> simp only [EqLeaf] at hb <;> first | (subst hb; simpa [eqv] using h) | (simpa [eqv] using h)

/-- A value `ber` relates is the same as itself, at a built-in type whose values are equal when
the same. -/
theorem ber_builtin_refl (E : Env) (p : Profile) : ∀ (n : Nat) (sc : Scope) (t : Ty) (v : Val) (nd : Node)
    (sc' : Scope) (b : Ty), ber E p n sc t v nd → builtin E n sc t = some (sc', b) → EqLeaf b →
    ∀ j, eqv E (j + 1) sc' b v v
  | 0, _, _, _, _, _, _, h, _, _, _ => h.elim
  | n + 1, sc, t, v, nd, sc', b, hv, hb, hl, j => by
    cases t with
    | ref name =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hv
      · rename_i s1 t1 hr; rw [hr] at hb; exact ber_builtin_refl E p n s1 t1 v nd sc' b hv hb hl j
      · exact hv.elim
    | extRef mn name =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hv
      · rename_i s1 t1 hr; rw [hr] at hb; exact ber_builtin_refl E p n s1 t1 v nd sc' b hv hb hl j
      · exact hv.elim
    | paramRef mn name args =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hv
      · rename_i s1 t1 hr; rw [hr] at hb; exact ber_builtin_refl E p n s1 t1 v nd sc' b hv hb hl j
      · exact hv.elim
    | tagged tg k t =>
      simp only [ber] at hv; simp only [builtin] at hb
      obtain ⟨base, hv, _⟩ := hv
      exact ber_builtin_refl E p n sc t v base sc' b hv hb hl j
    | constrained t c =>
      simp only [ber] at hv; simp only [builtin] at hb
      exact ber_builtin_refl E p n sc t v nd sc' b hv hb hl j
    | selection nm t =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hv
      · rename_i s1 root ext hs
        rw [hs] at hb; simp only at hb hv
        split at hv
        · rename_i a ha; rw [ha] at hb; exact ber_builtin_refl E p n _ _ v nd sc' b hv hb hl j
        · exact hv.elim
      · exact hv.elim
    | classField cls path =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hb
      · rename_i s1 nm t1 u o hf; rw [hf] at hv; exact ber_builtin_refl E p n _ _ v nd sc' b hv hb hl j
      · rename_i s1 nm t1 u hf; rw [hf] at hv; exact ber_builtin_refl E p n _ _ v nd sc' b hv hb hl j
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hb; obtain ⟨-, rfl⟩ := hb; exact hl.elim)
        | cases hb
    | fromObjects src path =>
      simp only [ber] at hv; simp only [builtin] at hb
      split at hb
      · rename_i csc cls ho
        rw [ho] at hv; simp only at hv
        split at hb
        · rename_i s1 nm t1 u o hf; rw [hf] at hv; exact ber_builtin_refl E p n _ _ v nd sc' b hv hb hl j
        · rename_i s1 nm t1 u hf; rw [hf] at hv; exact ber_builtin_refl E p n _ _ v nd sc' b hv hb hl j
        · cases hb
      · cases hb
    | instanceOf cls =>
      simp only [builtin] at hb
      cases n with
      | zero => simp [builtin] at hb
      | succ n =>
        simp only [instanceOfTy, builtin, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb; exact hl.elim
    | bitString named =>
      simp only [builtin, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      cases v with
      | bits bs => simp [eqv]
      | _ => simp [ber, timeKind?] at hv
    | _ =>
      simp only [builtin, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      first | exact hl.elim | simp [eqv]

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} {P : α → Prop} :
    ∀ {l1 : List α} {l2 : List β}, (∀ a ∈ l1, P a) → (∀ a b, P a → R a b → S a b) →
      List.Forall₂ R l1 l2 → List.Forall₂ S l1 l2
  | _, _, _, _, .nil => .nil
  | _ :: _, _ :: _, hp, h, .cons hr hs =>
    .cons (h _ _ (hp _ (List.mem_cons_self ..)) hr)
      (forall₂_imp_mem (fun a ha => hp a (List.mem_cons_of_mem _ ha)) h hs)

/-- **More fuel, the same values**: `eqv` at more fuel, for an `UnambV` value. -/
theorem eqv_mono (E : Env) (p : Profile) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x y : Val),
    UnambV E p n sc t x → eqv E n sc t x y → eqv E (n + 1) sc t x y
  | 0, _, _, _, _, _, h => by simp [eqv] at h
  | n + 1, sc, t, x, y, hu, he => by
    have IH : ∀ {sc t x y}, UnambV E p n sc t x → eqv E n sc t x y → eqv E (n + 1) sc t x y :=
      fun hu he => eqv_mono E p n _ _ _ _ hu he
    cases t with
    | ref name =>
      simp only [UnambV] at hu; simp only [eqv] at he ⊢
      split at he
      · rename_i sc' t' hr; rw [hr] at hu; rw [resolveTy_mono hr (Nat.le_succ n)]; exact IH hu he
      · exact he.elim
    | extRef mn name =>
      simp only [UnambV] at hu; simp only [eqv] at he ⊢
      split at he
      · rename_i sc' t' hr; rw [hr] at hu; rw [resolveTy_mono hr (Nat.le_succ n)]; exact IH hu he
      · exact he.elim
    | paramRef mn name args =>
      simp only [UnambV] at hu; simp only [eqv] at he ⊢
      split at he
      · rename_i sc' t' hr; rw [hr] at hu; rw [resolveTy_mono hr (Nat.le_succ n)]; exact IH hu he
      · exact he.elim
    | tagged tg k t => simp only [UnambV] at hu; simp only [eqv] at he ⊢; exact IH hu he
    | constrained t c => simp only [UnambV] at hu; simp only [eqv] at he ⊢; exact IH hu he
    | selection nm t =>
      simp only [UnambV] at hu; simp only [eqv] at he ⊢
      split at he
      · rename_i sc' root ext hb
        rw [hb] at hu; rw [builtin_mono hb (Nat.le_succ n)]; simp only at hu ⊢
        split at he
        · rename_i a ha; simp only [ha] at hu ⊢; exact IH hu he
        · exact he.elim
      · exact he.elim
    | classField cls path =>
      simp only [eqv] at he ⊢
      split at he
      · rename_i sc'' b hb
        rw [builtin_mono hb (Nat.le_succ n)]; simp only
        -- the field's type is one whose values are equal when the same
        cases n with
        | zero => simp [builtin] at hb
        | succ n =>
          simp only [builtin] at hb
          simp only [UnambV] at hu
          split at hb
          · rename_i s1 nm t1 u o hf
            rw [bind_fields_mono hf (Nat.le_succ n)] at hu; simp only at hu
            obtain ⟨_, _, hb', hl⟩ := builtin_of_eqIsEq E _ _ _ hu
            rw [builtin_mono hb (Nat.le_succ n)] at hb'; cases hb'
            exact eqv_leaf hl he
          · rename_i s1 nm t1 u hf
            rw [bind_fields_mono hf (Nat.le_succ n)] at hu; simp only at hu
            obtain ⟨_, _, hb', hl⟩ := builtin_of_eqIsEq E _ _ _ hu
            rw [builtin_mono hb (Nat.le_succ n)] at hb'; cases hb'
            exact eqv_leaf hl he
          all_goals first
            | (rename_i hf; rw [bind_fields_mono hf (Nat.le_succ n)] at hu; exact hu.elim)
            | cases hb
      · exact he.elim
    | instanceOf cls => simp [UnambV] at hu
    | openType => simp [UnambV] at hu
    | external => simp [UnambV] at hu
    | embeddedPdv => simp only [UnambV] at hu; simp only [eqv] at he ⊢; exact IH hu.2 he
    | characterString => simp only [UnambV] at hu; simp only [eqv] at he ⊢; exact IH hu.2 he
    | sequenceOf el =>
      cases x with
      | seqOf xs =>
        cases y with
        | seqOf ys =>
          simp only [UnambV] at hu; simp only [eqv] at he ⊢
          exact forall₂_imp_mem hu (fun a b ha hab => IH ha hab) he
        | _ => simp [eqv] at he
      | _ => simp [eqv] at he
    | setOf el =>
      cases x with
      | setOf xs =>
        cases y with
        | setOf ys =>
          simp only [UnambV] at hu; simp only [eqv] at he ⊢
          obtain ⟨ys', hp, hf⟩ := he
          exact ⟨ys', hp, forall₂_imp_mem hu (fun a b ha hab => IH ha hab) hf⟩
        | _ => simp [eqv] at he
      | _ => simp [eqv] at he
    | choice r e =>
      cases x with
      | choice a x =>
        cases y with
        | choice b y =>
          simp only [UnambV] at hu; simp only [eqv] at he ⊢
          obtain ⟨rfl, alt, hm, hn, he⟩ := he
          exact ⟨rfl, alt, hm, hn, IH (hu.2.2 alt hm hn) he⟩
        | _ => simp [eqv] at he
      | _ => simp [eqv] at he
    | sequence r e r2 | set r e r2 =>
      cases x with
      | seq cs =>
        cases y with
        | seq ds =>
          simp only [UnambV, CompsU] at hu; simp only [eqv] at he ⊢
          obtain ⟨⟨hk, -, hc⟩, -⟩ := hu
          rw [entries_stable hk (Nat.le_succ n)]
          obtain ⟨h1, h2, h3⟩ := he
          refine ⟨h1, h2, fun en hen => ?_⟩
          obtain ⟨c, hcm, rfl⟩ := mem_compTys hen
          obtain ⟨hdef, hval⟩ := hc c hcm
          have h3 := h3 c.1 hen
          revert h3; unfold SeqEntry
          cases hx : cs.lookup c.1.name with
          | none =>
            cases hy : ds.lookup c.1.name with
            | none => simp
            | some y =>
              simp only
              split
              · rename_i d hd
                obtain ⟨hl, hq⟩ := hdef d hd
                obtain ⟨d'', hd''⟩ := Option.isSome_iff_exists.mp hl
                rintro ⟨d', hv, he⟩
                have := evalLit_spec E n _ _ _ _ hd'' hv; subst this
                exact ⟨d', evalLit_evalVal E _ _ _ _ (evalLit_mono E _ _ _ _ hd''), eqv_mono_eqIsEq E _ _ _ _ _ hq he⟩
              · exact id
          | some x =>
            cases hy : ds.lookup c.1.name with
            | none =>
              simp only
              split
              · rename_i d hd
                obtain ⟨hl, hq⟩ := hdef d hd
                obtain ⟨d'', hd''⟩ := Option.isSome_iff_exists.mp hl
                rintro ⟨d', hv, he⟩
                have := evalLit_spec E n _ _ _ _ hd'' hv; subst this
                exact ⟨d', evalLit_evalVal E _ _ _ _ (evalLit_mono E _ _ _ _ hd''), eqv_mono_eqIsEq E _ _ _ _ _ hq he⟩
              · exact id
            | some y => exact IH (hval x hx).2
        | _ => simp [eqv] at he
      | _ => simp [eqv] at he
    | _ => simp only [eqv] at he ⊢; exact he

/-! ## Which component each encoding is -/

theorem retag_inj {a b : Node} {tg : Tag} (ht : a.tag = b.tag) (h : a.retag tg = b.retag tg) : a = b := by
  cases a <;> cases b <;> simp_all [Node.retag, Node.tag]

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {a : α}, List.Forall₂ R l1 l2 → a ∈ l1 → ∃ b ∈ l2, R a b
  | _, _, _, .nil, ha => absurd ha List.not_mem_nil
  | _ :: _, b :: _, a, .cons h hs, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨b', hb', h'⟩ := forall₂_mem_left hs ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem forall₂_join {α β γ : Type} {R : α → γ → Prop} {S : β → γ → Prop} :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ}, List.Forall₂ R l1 l3 → List.Forall₂ S l2 l3 →
      List.Forall₂ (fun a b => ∃ c, R a c ∧ S b c) l1 l2
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 hs1, .cons h2 hs2 => .cons ⟨_, h1, h2⟩ (forall₂_join hs1 hs2)

theorem forall₂_fst {α β γ : Type} {P : α × β → α × γ → Prop} :
    ∀ {L : List (α × β)} {out : List (α × γ)}, List.Forall₂ (fun q r => r.1 = q.1 ∧ P q r) L out →
      out.map (·.1) = L.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [h.1, forall₂_fst hs]

/-- The encoding of a component has one of the component's tags, where they are known. -/
def TagIn (E : Env) (n : Nat) (q : (Entry × Ty) × Node) : Prop :=
  ∀ ts, encTags E n q.1.1.scope q.1.2 = some ts → q.2.tag ∈ ts

theorem tagsDisj_symm {a b : Option (List Tag)} (h : TagsDisj a b) : TagsDisj b a := by
  obtain ⟨ta, tb, ha, hb, hd⟩ := h
  exact ⟨tb, ta, hb, ha, fun tg ht ht' => hd tg ht' ht⟩

/-- The first encoding of a SEQUENCE is for a component no later than the first one every value
has. -/
theorem untilMust_mem : ∀ {l : List (Entry × Ty)} {x : Entry × Ty} {s' : List (Entry × Ty)},
    (x :: s').Sublist l → l.Nodup → (∀ m ∈ l, m.1.mayAbsent = false → m ∈ x :: s') → x ∈ untilMust l
  | [], _, _, hs, _, _ => by simp at hs
  | y :: l, x, s', hs, hnd, hm => by
    rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
    · have hy : y.1.mayAbsent = true := by
        cases hy : y.1.mayAbsent
        · have := hm y (List.mem_cons_self ..) hy
          exact absurd (hs.subset this) (List.nodup_cons.mp hnd).1
        · rfl
      simp only [untilMust, hy, ↓reduceIte]
      refine List.mem_cons_of_mem _ (untilMust_mem hs (List.nodup_cons.mp hnd).2 (fun m hml hma => ?_))
      exact hm m (List.mem_cons_of_mem _ hml) hma
    · simp only [List.cons.injEq] at hr
      rw [hr.1]
      simp only [untilMust]; split <;> simp

/-- X.680 25.6: the encodings of a SEQUENCE value say which component each is. -/
theorem seq_match {E : Env} {n : Nat} : ∀ (comps : List (Entry × Ty)) (o1 o2 : List ((Entry × Ty) × Node)),
    comps.Nodup → SeqTagsOk E n comps → (o1.map (·.1)).Sublist comps → (o2.map (·.1)).Sublist comps →
    o1.map (·.2) = o2.map (·.2) →
    (∀ c ∈ comps, c.1.mayAbsent = false → c ∈ o1.map (·.1)) →
    (∀ c ∈ comps, c.1.mayAbsent = false → c ∈ o2.map (·.1)) →
    (∀ q ∈ o1, TagIn E n q) → (∀ q ∈ o2, TagIn E n q) → o1 = o2
  | [], o1, o2, _, _, h1, h2, _, _, _, _, _ => by
    have e1 := List.sublist_nil.mp h1; have e2 := List.sublist_nil.mp h2
    simp only [List.map_eq_nil_iff] at e1 e2; rw [e1, e2]
  | c :: rest, [], [], _, _, _, _, _, _, _, _, _ => rfl
  | c :: rest, [], _ :: _, _, _, _, _, hs, _, _, _, _ => by simp at hs
  | c :: rest, _ :: _, [], _, _, _, _, hs, _, _, _, _ => by simp at hs
  | c :: rest, q1 :: o1, q2 :: o2, hnd, ht, h1, h2, hs, hm1, hm2, ti1, ti2 => by
    simp only [List.map_cons, List.cons.injEq] at hs h1 h2
    obtain ⟨hn, hs⟩ := hs
    have hc : c ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    obtain ⟨ht1, ht'⟩ := ht
    -- a component the first encoding skips is one a value may leave out, and the other's first
    -- encoding is then for a component its tags differ from
    have clash : ∀ (qa qb : (Entry × Ty) × Node) (ob : List ((Entry × Ty) × Node)),
        qa.1 = c → ((qb :: ob).map (·.1)).Sublist rest → (∀ m ∈ c :: rest, m.1.mayAbsent = false → m ∈ (qb :: ob).map (·.1)) →
        TagIn E n qa → TagIn E n qb → qa.2 = qb.2 → False := by
      intro qa qb ob hqa hsb hmb tia tib hab
      have hma : c.1.mayAbsent = true := by
        cases hy : c.1.mayAbsent
        · exact absurd (hsb.subset (hmb c (List.mem_cons_self ..) hy)) hc
        · rfl
      have hu := untilMust_mem hsb hnd' (fun m hm hma' => hmb m (List.mem_cons_of_mem _ hm) hma')
      obtain ⟨ta, tb, hta, htb, hd⟩ := ht1 hma qb.1 hu
      have := tia ta (by rw [hqa]; exact hta)
      exact hd _ this (hab ▸ tib tb htb)
    rcases List.sublist_cons_iff.mp h1 with k1 | ⟨r1, hr1, k1⟩ <;>
      rcases List.sublist_cons_iff.mp h2 with k2 | ⟨r2, hr2, k2⟩
    · -- both skip `c`
      exact seq_match rest (q1 :: o1) (q2 :: o2) hnd' ht' k1 k2 (by simp [hn, hs])
        (fun m hm hma => hm1 m (List.mem_cons_of_mem _ hm) hma)
        (fun m hm hma => hm2 m (List.mem_cons_of_mem _ hm) hma) ti1 ti2
    · simp only [List.cons.injEq] at hr2
      exact (clash q2 q1 o1 hr2.1 k1 hm1 (ti2 _ (List.mem_cons_self ..)) (ti1 _ (List.mem_cons_self ..)) hn.symm).elim
    · simp only [List.cons.injEq] at hr1
      exact (clash q1 q2 o2 hr1.1 k2 hm2 (ti1 _ (List.mem_cons_self ..)) (ti2 _ (List.mem_cons_self ..)) hn).elim
    · simp only [List.cons.injEq] at hr1 hr2
      obtain ⟨e1, rfl⟩ := hr1; obtain ⟨e2, rfl⟩ := hr2
      have hq : q1 = q2 := Prod.ext (e1.trans e2.symm) hn
      subst hq
      congr 1
      refine seq_match rest o1 o2 hnd' ht' k1 k2 hs (fun m hm hma => ?_) (fun m hm hma => ?_)
        (fun q hq => ti1 q (List.mem_cons_of_mem _ hq)) (fun q hq => ti2 q (List.mem_cons_of_mem _ hq))
      · rcases List.mem_cons.mp (hm1 m (List.mem_cons_of_mem _ hm) hma) with h | h
        · exact absurd hm (by rw [h]; simp only; rw [e1]; exact hc)
        · exact h
      · rcases List.mem_cons.mp (hm2 m (List.mem_cons_of_mem _ hm) hma) with h | h
        · exact absurd hm (by rw [h]; simp only; rw [e1]; exact hc)
        · exact h

/-- X.680 27.3: the encodings of a SET value say which component each is. -/
theorem set_match {E : Env} {n : Nat} {comps : List (Entry × Ty)} (ht : SetTagsOk E n comps) :
    ∀ (o1 o2 : List ((Entry × Ty) × Node)), o1.map (·.2) = o2.map (·.2) →
    (∀ q ∈ o1, q.1 ∈ comps ∧ TagIn E n q) → (∀ q ∈ o2, q.1 ∈ comps ∧ TagIn E n q) → o1 = o2
  | [], [], _, _, _ => rfl
  | [], _ :: _, hs, _, _ => by simp at hs
  | _ :: _, [], hs, _, _ => by simp at hs
  | q1 :: o1, q2 :: o2, hs, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨m1, t1⟩ := h1 q1 (List.mem_cons_self ..)
    obtain ⟨m2, t2⟩ := h2 q2 (List.mem_cons_self ..)
    have : q1.1 = q2.1 := by
      by_contra hne
      have : Std.Symm fun a b : Entry × Ty =>
          TagsDisj (encTags E n a.1.scope a.2) (encTags E n b.1.scope b.2) := ⟨fun _ _ h => tagsDisj_symm h⟩
      obtain ⟨ta, tb, hta, htb, hd⟩ := List.Pairwise.forall ht m1 m2 hne
      exact hd _ (t1 ta hta) (hs.1 ▸ t2 tb htb)
    rw [Prod.ext this hs.1, set_match ht o1 o2 hs.2 (fun q hq => h1 q (List.mem_cons_of_mem _ hq))
      (fun q hq => h2 q (List.mem_cons_of_mem _ hq))]

/-- Two lists of pairs, each a permutation of the other, with the same first components, none
repeated, are equal. -/
theorem eq_of_perm_fst {α β : Type} : ∀ {l1 l2 : List (α × β)}, l1.Perm l2 → l1.map (·.1) = l2.map (·.1) →
    (l1.map (·.1)).Nodup → l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => absurd h.length_eq (by simp)
  | _ :: _, [], h, _, _ => absurd h.length_eq (by simp)
  | x :: l1, y :: l2, hp, hf, hnd => by
    simp only [List.map_cons, List.cons.injEq] at hf
    have hx : x = y := by
      rcases List.mem_cons.mp (hp.subset (by simp : x ∈ x :: l1)) with h | h
      · exact h
      · have : x.1 ∈ l1.map (·.1) := hf.2 ▸ List.mem_map_of_mem h
        exact absurd this (List.nodup_cons.mp (by simpa using hnd)).1
    subst hx
    rw [eq_of_perm_fst (hp.cons_inv) hf.2 (by simpa using (List.nodup_cons.mp (by simpa using hnd)).2)]

/-- The pairs of what two values encode for each component, given encodings of the same
components to the same nodes. -/
def EncPair (E : Env) (p : Profile) (n : Nat) (c : Entry × Ty) : Option Val × Option Val → Prop
  | (some x, some y) => ∃ nd, ber E p n c.1.scope c.2 x nd ∧ ber E p n c.1.scope c.2 y nd
  | (none, none) => True
  | _ => False

theorem sel_pair {E : Env} {p : Profile} {n : Nat} {cs ds : List (String × Val)} :
    ∀ {comps : List (Entry × Ty)} {sel1 sel2 : List (Option Val)} {out : List ((Entry × Ty) × Node)},
    comps.Nodup →
    List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) comps sel1 →
    List.Forall₂ (fun c o => CompChoice E p n c.1 ds o) comps sel2 →
    List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) ((comps.zip sel1).filterMap fun (c, o) => o.map (c, ·)) out →
    List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) ((comps.zip sel2).filterMap fun (c, o) => o.map (c, ·)) out →
    List.Forall₂ (fun c (oo : Option Val × Option Val) =>
      CompChoice E p n c.1 cs oo.1 ∧ CompChoice E p n c.1 ds oo.2 ∧ EncPair E p n c oo) comps (sel1.zip sel2)
  | [], [], [], _, _, .nil, .nil, _, _ => .nil
  | c :: comps, o1 :: s1, o2 :: s2, out, hnd, .cons hc1 hs1, .cons hc2 hs2, ho1, ho2 => by
    have hc : c ∉ comps := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    -- an encoding the other value gives a later component would be for `c`
    have later : ∀ {cs' : List (String × Val)} {s : List (Option Val)} {r : (Entry × Ty) × Node}
        {out' : List ((Entry × Ty) × Node)},
        List.Forall₂ (fun c o => CompChoice E p n c.1 cs' o) comps s → r.1 = c →
        List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
          r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) ((comps.zip s).filterMap fun (c, o) => o.map (c, ·))
          (r :: out') → False := by
      intro cs' s r out' hs hr ho
      obtain ⟨q, L', hq, -, hL⟩ := List.forall₂_cons_right_iff.mp ho
      have hm := (compSel_spec hs).2 q (by rw [hL]; exact List.mem_cons_self ..)
      exact hc (hr ▸ hq.1 ▸ hm.1)
    cases o1 with
    | none =>
      cases o2 with
      | none =>
        simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_none] at ho1 ho2
        exact .cons ⟨hc1, hc2, trivial⟩ (sel_pair hnd' hs1 hs2 ho1 ho2)
      | some y =>
        simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_none, Option.map_some] at ho1 ho2
        cases out with
        | nil => cases ho2
        | cons r out' => exact (later hs1 (List.forall₂_cons.mp ho2).1.1 ho1).elim
    | some x =>
      cases o2 with
      | none =>
        simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_none, Option.map_some] at ho1 ho2
        cases out with
        | nil => cases ho1
        | cons r out' => exact (later hs2 (List.forall₂_cons.mp ho1).1.1 ho2).elim
      | some y =>
        simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_some] at ho1 ho2
        cases out with
        | nil => cases ho1
        | cons r out' =>
          obtain ⟨h1, ho1⟩ := List.forall₂_cons.mp ho1
          obtain ⟨h2, ho2⟩ := List.forall₂_cons.mp ho2
          refine .cons ⟨hc1, hc2, ?_⟩ (sel_pair hnd' hs1 hs2 ho1 ho2)
          refine ⟨r.2, ?_, ?_⟩
          · exact h1.2
          · exact h2.2

theorem cc_some {E : Env} {p : Profile} {n : Nat} {en : Entry} {cs : List (String × Val)} {x : Val}
    (h : CompChoice E p n en cs (some x)) :
    cs.lookup en.name = some x ∨ (cs.lookup en.name = none ∧ IsDefault E n en x) := by
  simp only [CompChoice] at h
  split at h
  · rename_i y hy; left; rw [hy, h.1]
  · rename_i hy; right; exact ⟨hy, h.2⟩

theorem cc_none {E : Env} {p : Profile} {n : Nat} {en : Entry} {cs : List (String × Val)}
    (h : CompChoice E p n en cs none) :
    cs.lookup en.name = none ∨ ∃ y, cs.lookup en.name = some y ∧ IsDefault E n en y := by
  simp only [CompChoice] at h
  split at h
  · rename_i y hy; right; exact ⟨y, hy, h⟩
  · rename_i hy; left; exact hy

/-- One component of two values whose encodings agree (`SeqEntry` at one more fuel). -/
theorem entry_eqv {E : Env} {p : Profile} {n : Nat} {en : Entry} {cs ds : List (String × Val)} {o1 o2 : Option Val}
    (h1 : CompChoice E p n en cs o1) (h2 : CompChoice E p n en ds o2) (hpat : o1.isSome = o2.isSome)
    (hxy : ∀ x y, o1 = some x → o2 = some y → eqv E (n + 1) en.scope en.ty x y)
    (hdef : ∀ d, en.presence = .default_ d → (evalLit E n en.scope d).isSome ∧ eqIsEq E n en.scope en.ty = true) :
    SeqEntry (evalVal E (n + 1)) (eqv E (n + 1)) cs ds en := by
  unfold SeqEntry
  cases hp : en.presence with
  | default_ d =>
    obtain ⟨hl, hq⟩ := hdef d hp
    obtain ⟨d'', hd⟩ := Option.isSome_iff_exists.mp hl
    have hev : evalVal E (n + 1) en.scope d d'' := evalLit_evalVal E _ _ _ _ (evalLit_mono E _ _ _ _ hd)
    -- a value equal to the default is the default
    have isd : ∀ z, IsDefault E n en z → z = d'' ∧ eqv E (n + 1) en.scope en.ty z d'' := by
      intro z hz
      simp only [IsDefault, hp] at hz
      obtain ⟨d', hv, he⟩ := hz
      have := evalLit_spec E n _ _ _ _ hd hv; subst this
      exact ⟨eq_of_eqv_eqIsEq E _ _ _ _ _ hq he, eqv_mono_eqIsEq E _ _ _ _ _ hq he⟩
    cases o1 with
    | some x =>
      cases o2 with
      | none => simp at hpat
      | some y =>
        have hxy := hxy x y rfl rfl
        rcases cc_some h1 with hx | ⟨hx, dx⟩ <;> rcases cc_some h2 with hy | ⟨hy, dy⟩ <;> simp only [hx, hy]
        · exact hxy
        · obtain ⟨rfl, -⟩ := isd y dy; exact ⟨y, hev, hxy⟩
        · obtain ⟨rfl, -⟩ := isd x dx; exact ⟨x, hev, hxy⟩
    | none =>
      cases o2 with
      | some _ => simp at hpat
      | none =>
        rcases cc_none h1 with hx | ⟨x, hx, dx⟩ <;> rcases cc_none h2 with hy | ⟨y, hy, dy⟩ <;> simp only [hx, hy]
        · obtain ⟨rfl, he⟩ := isd y dy; exact ⟨y, hev, he⟩
        · exact ⟨d'', hev, (isd x dx).2⟩
        · obtain ⟨rfl, he⟩ := isd x dx; obtain ⟨e, -⟩ := isd y dy; rw [e]; exact he
  | _ =>
    have nd : ∀ z, ¬ IsDefault E n en z := fun z hz => by simp [IsDefault, hp] at hz
    cases o1 with
    | some x =>
      cases o2 with
      | none => simp at hpat
      | some y =>
        rcases cc_some h1 with hx | ⟨hx, dx⟩
        · rcases cc_some h2 with hy | ⟨hy, dy⟩
          · simp only [hx, hy]; exact hxy x y rfl rfl
          · exact (nd _ dy).elim
        · exact (nd _ dx).elim
    | none =>
      cases o2 with
      | some _ => simp at hpat
      | none =>
        rcases cc_none h1 with hx | ⟨x, hx, dx⟩
        · rcases cc_none h2 with hy | ⟨y, hy, dy⟩
          · simp only [hx, hy]
          · exact (nd _ dy).elim
        · exact (nd _ dx).elim

/-! ## Unambiguity -/

theorem forall₂_mem_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {a : α}, List.Forall₂ R l1 l2 → a ∈ l1 → ∃ b, (a, b) ∈ l1.zip l2 ∧ R a b
  | _, _, _, .nil, ha => absurd ha List.not_mem_nil
  | _ :: _, b :: _, a, .cons h hs, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, by simp, h⟩
    · obtain ⟨b', hb', h'⟩ := forall₂_mem_zip hs ha
      exact ⟨b', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb', h'⟩

theorem forall₂_imp_mem2 {α β : Type} {R S : α → β → Prop} {P : α → Prop} {Q : β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, (∀ a ∈ l1, P a) → (∀ b ∈ l2, Q b) → (∀ a b, P a → Q b → R a b → S a b) →
      List.Forall₂ R l1 l2 → List.Forall₂ S l1 l2
  | _, _, _, _, _, .nil => .nil
  | _ :: _, _ :: _, hp, hq, h, .cons hr hs =>
    .cons (h _ _ (hp _ (List.mem_cons_self ..)) (hq _ (List.mem_cons_self ..)) hr)
      (forall₂_imp_mem2 (fun a ha => hp a (List.mem_cons_of_mem _ ha)) (fun b hb => hq b (List.mem_cons_of_mem _ hb)) h hs)

theorem decodable_of_choice {E : Env} {p : Profile} {n : Nat} {comps : List (Entry × Ty)} {cs : List (String × Val)}
    {c : Entry × Ty} {x : Val} (hd : CompsDec E p n comps cs) (hc : c ∈ comps) (h : CompChoice E p n c.1 cs (some x)) :
    Decodable E p n c.1.scope c.2 x := by
  unfold CompsDec at hd
  rcases cc_some h with hx | ⟨_, hx⟩
  · exact ((hd.2 c hc).1 x hx).1
  · exact (hd.2 c hc).2 x hx

/-- A component's encoded type is its type, or that type with an automatic tag. -/
theorem comp_eqv {E : Env} {p : Profile} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)}
    {r2 : List Comp} {c : Entry × Ty} (hc : c ∈ compTys E n sc r e r2) {x y : Val}
    (h : eqv E (n + 1) c.1.scope c.2 x y) (hu : UnambV E p n c.1.scope c.1.ty x) :
    eqv E (n + 1) c.1.scope c.1.ty x y := by
  rcases compTys_ty hc with h2 | ⟨tg, k, h2⟩
  · rwa [h2] at h
  · rw [h2] at h; simp only [eqv] at h; exact eqv_mono E p n _ _ _ _ hu h

theorem comp_eqv_refl {E : Env} {p : Profile} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)}
    {r2 : List Comp} {c : Entry × Ty} (hc : c ∈ compTys E n sc r e r2) {x : Val} {nd : Node}
    (hq : eqIsEq E n c.1.scope c.1.ty = true) (hb : ber E p n c.1.scope c.2 x nd) :
    eqv E (n + 1) c.1.scope c.1.ty x x := by
  have h := ber_eqv_refl E p n _ _ _ _ hb (eqIsEq_compTy hc hq)
  rcases compTys_ty hc with h2 | ⟨tg, k, h2⟩
  · rwa [h2] at h
  · rw [h2] at h; simp only [eqv] at h; exact eqv_mono_eqIsEq E n _ _ _ _ hq h

theorem out_sub {E : Env} {p : Profile} {n : Nat} {cs : List (String × Val)} {comps : List (Entry × Ty)}
    {sel : List (Option Val)} {out : List ((Entry × Ty) × Node)}
    (hs : List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) comps sel)
    (ho : List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) ((comps.zip sel).filterMap fun (c, o) => o.map (c, ·)) out) :
    (out.map (·.1)).Sublist comps := by
  rw [forall₂_fst ho]; exact (compSel_spec hs).1

theorem out_tags {E : Env} {p : Profile} {n : Nat} {cs : List (String × Val)} {comps : List (Entry × Ty)}
    {sel : List (Option Val)} {out : List ((Entry × Ty) × Node)}
    (hs : List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) comps sel)
    (ho : List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2) ((comps.zip sel).filterMap fun (c, o) => o.map (c, ·)) out) :
    ∀ q ∈ out, q.1 ∈ comps ∧ TagIn E n q := by
  intro q hq
  obtain ⟨q', hq', hr⟩ := forall₂_mem_right ho hq
  have hm := (compSel_spec hs).2 q' hq'
  refine ⟨hr.1 ▸ hm.1, fun ts hts => ?_⟩
  rw [hr.1] at hts
  exact ber_encTags E p n _ _ _ _ _ hr.2 hts

/-- X.680 25.7: a component every value has is encoded. -/
theorem out_must {E : Env} {p : Profile} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)}
    {r2 : List Comp} {cs : List (String × Val)} {sel : List (Option Val)} {out : List ((Entry × Ty) × Node)}
    (hu : CompsU E p n sc r e r2 cs)
    (hs : List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) (compTys E n sc r e r2) sel)
    (ho : List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2)
        (((compTys E n sc r e r2).zip sel).filterMap fun (c, o) => o.map (c, ·)) out) :
    ∀ c ∈ compTys E n sc r e r2, c.1.mayAbsent = false → c ∈ out.map (·.1) := by
  intro c hc hma
  unfold CompsU at hu
  have hen : c.1 ∈ entries E n sc r e r2 := by rw [← compTys_fst]; exact List.mem_map_of_mem hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hu.2.1 c.1 hen hma)
  have hmand : c.1.presence = .mandatory := by
    simp only [Entry.mayAbsent, Bool.or_eq_false_iff, Bool.not_eq_false'] at hma
    revert hma; cases c.1.presence <;> simp [Presence.isMandatory]
  obtain ⟨o, hz, hch⟩ := forall₂_mem_zip hs hc
  cases o with
  | none =>
    rcases cc_none hch with h | ⟨y', _, hd⟩
    · rw [h] at hy; cases hy
    · simp [IsDefault, hmand] at hd
  | some x =>
    rw [forall₂_fst ho]
    exact List.mem_map.mpr ⟨(c, x), List.mem_filterMap.mpr ⟨(c, some x), hz, rfl⟩, rfl⟩

/-- Two SEQUENCE or SET values whose components have the same encodings are the same value, given
the encodings of their components are. -/
theorem seqEqv_of_out {E : Env} {p : Profile} {n : Nat} {sc : Scope} {r : List Comp} {e : Option (List ExtAdd)}
    {r2 : List Comp} {cs ds : List (String × Val)} {sel1 sel2 : List (Option Val)} {out : List ((Entry × Ty) × Node)}
    (IH : ∀ {sc t v w nd}, ber E p n sc t v nd → ber E p n sc t w nd → Decodable E p n sc t v →
      Decodable E p n sc t w → UnambV E p n sc t v → UnambV E p n sc t w → eqv E (n + 1) sc t v w)
    (hn1 : ∀ q ∈ cs, q.1 ∈ (compTys E n sc r e r2).map (·.1.name))
    (hn2 : ∀ q ∈ ds, q.1 ∈ (compTys E n sc r e r2).map (·.1.name))
    (hs1 : List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) (compTys E n sc r e r2) sel1)
    (hs2 : List.Forall₂ (fun c o => CompChoice E p n c.1 ds o) (compTys E n sc r e r2) sel2)
    (ho1 : List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2)
        (((compTys E n sc r e r2).zip sel1).filterMap fun (c, o) => o.map (c, ·)) out)
    (ho2 : List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ ber E p n q.1.1.scope q.1.2 q.2 r.2)
        (((compTys E n sc r e r2).zip sel2).filterMap fun (c, o) => o.map (c, ·)) out)
    (dc1 : CompsDec E p n (compTys E n sc r e r2) cs) (dc2 : CompsDec E p n (compTys E n sc r e r2) ds)
    (uc1 : CompsU E p n sc r e r2 cs) (uc2 : CompsU E p n sc r e r2 ds) :
    SeqEqv (evalVal E (n + 1)) (entries E (n + 1) sc r e r2) (eqv E (n + 1)) cs ds := by
  have uc1' := uc1; have uc2' := uc2
  unfold CompsU at uc1' uc2'
  have hnd : (compTys E n sc r e r2).Nodup := by
    have := dc1; unfold CompsDec at this; exact List.Nodup.of_map _ this.1
  rw [entries_stable uc1'.1 (Nat.le_succ n)]
  have hnames : (compTys E n sc r e r2).map (·.1.name) = (entries E n sc r e r2).map (·.name) := by
    rw [← compTys_fst, List.map_map]; rfl
  refine ⟨fun q hq => hnames ▸ hn1 q hq, fun q hq => hnames ▸ hn2 q hq, fun en hen => ?_⟩
  obtain ⟨c, hc, rfl⟩ := mem_compTys hen
  have hP := sel_pair hnd hs1 hs2 ho1 ho2
  obtain ⟨oo, -, h1, h2, hpair⟩ := forall₂_mem_zip hP hc
  have hdef := (uc1'.2.2 c hc).1
  refine entry_eqv h1 h2 ?_ ?_ hdef
  · obtain ⟨o1, o2⟩ := oo; cases o1 <;> cases o2 <;> simp_all [EncPair]
  · intro x y hx hy
    obtain ⟨o1, o2⟩ := oo
    simp only at hx hy; subst hx; subst hy
    obtain ⟨nd', bx, by'⟩ := hpair
    have dx := decodable_of_choice dc1 hc h1
    have dy := decodable_of_choice dc2 hc h2
    by_cases hd : ∃ d, c.1.presence = .default_ d
    · obtain ⟨d, hd⟩ := hd
      have hq := (hdef d hd).2
      have := ber_eq_of_eqIsEq bx by' dx dy (eqIsEq_compTy hc hq); subst this
      exact comp_eqv_refl hc hq bx
    · have nd : ∀ z, ¬ IsDefault E n c.1 z := fun z hz => by
        simp only [IsDefault] at hz; split at hz
        · rename_i d hd'; exact hd ⟨d, hd'⟩
        · exact hz
      have lx : cs.lookup c.1.name = some x := by
        rcases cc_some h1 with h | ⟨_, h⟩
        · exact h
        · exact (nd _ h).elim
      have ly : ds.lookup c.1.name = some y := by
        rcases cc_some h2 with h | ⟨_, h⟩
        · exact h
        · exact (nd _ h).elim
      have ux := (uc1'.2.2 c hc).2 x lx
      have uy := (uc2'.2.2 c hc).2 y ly
      exact comp_eqv hc (IH bx by' dx dy ux.1 uy.1) ux.2

/-- **X.690 is unambiguous**: two values that `ber` relates to the same encoding, both
`Decodable` and `UnambV`, are the same abstract value of the type (`eqv`, one more fuel). -/
theorem ber_unambiguous (E : Env) (p : Profile) : ∀ (n : Nat) (sc : Scope) (t : Ty) (v w : Val) (nd : Node),
    ber E p n sc t v nd → ber E p n sc t w nd → Decodable E p n sc t v → Decodable E p n sc t w →
    UnambV E p n sc t v → UnambV E p n sc t w → eqv E (n + 1) sc t v w
  | 0, _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | n + 1, sc, t, v, w, nd, hv, hw, dv, dw, uv, uw => by
    have IH : ∀ {sc t v w nd}, ber E p n sc t v nd → ber E p n sc t w nd → Decodable E p n sc t v →
        Decodable E p n sc t w → UnambV E p n sc t v → UnambV E p n sc t w → eqv E (n + 1) sc t v w :=
      fun hv hw dv dw uv uw => ber_unambiguous E p n _ _ _ _ _ hv hw dv dw uv uw
    by_cases hq : eqIsEq E (n + 1) sc t = true
    · have := ber_eq_of_eqIsEq hv hw dv dw (eqIsEq_mono E _ _ _ hq)
      subst this
      exact ber_eqv_refl E p (n + 1) sc t v nd hv (eqIsEq_mono E _ _ _ hq)
    cases t with
    | ref name =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      split at hv
      · rename_i sc' t' hr
        rw [hr] at hw dv dw uv uw; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact IH hv hw dv dw uv uw
      · exact hv.elim
    | extRef mn name =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      split at hv
      · rename_i sc' t' hr
        rw [hr] at hw dv dw uv uw; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact IH hv hw dv dw uv uw
      · exact hv.elim
    | paramRef mn name args =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      split at hv
      · rename_i sc' t' hr
        rw [hr] at hw dv dw uv uw; rw [resolveTy_mono hr (Nat.le_succ n)]
        exact IH hv hw dv dw uv uw
      · exact hv.elim
    | tagged tg k t =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      obtain ⟨b1, hb1, he1⟩ := hv
      obtain ⟨b2, hb2, he2⟩ := hw
      have hb : b1 = b2 := by
        split at he1
        · rename_i hx; simp only [hx, ↓reduceIte] at he2
          obtain ⟨f1, rfl⟩ := he1; obtain ⟨f2, h⟩ := he2
          simp only [Node.cons.injEq, List.cons.injEq] at h; exact h.2.2.1
        · rename_i hx; simp only [hx] at he2
          obtain ⟨tb, htb⟩ := dv.2 (by simpa using hx)
          have t1 := ber_encTags E p n sc t _ _ _ hb1 htb
          have t2 := ber_encTags E p n sc t _ _ _ hb2 htb
          simp only [List.mem_singleton] at t1 t2
          exact retag_inj (t1.trans t2.symm) (he1.symm.trans he2)
      subst hb
      exact IH hb1 hb2 dv.1 dw.1 uv uw
    | constrained t c =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      exact IH hv hw dv.1 dw.1 uv uw
    | selection nm t =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      split at hv
      · rename_i sc' root ext hb
        rw [hb] at hw dv dw uv uw; rw [builtin_mono hb (Nat.le_succ n)]
        simp only at hw dv dw uv uw ⊢
        split at hv
        · rename_i a ha; simp only [ha] at hw dv dw uv uw ⊢; exact IH hv hw dv dw uv uw
        · exact hv.elim
      · exact hv.elim
    | classField cls path =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv; simp only [eqv]
      split at hv
      · rename_i sc' nm t1 u o hf
        rw [hf] at hw dv dw uv
        have := ber_eq_of_eqIsEq hv hw dv dw (eqIsEq_mono E _ _ _ uv); subst this
        obtain ⟨sc'', b, hb, hl⟩ := builtin_of_eqIsEq E n sc' t1 uv
        have hb' : builtin E (n + 1) sc (.classField cls path) = some (sc'', b) := by simp only [builtin, hf]; exact hb
        rw [hb']
        exact ber_builtin_refl E p n sc' t1 v nd sc'' b hv hb hl n
      · rename_i sc' nm t1 u hf
        rw [hf] at hw dv dw uv
        have := ber_eq_of_eqIsEq hv hw dv dw (eqIsEq_mono E _ _ _ uv); subst this
        obtain ⟨sc'', b, hb, hl⟩ := builtin_of_eqIsEq E n sc' t1 uv
        have hb' : builtin E (n + 1) sc (.classField cls path) = some (sc'', b) := by simp only [builtin, hf]; exact hb
        rw [hb']
        exact ber_builtin_refl E p n sc' t1 v nd sc'' b hv hb hl n
      all_goals first | exact hv.elim | (rename_i hf; rw [hf] at dv; simp at dv)
    | fromObjects src path =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv
      split at dv
      · rename_i csc cls ho
        rw [ho] at hv hw dw uv; dsimp only at hv hw dw uv
        split at dv
        · rename_i sc' nm t1 u o hf
          rw [hf] at hv hw dw uv
          have := ber_eq_of_eqIsEq hv hw dv dw (eqIsEq_mono E _ _ _ uv); subst this
          simp [eqv]
        · rename_i sc' nm t1 u hf
          rw [hf] at hv hw dw uv
          have := ber_eq_of_eqIsEq hv hw dv dw (eqIsEq_mono E _ _ _ uv); subst this
          simp [eqv]
        · exact dv.elim
      · exact dv.elim
    | sequence r e r2 =>
      cases v with
      | seq cs =>
        cases w with
        | seq ds =>
          simp only [ber, CompEncs] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw
          simp only [eqv]
          obtain ⟨f1, out1, rfl, hn1, sel1, hs1, ho1⟩ := hv
          obtain ⟨f2, out2, he, hn2, sel2, hs2, ho2⟩ := hw
          simp only [Node.cons.injEq] at he
          have hnd : (compTys E n sc r e r2).Nodup := by
            have := dv; unfold CompsDec at this; exact List.Nodup.of_map _ this.1
          have hout : out1 = out2 :=
            seq_match _ out1 out2 hnd uv.2 (out_sub hs1 ho1) (out_sub hs2 ho2) he.2.2
              (out_must uv.1 hs1 ho1) (out_must uw.1 hs2 ho2)
              (fun q hq => (out_tags hs1 ho1 q hq).2) (fun q hq => (out_tags hs2 ho2 q hq).2)
          subst hout
          exact seqEqv_of_out IH hn1 hn2 hs1 hs2 ho1 ho2 dv dw uv.1 uw.1
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | set r e r2 =>
      cases v with
      | seq cs =>
        cases w with
        | seq ds =>
          simp only [ber, CompEncs] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw
          simp only [eqv]
          obtain ⟨f1, out1, out1', rfl, ⟨hn1, sel1, hs1, ho1⟩, hp1, -, -⟩ := hv
          obtain ⟨f2, out2, out2', he, ⟨hn2, sel2, hs2, ho2⟩, hp2, -, -⟩ := hw
          simp only [Node.cons.injEq] at he
          have hnd : (compTys E n sc r e r2).Nodup := by
            have := dv; unfold CompsDec at this; exact List.Nodup.of_map _ this.1
          have h12 : out1 = out2 := set_match uv.2 out1 out2 he.2.2
            (fun q hq => out_tags hs1 ho1 q (hp1.subset hq)) (fun q hq => out_tags hs2 ho2 q (hp2.subset hq))
          subst h12
          have hp : out1'.Perm out2' := hp1.symm.trans hp2
          have s1 := out_sub hs1 ho1
          have s2 := out_sub hs2 ho2
          have hf : out1'.map (·.1) = out2'.map (·.1) :=
            (List.Nodup.perm_iff_eq_of_sublist hnd s1 s2).mp (hp.map _)
          have : out1' = out2' := eq_of_perm_fst hp hf (s1.nodup hnd)
          subst this
          exact seqEqv_of_out IH hn1 hn2 hs1 hs2 ho1 ho2 dv dw uv.1 uw.1
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | sequenceOf el =>
      cases v with
      | seqOf vs =>
        cases w with
        | seqOf ws =>
          simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
          obtain ⟨f1, ch1, rfl, hf1⟩ := hv
          obtain ⟨f2, ch2, he, hf2⟩ := hw
          simp only [Node.cons.injEq] at he
          rw [← he.2.2] at hf2
          exact forall₂_imp_mem2 (P := fun x => Decodable E p n sc el x ∧ UnambV E p n sc el x)
            (Q := fun x => Decodable E p n sc el x ∧ UnambV E p n sc el x)
            (fun a ha => ⟨dv a ha, uv a ha⟩) (fun b hb => ⟨dw b hb, uw b hb⟩)
            (fun a b ha hb ⟨c, h1, h2⟩ => IH h1 h2 ha.1 hb.1 ha.2 hb.2) (forall₂_join hf1 hf2)
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | setOf el =>
      cases v with
      | setOf vs =>
        cases w with
        | setOf ws =>
          simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
          obtain ⟨f1, ch1, ch1', rfl, hf1, hp1, -⟩ := hv
          obtain ⟨f2, ch2, ch2', he, hf2, hp2, -⟩ := hw
          simp only [Node.cons.injEq] at he
          rw [← he.2.2] at hp2
          have hp : ch1'.Perm ch2' := hp1.symm.trans hp2
          obtain ⟨l', hl', hpl⟩ := List.perm_comp_forall₂ hp hf2.flip
          refine ⟨l', hpl, ?_⟩
          exact forall₂_imp_mem2 (P := fun x => Decodable E p n sc el x ∧ UnambV E p n sc el x)
            (Q := fun x => Decodable E p n sc el x ∧ UnambV E p n sc el x)
            (fun a ha => ⟨dv a ha, uv a ha⟩) (fun b hb => ⟨dw b (hpl.subset hb), uw b (hpl.subset hb)⟩)
            (fun a b ha hb ⟨c, h1, h2⟩ => IH h1 h2 ha.1 hb.1 ha.2 hb.2) (forall₂_join hf1 hl'.flip)
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | choice r e =>
      cases v with
      | choice a x =>
        cases w with
        | choice b y =>
          simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
          obtain ⟨alt1, hm1, hn1, hb1⟩ := hv
          obtain ⟨alt2, hm2, hn2, hb2⟩ := hw
          have he : alt1 = alt2 := by
            by_contra hne
            have : Std.Symm fun a b : Alt × Ty => TagsDisj (encTags E n sc a.2) (encTags E n sc b.2) :=
              ⟨fun _ _ h => tagsDisj_symm h⟩
            obtain ⟨ta, tb, hta, htb, hd⟩ := List.Pairwise.forall uv.1 hm1 hm2 hne
            exact hd _ (ber_encTags E p n _ _ _ _ _ hb1 hta) (ber_encTags E p n _ _ _ _ _ hb2 htb)
          subst he
          have hab : a = b := hn1.symm.trans hn2
          subst hab
          have h := IH hb1 hb2 (dv alt1 hm1 hn1) (dw alt1 hm1 hn2) (uv.2.1 alt1 hm1 hn1) (uw.2.1 alt1 hm1 hn2)
          obtain ⟨hmem, hty⟩ := altTys_mem hm1
          refine ⟨rfl, alt1.1, hmem, hn1, ?_⟩
          rcases hty with h2 | ⟨tg, k, h2⟩
          · rwa [h2] at h
          · rw [h2] at h; simp only [eqv] at h; exact eqv_mono E p n _ _ _ _ (uv.2.2 alt1.1 hmem hn1) h
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | bitString named =>
      cases v with
      | bits bs =>
        cases w with
        | bits bs2 =>
          simp only [ber] at hv hw; simp only [eqv]
          obtain ⟨b1, c1, e1⟩ := hv
          obtain ⟨b2, c2, e2⟩ := hw
          have h1 := decBits_complete p n true (univ 3) b1 nd e1
          rw [decBits_complete p n true (univ 3) b2 nd e2] at h1
          cases h1
          split
          · rename_i h0; simp only [h0, ↓reduceIte] at c1 c2; rw [← c1, ← c2]
          · rename_i h0; simp only [h0, ↓reduceIte] at c1 c2
            split at c1
            · rename_i hr; simp only [hr, ↓reduceIte] at c2; rw [← c1, ← c2]
            · rename_i hr; simp only [hr] at c2; rw [← c1, ← c2]
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | real =>
      cases v with
      | real r1 =>
        cases w with
        | real r2 =>
          simp only [ber] at hv hw; simp only [Decodable] at dv dw
          obtain ⟨f1, c1, rfl, h1⟩ := hv
          obtain ⟨f2, c2, he, h2⟩ := hw
          simp only [Node.prim.injEq] at he
          rw [← he.2.2] at h2
          have := decReal_complete h1 dv
          rw [decReal_complete h2 dw] at this
          cases this
          simp [eqv]
        | _ => simp [ber, timeKind?] at hw
      | _ => simp [ber, timeKind?] at hv
    | objectDescriptor =>
      simp only [ber] at hv hw; simp only [UnambV] at uv uw
      obtain ⟨o1, s1, e1⟩ := hv
      obtain ⟨o2, s2, e2⟩ := hw
      have h1 := decOctets_complete p n (univ 7) o1 nd e1
      rw [decOctets_complete p n (univ 7) o2 nd e2] at h1
      cases h1
      have h3 := decString_complete s1 uv
      rw [decString_complete s2 uw] at h3
      cases h3
      simp [eqv]
    | embeddedPdv =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      have h := IH hv hw dv dw uv.1 uw.1
      simp only [eqv] at h
      exact eqv_mono E p n _ _ _ _ uv.2 h
    | characterString =>
      simp only [ber] at hv hw; simp only [Decodable] at dv dw; simp only [UnambV] at uv uw; simp only [eqv]
      have h := IH hv hw dv dw uv.1 uw.1
      simp only [eqv] at h
      exact eqv_mono E p n _ _ _ _ uv.2 h
    | openType => simp [UnambV] at uv
    | instanceOf cls => simp [UnambV] at uv
    | external => simp [UnambV] at uv
    | oidIri => simp [Decodable] at dv
    | relativeOidIri => simp [Decodable] at dv
    | time => simp [Decodable] at dv
    | date => simp [Decodable] at dv
    | timeOfDay => simp [Decodable] at dv
    | dateTime => simp [Decodable] at dv
    | duration => simp [Decodable] at dv
    | _ => simp [eqIsEq] at hq

/-- **X.690 is unambiguous, on octets**: two values with encodings (length forms the profile
allows, no primitive UNIVERSAL 0) laid out as the same octets are the same abstract value. The
octets are one tree (`parse_octets_self`), and `ber_unambiguous` applies. -/
theorem octets_unambiguous {E : Env} {p : Profile} {n : Nat} {sc : Scope} {t : Ty} {v w : Val} {nd nd' : Node}
    (hv : ber E p n sc t v nd) (hw : ber E p n sc t w nd') (hl : nd.LenOk p) (hl' : nd'.LenOk p)
    (hn : nd.NoEoc) (hn' : nd'.NoEoc) (ho : nd.octets = nd'.octets)
    (dv : Decodable E p n sc t v) (dw : Decodable E p n sc t w) (uv : UnambV E p n sc t v) (uw : UnambV E p n sc t w) :
    eqv E (n + 1) sc t v w := by
  have h1 := (parse_octets_self hl hn).1
  have h2 := (parse_octets_self hl' hn').1
  rw [ho, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  rw [h1.1] at hw
  exact ber_unambiguous E p n sc t v w nd hv hw dv dw uv uw

end Asn1.X690
