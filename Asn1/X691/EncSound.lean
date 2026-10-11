import Asn1.X691.Enc
import Asn1.X691.DecodeSound
import Asn1.X691.DecCompleteStruct

/-!
# The PER encoder is sound

`penc_sound`: what `penc` returns, `per` relates to the value; `encode_sound`: the octets `encode`
returns are the complete encoding (11.1) of a field-list `per` relates to the value. Each case of
`pencB` builds the field-list `perB`'s case names, so the proof is one lemma per case; the leaf
cases reuse the decoder's (`int_ok`, `bits_ok`, `km_ok`, …).
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (except_bind_ok mapM_ok valKeyEq)

/-! ## Plumbing -/

theorem eqLitB_spec : ∀ (x y : Val), eqLitB x y = true → x = y := by
  intro x y h
  unfold eqLitB at h
  split at h <;> first
    | rfl
    | (simp only [beq_iff_eq] at h; subst h; rfl)
    | (revert h; unfold valKeyEq; split <;> simp_all)

theorem ok_of_ite_error {α : Type} {c : Bool} {m : String} {k : Except String α} {a : α}
    (h : (if c = true then Except.error m else k) = .ok a) : c = false ∧ k = .ok a := by
  cases c <;> simp_all

theorem forall₂_of_mapM {α β : Type} {f : α → Except String β} {P : α → β → Prop}
    (hf : ∀ a b, f a = .ok b → P a b) {l : List α} {l' : List β} (h : l.mapM f = .ok l') :
    List.Forall₂ P l l' :=
  by
    have h2 := mapM_ok h
    clear h
    induction h2 with
    | nil => exact .nil
    | cons hab _ ih => exact .cons (hf _ _ hab) ih

/-! ## DEFAULT components and SEQUENCE (19) -/

theorem compOutE_sound {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → Except String FieldList}
    {R : Scope → Ty → Val → FieldList → Prop} (hrec : ∀ sc t x fl, rec sc t x = .ok fl → R sc t x fl)
    {root : Bool} {cs : List (String × Val)} {en : Entry} {out : Option FieldList}
    (h : compOutE E v n rec root cs en = .ok out) : CompOut E v n R root cs en out := by
  unfold compOutE at h
  unfold CompOut
  split at h
  · rename_i hp; rw [hp]
    split at h
    · rename_i x hx; rw [hx]
      obtain ⟨f, hf, h⟩ := except_bind_ok h
      cases h; exact ⟨f, hrec _ _ _ _ hf, rfl⟩
    · rename_i hx; rw [hx]
      split at h
      · cases h
      · cases h; exact ⟨by simp_all, rfl⟩
  · rename_i hp; rw [hp]
    split at h
    · rename_i x hx; rw [hx]
      obtain ⟨f, hf, h⟩ := except_bind_ok h
      cases h; exact ⟨f, hrec _ _ _ _ hf, rfl⟩
    · rename_i hx; rw [hx]; cases h; rfl
  · rename_i d hp; rw [hp]
    split at h
    · cases h
    · rename_i dv hdv
      refine ⟨dv, evalValC_spec E n en.scope d dv hdv, ?_⟩
      split at h
      · rename_i hx
        rw [hx]
        split at h
        · rename_i hr
          cases h
          dsimp only
          exact ⟨fun _ => Or.inl rfl, fun hne => absurd (eqvReflB_spec E n _ _ _ hr) hne⟩
        · cases h
      · rename_i x hx
        rw [hx]
        simp only [Option.getD_some]
        split at h
        · rename_i hq
          simp only [Bool.and_eq_true] at hq
          cases h
          have he : eqv E n en.scope en.ty x dv := by
            rw [eqLitB_spec _ _ hq.1]; exact eqvReflB_spec E n _ _ _ hq.2
          exact ⟨fun _ => Or.inl rfl, fun hne => absurd he hne⟩
        · split at h
          · rename_i hc
            obtain ⟨f, hf, h⟩ := except_bind_ok h
            cases h
            have henc : ∃ fl, R en.scope en.ty x fl ∧ some f = some fl := ⟨f, hrec _ _ _ _ hf, rfl⟩
            refine ⟨fun he => ?_, fun _ => henc⟩
            simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
            rcases hc with (hc | hc) | ⟨hcan, hcomp⟩
            · exact (X690.notDefaultB_spec hc (by
                unfold X690.IsDefault; rw [hp]; exact ⟨dv, evalValC_spec E n en.scope d dv hdv, he⟩)).elim
            · exact absurd he (neqvB_spec E n _ _ _ _ hc)
            · exact Or.inr ⟨hcan, isCompositeB_spec hcomp, henc⟩
          · cases h

theorem groupE_sound {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → Except String FieldList}
    {R : Scope → Ty → Val → FieldList → Prop} (hrec : ∀ sc t x fl, rec sc t x = .ok fl → R sc t x fl)
    {cs : List (String × Val)} {es : List Entry} {out : Option FieldList}
    (h : groupE E v n rec cs es = .ok out) : GroupOut E v n R cs es out := by
  unfold groupE at h
  obtain ⟨outs, ho, h⟩ := except_bind_ok h
  refine ⟨outs, forall₂_of_mapM (P := CompOut E v n R false cs) (fun _ _ hab => compOutE_sound hrec hab) ho, ?_⟩
  split at h
  · rename_i hn; cases h; simp [hn]
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split at h
    · rename_i hm
      cases h
      refine ⟨fun p hp hmand => ?_, rfl⟩
      have := List.all_eq_true.mp hm p hp
      simp_all
    · cases h

theorem seqE_sound {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → Except String FieldList}
    {R : Scope → Ty → Val → FieldList → Prop} (hrec : ∀ sc t x fl, rec sc t x = .ok fl → R sc t x fl)
    {isExt : Bool} {rootEs : List Entry} {adds : List (List Entry × Bool)} {cs : List (String × Val)}
    {fl : FieldList} (h : seqE E v n rec isExt rootEs adds cs = .ok fl) :
    SeqFields E v n R isExt rootEs adds cs fl := by
  unfold seqE at h
  cases hall : (cs.all fun p => ((rootEs ++ adds.flatMap (·.1)).map (·.name)).contains p.1)
  · rw [hall] at h; cases h
  rw [hall] at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨rootOuts, hro, h⟩ := except_bind_ok h
  obtain ⟨addOuts, hao, h⟩ := except_bind_ok h
  refine ⟨fun p hp => ?_, rootOuts, addOuts,
    forall₂_of_mapM (P := CompOut E v n R true cs) (fun _ _ hab => compOutE_sound hrec hab) hro,
    forall₂_of_mapM (fun a o hab => ?_) hao, ?_⟩
  · have := List.all_eq_true.mp hall p hp
    simpa using this
  · split
    · rename_i hg; rw [if_pos hg] at hab; exact groupE_sound hrec hab
    · rename_i hg; rw [if_neg hg] at hab
      split at hab
      · rename_i e he; exact ⟨e, he, compOutE_sound hrec hab⟩
      · cases hab
  · dsimp only at h ⊢
    split at h
    · rename_i hx; cases h; simp only [hx, ↓reduceIte]; rfl
    · rename_i hx
      split at h
      · cases h
      · rename_i hany
        cases h; simp only [hx, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by simpa using hany, trivial⟩

/-! ## The cases of `pencB` -/

theorem pure_ok {α : Type} {a b : α} (h : (pure a : Except String α) = .ok b) : a = b := by
  simpa [pure, Except.pure] using h

theorem namedSentE_spec {S : CSet} {P : PSet Nat} (hD : DenN S P) {bs sent : Bits}
    (h : namedSentE S bs = .ok sent) : NamedBitsSent P bs sent := by
  unfold namedSentE at h
  dsimp only at h
  split at h
  · rename_i k hk
    cases h
    have hl := (Ivs.least?_spec _ _).mp hk
    have hm := hl.1
    simp only [Set.mem_setOf_eq, Ivs.mem_inter] at hm
    rw [Bool.and_eq_true] at hm
    have hge : ((stripTrailingZeros bs).length : Int) ≤ k := by
      have := hm.2; simp [Ivs.mem, Ivs.memI] at this; omega
    refine ⟨k.toNat, rfl, by omega, (hD.2.1 k.toNat).2 (by rw [show ((k.toNat : Nat) : Int) = k by omega]; exact hm.1), ?_⟩
    intro k' h1 h2
    have := hl.2 (show (k' : Int) ∈ {x | (S.a.inter [(some ((stripTrailingZeros bs).length : Int), none)]).mem x = true} by
      simp only [Set.mem_setOf_eq, Ivs.mem_inter, Bool.and_eq_true]
      refine ⟨(hD.2.1 k').1 h2, ?_⟩
      simp [Ivs.mem, Ivs.memI]; omega)
    omega
  · cases h

theorem pairs_spec {f : Val → Except String FieldList} :
    ∀ {vs : List Val} {pairs : List (Val × FieldList)},
      vs.mapM (fun w => do pure (w, ← f w)) = .ok pairs →
      pairs.map (·.1) = vs ∧ ∀ p ∈ pairs, f p.1 = .ok p.2 := by
  intro vs pairs h
  have h2 := mapM_ok h
  clear h
  induction h2 with
  | nil => simp
  | cons hab _ ih =>
    rename_i w p _ _
    obtain ⟨g, hg, hp⟩ := except_bind_ok hab
    have := pure_ok hp; subst this
    refine ⟨by simp [ih.1], ?_⟩
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hg
    · exact ih.2 q hq

theorem idx_name {S : List (Alt × Option (List Tag))} {nm : String} {k : Nat} {a : Alt} {tg : Option (List Tag)}
    (hk : (S.map (·.1.name)).idxOf? nm = some k) (ha : S[k]? = some (a, tg)) : a.name = nm := by
  rw [List.idxOf?_eq_some_iff] at hk
  obtain ⟨hl, h1, _⟩ := hk
  have : (S.map (·.1.name))[k]? = some a.name := by simp [ha]
  rw [List.getElem?_eq_getElem hl, h1] at this
  cases this; rfl

theorem strOctetsE_spec {k : StrType} {x : Val} {os : Octets} (h : strOctetsE k x = .ok os) (p : X690.Profile) :
    X690.StringOctets p k x os := by
  unfold strOctetsE at h
  split at h
  · rename_i cs
    unfold X690.StringOctets
    split at h <;> (try cases h)
    all_goals first
      | (split at h
         · rename_i hall; cases h; exact ⟨rfl, by simpa using hall⟩
         · cases h)
      | rfl
  · cases h

theorem firstOkE_spec {α β : Type} {f : α → Except String β} {err : String} :
    ∀ {xs : List α} {b : β}, firstOkE f err xs = .ok b → ∃ x, f x = .ok b
  | [], _, h => by cases h
  | x :: xs, b, h => by
    unfold firstOkE at h
    split at h
    · rename_i b' hb; cases h; exact ⟨x, hb⟩
    · exact firstOkE_spec h

theorem pencB_sound {E : Env} {v : Variant} {n : Nat} {rec : Scope → Ty → Val → Except String FieldList}
    (hrec : ∀ sc t x fl, rec sc t x = .ok fl → per E v n sc t x fl)
    {sc : Scope} {t : Ty} {sc' : Scope} {bt : Ty} {x : Val} {fl : FieldList}
    (h : pencB E v n rec sc t sc' bt x = .ok fl) : perB E v n (per E v n) sc t sc' bt x fl := by
  unfold pencB at h
  split at h
  · cases h; simp only [perB]
  · split at h
    · rename_i C hC
      simp only [bind, Except.bind] at h
      obtain ⟨h1, h⟩ := ok_of_ite_error h
      obtain ⟨h2, h⟩ := ok_of_ite_error h
      cases pure_ok h
      exact int_ok hC (by simpa using h1) (fun hx => by simp_all)
    · cases h
  · simp only [perB, EnumFields]
    dsimp only at h
    split at h
    · rename_i k hk
      cases pure_ok h
      split
      · exact Or.inl ⟨k, hk, rfl⟩
      · exact ⟨k, hk, rfl⟩
    · rename_i hk
      split at h
      · rename_i hx
        split at h
        · rename_i k hk2
          cases pure_ok h
          rw [if_pos hx]; exact Or.inr ⟨k, hk2, rfl⟩
        · cases h
      · cases h
  -- 15
  · split at h
    · rename_i os hos
      split at h
      · rename_i r' hr
        split at h
        · rename_i he; subst he; cases pure_ok h
          simp only [perB]; exact ⟨os, X690.decReal_spec hr, rfl⟩
        · cases h
      · cases h
    · cases h
  -- 16
  · rename_i named bs
    split at h
    · rename_i S hS
      have hD := pSizeC_sound hS
      simp only [bind, Except.bind] at h
      split at h
      · rename_i hn
        obtain ⟨h1, h⟩ := ok_of_ite_error h
        obtain ⟨h2, h⟩ := ok_of_ite_error h
        cases pure_ok h
        simp only [perB]
        refine ⟨bs, by simp only [hn, ↓reduceIte], ?_⟩
        simp only [BitsFields]; rw [lbOf_eq hD, ubOf_eq hD]
        exact sized_ok hD _ _ (by simpa using h1) (fun hx => by simp_all)
      · rename_i hn
        split at h
        · cases h
        · rename_i sent hs
          obtain ⟨h1, h⟩ := ok_of_ite_error h
          obtain ⟨h2, h⟩ := ok_of_ite_error h
          cases pure_ok h
          simp only [perB]
          refine ⟨sent, by simp only [hn, ↓reduceIte]; exact namedSentE_spec hD hs, ?_⟩
          simp only [BitsFields]; rw [lbOf_eq hD, ubOf_eq hD]
          exact sized_ok hD _ _ (by simpa using h1) (fun hx => by simp_all)
    · cases h
  -- 17
  · rename_i os
    split at h
    · rename_i S hS
      simp only [bind, Except.bind] at h
      obtain ⟨h1, h⟩ := ok_of_ite_error h
      obtain ⟨h2, h⟩ := ok_of_ite_error h
      cases pure_ok h
      exact octets_ok hS (by simpa using h1) (fun hx => by simp_all)
    · cases h
  -- 18
  · cases pure_ok h; simp only [perB]
  -- 19, 21
  · exact seqE_sound hrec h
  · exact seqE_sound hrec h
  -- 20
  · rename_i el vs
    split at h
    · rename_i S hS
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i fls hfls
        obtain ⟨h1, h⟩ := ok_of_ite_error h
        obtain ⟨h2, h⟩ := ok_of_ite_error h
        cases pure_ok h
        simp only [perB]
        exact ⟨fls, forall₂_of_mapM (P := per E v n sc' el) (fun a b hab => hrec _ _ _ _ hab) hfls,
          seqOfFields_ok (pSizeC_sound hS) (by simpa using h1) (fun hx => by simp_all)⟩
    · cases h
  -- 22
  · rename_i el vs
    split at h
    · rename_i S hS
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i pairs hpairs
        obtain ⟨h0, h⟩ := ok_of_ite_error h
        obtain ⟨h1, h⟩ := ok_of_ite_error h
        obtain ⟨h2, h⟩ := ok_of_ite_error h
        cases pure_ok h
        obtain ⟨hfst, hall⟩ := pairs_spec hpairs
        have hperm : (if v.canonical = true then
            pairs.mergeSort (fun a b => bitsLe (setOfKey v a.2) (setOfKey v b.2)) else pairs).Perm pairs := by
          split
          · exact List.mergeSort_perm _ _
          · exact List.Perm.refl _
        generalize (if v.canonical = true then
            pairs.mergeSort (fun a b => bitsLe (setOfKey v a.2) (setOfKey v b.2)) else pairs) = ps at hperm h0 h1 h2 ⊢
        simp only [perB]
        refine ⟨ps.map (·.1), ps.map (·.2), ?_, ?_, ?_, ?_⟩
        · rw [← hfst]; exact hperm.map _
        · exact forall₂_map_of (fun p hp => hrec _ _ _ _ (hall p (hperm.subset hp)))
        · intro hc; rw [hc] at h0; simpa using h0
        · exact seqOfFields_ok (pSizeC_sound hS) (by simpa using h1) (fun hx => by rw [hx] at h2; simpa using h2)
    · cases h
  -- 23
  · rename_i root ext nm y
    dsimp only at h
    split at h
    · rename_i k hk
      split at h
      · rename_i a tg hak
        obtain ⟨afl, hafl, h⟩ := except_bind_ok h
        cases pure_ok h
        have hname := idx_name hk hak
        subst hname
        simp only [perB]
        exact choice_root hak (by simpa using hk) (hrec _ _ _ _ hafl) rfl
      · cases h
    · rename_i hk0
      split at h
      · rename_i k hk
        split at h
        · rename_i a tg hak
          split at h
          · rename_i hx
            obtain ⟨afl, hafl, h⟩ := except_bind_ok h
            cases pure_ok h
            have hname := idx_name hk hak
            subst hname
            simp only [perB]
            exact choice_add hak (by simpa using hk) (hrec _ _ _ _ hafl) hx
          · cases h
        · cases h
      · cases h
  -- 24–27
  · cases pure_ok h; simp only [perB]
  · cases pure_ok h; simp only [perB]
  · cases pure_ok h; simp only [perB]
  · cases pure_ok h; simp only [perB]
  -- 30
  · rename_i k
    split at h
    · rename_i hk
      split at h
      · rename_i cs
        split at h
        · rename_i S A hS
          dsimp only at h
          obtain ⟨h0, h⟩ := ok_of_ite_error h
          obtain ⟨h1, h⟩ := ok_of_ite_error h
          obtain ⟨h2, h⟩ := ok_of_ite_error h
          cases pure_ok h
          exact km_ok hk hS (fun c hc => by simp at h0; exact h0 c hc)
            (by simpa using h1) (fun hx => by rw [hx] at h2; simpa using h2)
        · cases h
      · cases h
    · rename_i hk
      obtain ⟨os, hos, h⟩ := except_bind_ok h
      cases pure_ok h
      simp only [perB, hk, Bool.false_eq_true, ↓reduceIte]
      exact ⟨os, strOctetsE_spec hos _, rfl⟩
  -- 10.6.5
  · rename_i cs
    dsimp only at h
    obtain ⟨h0, h⟩ := ok_of_ite_error h
    simp only [↓reduceIte] at h
    obtain ⟨h1, h⟩ := ok_of_ite_error h
    cases pure_ok h
    simp only [perB]
    exact time_ok (X690.genTimeCanonB_spec (by simpa using h1)) (fun c hc => by simp at h0; exact h0 c hc)
  · rename_i cs
    dsimp only at h
    obtain ⟨h0, h⟩ := ok_of_ite_error h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨h1, h⟩ := ok_of_ite_error h
    cases pure_ok h
    simp only [perB]
    exact time_ok (X690.utcTimeCanonB_spec (by simpa using h1)) (fun c hc => by simp at h0; exact h0 c hc)
  -- 11.2
  · rename_i ty y
    obtain ⟨afl, hafl, h⟩ := except_bind_ok h
    cases pure_ok h
    simp only [perB]
    obtain ⟨sc'', hsc⟩ := firstOkE_spec hafl
    exact ⟨sc'', afl, hrec _ _ _ _ hsc, rfl⟩
  · cases h

/-! ## The encoder -/

theorem penc_sound (E : Env) (v : Variant) : ∀ (n : Nat) (sc : Scope) (t : Ty) (x : Val) (fl : FieldList),
    penc E v n sc t x = .ok fl → per E v n sc t x fl
  | 0, _, _, _, _, h => by cases h
  | n + 1, sc, t, x, fl, h => by
    unfold penc at h
    unfold per
    split at h
    · rename_i sc' bt hb
      rw [hb]
      exact pencB_sound (penc_sound E v n) h
    · cases h

theorem encode_sound {E : Env} {v : Variant} {fuel : Nat} {m : Module} {t : Ty} {x : Val} {os : Octets}
    (h : encode E v fuel m t x = .ok os) :
    ∃ fl, per E v fuel (.ofModule m) t x fl ∧ bitsOf os = complete v .other fl := by
  unfold encode at h
  obtain ⟨fl, hfl, h⟩ := except_bind_ok h
  cases pure_ok h
  refine ⟨fl, penc_sound E v fuel _ t x fl hfl, ?_⟩
  rw [completeFast_eq]
  obtain ⟨_, _, h8⟩ := complete_other v fl
  exact bitsOf_bitsToOctets _ h8

end Asn1.X691
