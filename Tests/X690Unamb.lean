import Asn1.X690.Unamb
import Tests.X690

/-! `ber_unambiguous` applies to real schemas: its hypotheses hold for X.690's 8.9.3 example
(`SEQUENCE {name IA5String, ok BOOLEAN}`, `{name "Smith", ok TRUE}`), so any value with the same
encoding is that value. -/

open Asn1 Asn1.X690 Asn1.X680

theorem smith_compTys : compTys [expl] 3 (.ofModule expl) [.mk "name" (.restricted .ia5) .mandatory,
      .mk "ok" .boolean .mandatory] none [] =
    [(⟨.ofModule expl, "name", .restricted .ia5, .mandatory, none, false⟩, .restricted .ia5),
     (⟨.ofModule expl, "ok", .boolean, .mandatory, none, false⟩, .boolean)] := by rfl

theorem smith_unambV : UnambV [expl] .der 4 (.ofModule expl) seqTy smithVal := by
  simp only [seqTy, smithVal, UnambV, CompsU, smith_compTys]
  refine ⟨⟨by decide, ?_, ?_⟩, ?_⟩
  · intro en hen hma
    simp [entries, expand] at hen
    rcases hen with rfl | rfl <;> simp [str]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> refine ⟨by simp, ?_⟩ <;> intro x hx <;>
      simp only [List.lookup] at hx <;> simp_all [UnambV]
  · simp [SeqTagsOk, untilMust, Entry.mayAbsent, Presence.isMandatory]

theorem smith_decodable : Decodable [expl] .der 4 (.ofModule expl) seqTy smithVal := by
  simp only [seqTy, smithVal, Decodable, CompsDec, smith_compTys]
  refine ⟨by decide, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> refine ⟨fun x hx => ?_, fun x hx => by simp [IsDefault] at hx⟩ <;>
    simp only [List.lookup] at hx <;> simp_all [Decodable, DefaultDec, StrBound, str]

/-- Every value with the 8.9.3 encoding (and the conditions) is `{name "Smith", ok TRUE}`. -/
example (w : Val) (hw : ber [expl] .der 4 (.ofModule expl) seqTy w smithNode)
    (dw : Decodable [expl] .der 4 (.ofModule expl) seqTy w) (uw : UnambV [expl] .der 4 (.ofModule expl) seqTy w)
    (hv : ber [expl] .der 4 (.ofModule expl) seqTy smithVal smithNode) :
    eqv [expl] 5 (.ofModule expl) seqTy smithVal w :=
  ber_unambiguous _ _ _ _ _ _ _ _ hv hw smith_decodable dw smith_unambV uw
