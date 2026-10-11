import Asn1.X680.Validity

/-! Which subtype notations apply to which types (X.680 51.1, Table 11, Table 12), and inner
subtyping through associated types (21.5, 36.5). -/

open Asn1.X680

def M : Module := { name := "M", header := ⟨.explicit, false⟩ }
def H0 : ContentsHook := fun _ _ _ _ _ => True
def sc : Scope := .ofModule M

def cRoot (s : ElemSet) : Constraint := .mk s false none
def rng (a b : Val) : ElemSet := .elem (.range (.val a) false (.val b) false)
def ch (c : Char) : Val := .chars [c.toNat]

attribute [local simp] ConsOk ESetOk ElemOk builtin rowOf Row.allows Elem.kind cRoot rng RefMaps

/-- `INTEGER (1..10)` -/
example (k : Nat) : ConsOk [M] H0 (k + 5) sc (.integer []) false (cRoot (rng (.int 1) (.int 10))) := by
  simp [EvalBound, evalVal, sem, VSet.plain]

/-- `INTEGER (SIZE (1..4))`: Table 11 has no size constraint for Integer. -/
example (k : Nat) :
    ¬ ConsOk [M] H0 (k + 7) sc (.integer []) false (cRoot (.elem (.size (cRoot (rng (.int 1) (.int 4)))))) := by
  simp

/-- `IA5String ("a".."z")`: a value range is allowed only within a permitted alphabet (note a)). -/
example (k : Nat) : ¬ ConsOk [M] H0 (k + 4) sc (.restricted .ia5) false (cRoot (rng (ch 'a') (ch 'z'))) := by
  simp

/-- `IA5String (FROM ("a".."z"))` -/
example (k : Nat) :
    ConsOk [M] H0 (k + 8) sc (.restricted .ia5) false (cRoot (.elem (.from_ (cRoot (rng (ch 'a') (ch 'z')))))) := by
  simp [StrType.knownOrder, Constraint.isSubtype, EvalBound, evalVal, ch, SingleChar]
  simp only [sem, restrictedVSet, charsVSet, VSet.plain, StrType.isRegister]
  rintro w ⟨cs, rfl, hcs⟩ -
  exact ⟨cs, rfl, hcs⟩

/-- `GeneralString (FROM ("a".."z"))`: GeneralString's characters have no canonical order. -/
example (k : Nat) :
    ¬ ConsOk [M] H0 (k + 7) sc (.restricted .general) false (cRoot (.elem (.from_ (cRoot (rng (ch 'a') (ch 'z')))))) := by
  simp [StrType.knownOrder]

/-- `TIME (SETTINGS "Basic=Date Date=YMD")` -/
example (k : Nat) :
    ConsOk [M] H0 (k + 4) sc .time false (cRoot (.elem (.settings [("Basic", "Date"), ("Date", "YMD")]))) := by
  simp; decide

/-- `TIME (SETTINGS "Basic=Date Time=HMS")`: Table 13 prohibits Time with Basic=Date. -/
example (k : Nat) :
    ¬ ConsOk [M] H0 (k + 4) sc .time false (cRoot (.elem (.settings [("Basic", "Date"), ("Time", "HMS")]))) := by
  simp; decide

/-- `BOOLEAN (INTEGER)`: 51.3.2, a contained subtype is derived from the parent's built-in type. -/
example (k : Nat) : ¬ ConsOk [M] H0 (k + 4) sc .boolean false (cRoot (.elem (.contained (.integer []) false))) := by
  simp

/-! ## REAL's associated type (21.5) -/

-- 1.5 in base 10 is 15 × 10^−1, and also 150 × 10^−2
example : (RealVal.num .ten (3 / 2)).Denotes
    (.seq [("mantissa", .int 15), ("base", .int 10), ("exponent", .int (-1))]) :=
  ⟨15, -1, by decide, by norm_num, rfl⟩
example : (RealVal.num .ten (3 / 2)).Denotes
    (.seq [("mantissa", .int 150), ("base", .int 10), ("exponent", .int (-2))]) :=
  ⟨150, -2, by decide, by norm_num, rfl⟩
-- 21.5 NOTE 2: zero is not a value of the associated type
example (x : Val) : ¬ RealVal.plusZero.Denotes x := fun h => h

/-- 21.5 NOTE 2: `REAL (WITH COMPONENTS { ..., base (10) })` selects the base 10 values. Here `S`
stands for the inner constraint's values. -/
def base10 : ESet := .fixed fun x => ∃ m e, x = .seq [("mantissa", .int m), ("base", .int 10), ("exponent", .int e)]

example : (ESet.byReal (fun _ => True) base10).r (.real (.num .ten (3 / 2))) :=
  ⟨trivial, _, rfl, _, ⟨15, -1, by decide, by norm_num, rfl⟩, 15, -1, rfl⟩

example : ¬ (ESet.byReal (fun _ => True) base10).r (.real (.num .two (3 / 2))) := by
  rintro ⟨-, r, hr, x, hd, m', e', h⟩
  cases hr
  obtain ⟨m, e, -, -, rfl⟩ := hd
  simp at h

/-! ## The endpoints of ranges (51.4, 51.11–51.13) -/

/-- 51.4.2: `INTEGER (1..3)` constrained by `(2..5)`: 4 and 5 are not in the parent's root. -/
example (k : Nat) :
    ¬ ConsOk [M] H0 (k + 9) sc (.constrained (.integer []) (cRoot (rng (.int 1) (.int 3)))) false
      (cRoot (rng (.int 2) (.int 5))) := by
  simp [EvalBound, evalVal]
  refine ⟨.int 4, ?_, ?_, ?_⟩ <;> simp [sem, cons, eset, elem, VSet.keepExt, structExt, builtin, EvalBound, evalVal, VSet.plain, VSet.ofSpecs,
    ESet.fixed, RangeHas, InRange, Val.le]

def tb (s : String) : Bound := match Notation.parse s.toList with
  | some t => .val (.time t)
  | none => .min

-- 51.11.4 EXAMPLE: the same element (seconds) to the same accuracy, identical above it
#guard timeRangeOk (tb "PT2M0.000S") (tb "PT2M59.000S")
-- 51.11.3: different accuracies, or different above the least significant element
#guard !timeRangeOk (tb "PT2M0.000S") (tb "PT2M59.00S")
#guard !timeRangeOk (tb "PT2M0.000S") (tb "PT3M59.000S")
#guard !timeRangeOk (tb "PT2M0S") (tb "PT59S")
-- 51.12.4 NOTE: TIME ("00:00".."09:00"), TIME ("21:00".."24:00")
#guard timeRangeOk (tb "00:00") (tb "09:00") && timeRangeOk (tb "21:00") (tb "24:00")
-- 51.12.3: identical settings except Midnight; 51.12.4: the same time difference
#guard !timeRangeOk (tb "00:00") (tb "09:00:00")
#guard !timeRangeOk (tb "00:00Z") (tb "09:00")
#guard !timeRangeOk (tb "00:00+01") (tb "09:00+02")
-- 51.13.2: integers
#guard timeRangeOk (.val (.int 1)) .max
-- a duration against a time point is no range at all
#guard !timeRangeOk (tb "PT2M") (tb "09:00")

/-! ## Inner subtyping (51.8.6, 51.8.10) -/

def ab : Ty := .choice [.mk "a" .boolean, .mk "b" .null] none
def ob : Ty := .sequence [.mk "a" .boolean .optional, .mk "b" .null .mandatory] none []

/-- 51.8.10.2: at most one PRESENT in a choice. -/
example (k : Nat) : ¬ PresenceOk [M] (k + 1) sc ab [("a", none, .present), ("b", none, .present)] := by
  simp [PresenceOk, builtin, ab, PresenceC.isPresent, PresenceC.isOptional]
example (k : Nat) : PresenceOk [M] (k + 1) sc ab [("a", none, .present), ("b", none, .absent)] := by
  simp [PresenceOk, builtin, ab, PresenceC.isPresent, PresenceC.isOptional]

/-- 51.8.10.1: ABSENT only on an OPTIONAL component; 51.8.6: in order. -/
example (k : Nat) : PresenceOk [M] (k + 4) sc ob [("a", none, .absent)] := by
  simp [PresenceOk, builtin, ob, entries, expand, PresenceC.isEmpty]
example (k : Nat) : ¬ PresenceOk [M] (k + 4) sc ob [("b", none, .absent)] := by
  simp [PresenceOk, builtin, ob, entries, expand, PresenceC.isEmpty]
example : ¬ PresenceOk [M] 4 sc ob [("b", none, .unspecified), ("a", none, .unspecified)] := by
  simp only [PresenceOk, builtin, ob, entries, expand]
  exact fun h => absurd h.1 (by decide)
