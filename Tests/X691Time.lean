import Asn1.X691.Time
import Asn1.Parse.Values
import Asn1.Parse.Report
import Asn1.X680.Checker

/-! X.691 32: the encoding types against X.691's own ASN.1 text, Table 2's rows, and the values of
the encoding types. -/

open Asn1 Asn1.X680 Asn1.X691 Asn1.Parse

/-! ## The encoding types are X.691's text -/

mutual
  /-- The notation of the types X.691 32 uses, shown, to compare the terms with the parsed text. -/
  partial def showTy : Ty → String
    | .integer ns => s!"INTEGER{ns.length}"
    | .constrained t c => s!"({showTy t} ({showC c}))"
    | .sequence r e r2 => s!"SEQ\{{", ".intercalate (r.map showComp)}}{e.isSome}{r2.length}"
    | .choice r e => s!"CHOICE\{{", ".intercalate (r.map fun | .mk n t => n ++ " " ++ showTy t)}}{e.isSome}"
    | .enumerated r e => s!"ENUM{r}{e}"
    | .ref n => n
    | .paramRef mn n args =>
      s!"{mn}.{n}\{{", ".intercalate (args.map fun | .type t => showTy t | _ => "?arg")}}"
    | _ => "?ty"
  partial def showComp : Comp → String
    | .mk n t p => n ++ " " ++ showTy t ++
        (match p with | .mandatory => "" | .optional => " OPT" | .default_ _ => " DEF")
    | .componentsOf _ => "?co"
  partial def showC : Constraint → String
    | .mk r ext adds => s!"{showE r}{ext}{adds.map showE}"
    | _ => "?c"
  partial def showE : ElemSet → String
    | .elem (.range lo a hi b) => s!"{showB lo}{a}..{showB hi}{b}"
    | .union a b => s!"{showE a}|{showE b}"
    | _ => "?e"
  partial def showB : Bound → String
    | .min => "MIN" | .max => "MAX" | .val (.int i) => toString i | _ => "?b"
end

/-- X.691 32.2–32.11 as printed (`Tests/asn1/x691-time.asn`), read by the front end. -/
def parsed : Module :=
  match parseModules (include_str "asn1/x691-time.asn") with
  | .ok ms => ((readValues (resolveAll ms).1).1).headD { name := "NONE", header := ⟨.automatic, false⟩ }
  | .error _ => { name := "ERROR", header := ⟨.automatic, false⟩ }

#guard parsed.name = "X691-TIME-ENCODINGS"
#guard parsed.header.tagDefault = .automatic
-- the same type assignments, in the same order, each the same notation
#guard parsed.types.length = 38
#guard parsed.types.map (·.1) = timeEncTypes.map (·.1)
#guard parsed.types.all fun (n, t) =>
  (timeEncModule.lookup n).map showTy = some (showTy t) && !(showTy t).contains '?'
-- the same 20 parameterized assignments, dummies with no governor (they stand for types)
#guard parsed.params.length = 20 ∧ TimeEnc.paramTypes.length = 20
#guard parsed.params.all fun p => match p, TimeEnc.paramTypes.find? (·.name == p.name) with
  | .type _ ps b, some (.type _ ps' b') =>
    ps.map (·.name) == ps'.map (·.name) && ps.all (·.governor.isNone) && ps'.all (·.governor.isNone) &&
      showTy b == showTy b' && !(showTy b).contains '?'
  | _, _ => false

-- with the instantiations, every reference resolves and no validity rule is broken
#guard (report [timeEncModule]).unresolved.size = 0
#guard checkEnv [timeEncModule] 60 = []
#guard instances.length = 948
#guard timeEncModule.types.all fun (n, _) =>
  (builtin [timeEncModule] 30 (.ofModule timeEncModule) (.ref n)).isSome

/-! ## Table 2 -/

#guard rowTypeName 1 = "CENTURY-ENCODING" ∧ rowTypeName 14 = "ANY-YEAR-WEEK-DAY-ENCODING"
#guard rowTypeName 15 = "HOURS-ENCODING" ∧ rowTypeName 23 = "TIME-OF-DAY-AND-DIFF-ENCODING"
#guard rowTypeName 24 = "HOURS-AND-FRACTION-ENCODING"
#guard rowTypeName 32 = "TIME-OF-DAY-AND-DIFF-AND-FRACTION-ENCODING"
#guard (List.range' 1 53).all fun r => (rowTypeName r).length > 0

/-- A time of day in row `r` (15–32). -/
def todOf (r : Nat) : TimeOfDayV :=
  let k := r - 15
  let acc := (k % 9) / 3
  { hour := 10, minute := if 1 ≤ acc then some 30 else none, second := if 2 ≤ acc then some 15 else none,
    frac := if 9 ≤ k then [2, 5] else [],
    zone := match k % 3 with | 0 => .local_ | 1 => .utc | _ => .diff (-90) }

/-- A date in row `r` (1–14). -/
def dateOf (r : Nat) : DateV :=
  let y : Int := if r % 2 = 1 then 2020 else -5
  match (r - 1) / 2 with
  | 0 => .c (if r % 2 = 1 then 20 else -1)
  | 1 => .y y
  | 2 => .ym y 3
  | 3 => .ymd y 1 5
  | 4 => .yd y 100
  | 5 => .yw y 10
  | _ => .ywd y 10 3

def du : DurationV := { years := some 1, months := some 0, days := some 2, frac := [5] }

/-- A value in row `r`, with date row 7 and time row 21 where it has them. -/
def sample (r : Nat) : TimeV :=
  let pt (k : Nat) : PointV :=
    match k with
    | 0 => .date (dateOf 7)
    | 1 => .time (todOf 21)
    | _ => .dateTime (dateOf 7) (todOf 21)
  if r ≤ 14 then .point (.date (dateOf r))
  else if r ≤ 32 then .point (.time (todOf r))
  else if r = 33 then .point (pt 2)
  else if r ≤ 36 then .interval (.se (pt (r - 34)) (pt (r - 34)))
  else if r = 37 then .interval (.d du)
  else if r ≤ 40 then .interval (.sd (pt (r - 38)) du)
  else if r ≤ 43 then .interval (.de du (pt (r - 41)))
  else if r ≤ 46 then .recurring (some 5) (.se (pt (r - 44)) (pt (r - 44)))
  else if r = 47 then .recurring none (.d du)
  else if r ≤ 50 then .recurring (some 5) (.sd (pt (r - 48)) du)
  else .recurring (some 5) (.de du (pt (r - 51)))

-- the samples are values
#guard (List.range' 1 53).all fun r => (sample r).Wf
-- 32.11.1: each value matches exactly one row of Table 2, its main determining row
#guard (List.range' 1 53).all fun r => (List.range' 1 53).filter (rowMatches · (sample r)) == [r]
-- 32.11.2, 32.11.3: the date and time determining rows, where the main row has them
#guard (List.range' 1 53).all fun r =>
  rowsOf (sample r) == some ⟨r, if needsDate r then some 7 else none, if needsTime r then some 21 else none⟩
-- the Year settings: Basic and Proleptic years are odd rows, Negative and Ln even rows
#guard mainRow (.point (.date (.y 1000))) = some 3 ∧ mainRow (.point (.date (.y 12345))) = some 4
#guard mainRow (.point (.date (.c 100))) = some 2
#guard encName ⟨33, some 7, some 21⟩ = "DATE-TIME-ENCODING {DATE-ENCODING, TIME-OF-DAY-ENCODING}"
#guard encName ⟨44, some 3, none⟩ = "REC-START-END-DATE-INTERVAL-ENCODING {YEAR-ENCODING}"

/-! ### The defined time types (X.680 38.4) and some subtypes of TIME -/

/-- X.680 38.4.1: DATE's values have row 7. -/
theorem date_row : RowApplies (fun x => x.Wf ∧ x.satisfies dateSettings) ⟨7, none, none⟩ := by
  refine ⟨by decide, by decide, ?_, by simp [needsDate], by simp [needsTime], by simp [isFracRow]⟩
  rintro x ⟨-, h⟩
  rcases x with ⟨p⟩ | ⟨i⟩ | ⟨n, i⟩
  · rcases p with ⟨d⟩ | ⟨t⟩ | ⟨d, t⟩
    · cases d <;> simp_all [TimeV.satisfies, dateSettings, TimeV.props, PointV.props, DateV.props,
        rowMatches, table2, settingsMatch, PointV.basic, DateV.scale, SettingPat.accepts, dateScales]
    all_goals simp_all [TimeV.satisfies, dateSettings, TimeV.props, PointV.props, PointV.basic]
  all_goals simp_all [TimeV.satisfies, dateSettings, TimeV.props]

/-- X.680 38.4.2: TIME-OF-DAY's values have row 21. -/
theorem timeOfDay_row :
    RowApplies (fun x => x.Wf ∧ x.satisfies timeOfDaySettings) ⟨21, none, none⟩ := by
  refine ⟨by decide, by decide, ?_, by simp [needsDate], by simp [needsTime], by simp [isFracRow]⟩
  rintro x ⟨-, h⟩
  rcases x with ⟨p⟩ | ⟨i⟩ | ⟨n, i⟩
  · rcases p with ⟨d⟩ | ⟨t⟩ | ⟨d, t⟩
    · simp_all [TimeV.satisfies, timeOfDaySettings, TimeV.props, PointV.props, PointV.basic]
    · simp_all [TimeV.satisfies, timeOfDaySettings, TimeV.props, PointV.props, TimeOfDayV.props,
        rowMatches, table2, settingsMatch, PointV.basic, SettingPat.accepts, timeAccuracies,
        zoneSettings]
    · simp_all [TimeV.satisfies, timeOfDaySettings, TimeV.props, PointV.props, PointV.basic]
  all_goals simp_all [TimeV.satisfies, timeOfDaySettings, TimeV.props]

/-- X.680 38.4.4: DURATION's values have row 37. -/
theorem duration_row :
    RowApplies (fun x => x.Wf ∧ x.satisfies durationSettings) ⟨37, none, none⟩ := by
  refine ⟨by decide, by decide, ?_, by simp [needsDate], by simp [needsTime], by simp [isFracRow]⟩
  rintro x ⟨-, h⟩
  rcases x with ⟨p⟩ | ⟨i⟩ | ⟨n, i⟩
  · cases p <;> simp_all [TimeV.satisfies, durationSettings, TimeV.props, PointV.basic]
  · cases i <;> simp_all [TimeV.satisfies, durationSettings, TimeV.props, IntervalV.props, rowMatches,
      table2, intervalSettings, settingsMatch, SettingPat.accepts]
  · simp_all [TimeV.satisfies, durationSettings, TimeV.props]

theorem midnight_cases (t : TimeOfDayV) :
    t.midnight = [] ∨ t.midnight = ["Start"] ∨ t.midnight = ["End"] := by
  unfold TimeOfDayV.midnight; split_ifs <;> simp

theorem props_dateTime (d : DateV) (t : TimeOfDayV) (hs : d.scale = "YMD") (hy : d.year = "Basic")
    (ha : t.accuracy = "HMS") (hz : t.zone.setting = "L") :
    (TimeV.point (.dateTime d t)).props = [("Basic", "Date-Time"), ("Date", "YMD"), ("Year", "Basic"),
      ("Time", "HMS"), ("Local-or-UTC", "L")] ++ t.midnight.map (("Midnight", ·)) := by
  simp [TimeV.props, PointV.basic, PointV.props, DateV.props, TimeOfDayV.props, hs, hy, ha, hz]

/-- X.680 38.4.3: DATE-TIME's values have row 33, with date row 7 and time row 21. -/
theorem dateTime_row :
    RowApplies (fun x => x.Wf ∧ x.satisfies dateTimeSettings) ⟨33, some 7, some 21⟩ := by
  have pt : ∀ x : TimeV, x.satisfies dateTimeSettings = true →
      ∃ d t, x = .point (.dateTime d t) ∧ d.scale = "YMD" ∧ d.year = "Basic" ∧
        t.accuracy = "HMS" ∧ t.zone.setting = "L" := by
    intro x h
    rcases x with ⟨p⟩ | ⟨i⟩ | ⟨n, i⟩
    · rcases p with ⟨d⟩ | ⟨t⟩ | ⟨d, t⟩
      · simp_all [TimeV.satisfies, dateTimeSettings, TimeV.props, PointV.props, PointV.basic]
      · simp_all [TimeV.satisfies, dateTimeSettings, TimeV.props, PointV.props, PointV.basic]
      · simp_all [TimeV.satisfies, dateTimeSettings, TimeV.props, PointV.props, PointV.basic,
          DateV.props, TimeOfDayV.props]
    all_goals simp_all [TimeV.satisfies, dateTimeSettings, TimeV.props]
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨-, h⟩
    obtain ⟨d, t, rfl, -⟩ := pt x h
    simp [rowMatches, table2, settingsMatch, TimeV.props, PointV.basic, SettingPat.accepts]
  · refine ⟨7, by decide, rfl, ?_⟩
    rintro x ⟨-, h⟩
    obtain ⟨d, t, rfl, hs, hy, ha, hz⟩ := pt x h
    unfold dateRowOf additionalMatch
    rw [props_dateTime d t hs hy ha hz]
    rcases midnight_cases t with h | h | h <;> rw [h] <;> decide +kernel
  · refine ⟨21, rfl, ?_⟩
    rintro x ⟨-, h⟩
    obtain ⟨d, t, rfl, hs, hy, ha, hz⟩ := pt x h
    unfold timeRowOf additionalMatch
    rw [props_dateTime d t hs hy ha hz]
    rcases midnight_cases t with h | h | h <;> rw [h] <;> decide +kernel
  · simp [isFracRow]

def t1 : TimeV :=
  .point (.time { hour := 10, minute := some 0, second := some 0, frac := [1, 2, 3], zone := .utc })
def t2 : TimeV :=
  .point (.time { hour := 11, minute := some 0, second := some 0, frac := [5, 0, 0], zone := .utc })
def t3 : TimeV :=
  .point (.time { hour := 11, minute := some 0, second := some 0, frac := [5], zone := .utc })
def d1 : TimeV := .point (.date (.ymd 2020 1 5))

theorem not_row_d1_t1 : ∀ r ∈ List.range' 1 53, (rowMatches r d1 && rowMatches r t1) = false := by
  decide +kernel

theorem not_row_t1_t3 : ∀ r ∈ List.range' 1 53, (rowMatches r t1 && rowMatches r t3) = true →
    fracDigitsOf t1 ≠ fracDigitsOf t3 := by
  decide +kernel

/-- 32.1.2, NOTE 2 of 32.1.4: the unconstrained TIME type has no row; it is encoded as 32.11 says. -/
theorem time_mixed : ¬ ∃ c, RowApplies (fun x => x.Wf = true) c := by
  rintro ⟨c, h1, h2, h3, -⟩
  have := not_row_d1_t1 c.main (List.mem_range'_1.2 ⟨h1, by omega⟩)
  simp [h3 d1 (by decide +kernel), h3 t1 (by decide +kernel)] at this

/-- Times with three fraction digits, in UTC: row 31 (32.1.3: the same n). -/
theorem frac3_row : RowApplies (fun x => x = t1 ∨ x = t2) ⟨31, none, none⟩ := by
  refine ⟨by decide, by decide, ?_, by simp [needsDate], by simp [needsTime], ?_⟩
  · rintro x (rfl | rfl) <;> decide +kernel
  · intro _; exact ⟨3, by rintro x (rfl | rfl) <;> decide +kernel⟩

/-- 32.1.3: with fractions of one and three digits, rows 24 to 32 do not apply, and nothing else
does: 32.11. -/
theorem fracMixed : ¬ ∃ c, RowApplies (fun x => x = t1 ∨ x = t3) c := by
  rintro ⟨c, h1, h2, h3, -, -, h6⟩
  have a := h3 t1 (.inl rfl)
  have b := h3 t3 (.inr rfl)
  have hr : c.main = 31 := by
    have : ∀ r ∈ List.range' 1 53, rowMatches r t1 = true → r = 31 := by decide +kernel
    exact this _ (List.mem_range'_1.2 ⟨h1, by omega⟩) a
  obtain ⟨n, hn⟩ := h6 (by simp [hr, isFracRow])
  have := not_row_t1_t3 c.main (List.mem_range'_1.2 ⟨h1, by omega⟩) (by simp [a, b])
  exact this ((hn t1 (.inl rfl)).trans (hn t3 (.inr rfl)).symm)

/-- `TimeAs` for t1 under row 31, and for t3 under MIXED-ENCODING. -/
example : TimeAs (fun x => x = t1 ∨ x = t2) t1 "TIME-OF-DAY-UTC-AND-FRACTION-ENCODING"
    (.seq [("hours", .int 10), ("minutes", .int 0), ("seconds", .int 0), ("fraction", .int 123)]) :=
  ⟨⟨31, none, none⟩, by decide +kernel, .inl ⟨frac3_row, rfl, rfl⟩⟩

example : TimeAs (fun x => x = t1 ∨ x = t3) t3 "MIXED-ENCODING"
    (.choice "row-31" (.seq [("number-of-digits", .int 1), ("time-value",
      .seq [("hours", .int 11), ("minutes", .int 0), ("seconds", .int 0), ("fraction", .int 5)])])) :=
  ⟨⟨31, none, none⟩, by decide +kernel, .inr ⟨fracMixed, rfl, rfl⟩⟩

/-! ## The values of the encoding types -/

mutual
  partial def showVal : Val → String
    | .int i => toString i
    | .enum e => e
    | .seq cs => "{" ++ ", ".intercalate (cs.map fun (n, v) => n ++ " " ++ showVal v) ++ "}"
    | .choice a v => a ++ ":" ++ showVal v
    | _ => "?"
end

-- 32.2.7, 32.2.3: a date in 2020 has YEAR-ENCODING immediate
#guard showVal (directVal ⟨7, none, none⟩ d1) = "{year immediate:2020, month 1, day 5}"
#guard showVal (yearEncodingVal 1748) = "remainder:1748"
#guard showVal (yearEncodingVal 1749) = "near-past:1749"
#guard showVal (yearEncodingVal 2276) = "near-future:2276"
#guard showVal (directVal ⟨8, none, none⟩ (.point (.date (.ymd 12345 1 5)))) = "{year 12345, month 1, day 5}"
-- 32.2.1: a century
#guard showVal (directVal ⟨1, none, none⟩ (.point (.date (.c 19)))) = "19"
-- 32.3.18, 32.3.3: a time with a fraction and a time difference of -01:30
#guard showVal (directVal ⟨32, none, none⟩ (sample 32)) =
  "{local-time {hours 10, minutes 30, seconds 15, fraction 25}, time-difference {sign negative, hours 1, minutes 30}}"
-- 32.3.3: the minutes of a whole number of hours are omitted; 32.3.12 keeps local-hours flat
#guard showVal (timeVal 26 { hour := 7, frac := [5], zone := .diff 120 }) =
  "{local-hours 7, fraction 5, time-difference {sign positive, hours 2}}"
#guard showVal (timeVal 15 { hour := 7 }) = "7"
-- 32.6.3: the zero months are absent, and so are the weeks; the fraction of the days kept (32.6.5)
#guard showVal (durationVal du) =
  "{years 1, days 2, fractional-part {number-of-digits 1, fractional-value 5}}"
-- 32.6.3: a zero least significant element is present
#guard showVal (durationVal { years := some 0, months := some 0 }) = "{months 0}"
#guard showVal (durationVal { weeks := some 3 }) = "{weeks 3}"
-- 32.4, 32.9.2: a date-time, and a recurring interval with unlimited recurrences
#guard showVal (directVal ⟨33, some 7, some 21⟩ (sample 33)) =
  "{date {year immediate:2020, month 1, day 5}, time {hours 10, minutes 30, seconds 15}}"
#guard showVal (directVal ⟨47, none, none⟩ (sample 47)) =
  "{duration {years 1, days 2, fractional-part {number-of-digits 1, fractional-value 5}}}"
#guard showVal (directVal ⟨44, some 7, none⟩ (sample 44)) =
  "{recurrence 5, start {year immediate:2020, month 1, day 5}, end {year immediate:2020, month 1, day 5}}"
-- 32.11: MIXED-ENCODING, through DATE-TYPE and TIME-TYPE (with number-of-digits for rows 24–32)
#guard showVal (mixedVal ⟨33, some 7, some 30⟩
    (.point (.dateTime (dateOf 7) { hour := 1, minute := some 2, second := some 3, frac := [4, 0] }))) =
  "row-33:{date row-7:{year immediate:2020, month 1, day 5}, time {number-of-digits 2, time-type row-30:{hours 1, minutes 2, seconds 3, fraction 40}}}"
#guard showVal (mixedVal ⟨21, none, none⟩ (sample 21)) = "row-21:{hours 10, minutes 30, seconds 15}"
#guard showVal (mixedVal ⟨7, none, none⟩ d1) = "row-7:{year immediate:2020, month 1, day 5}"
#guard showVal (mixedVal ⟨37, none, none⟩ (sample 37)) =
  "row-37:{years 1, days 2, fractional-part {number-of-digits 1, fractional-value 5}}"
