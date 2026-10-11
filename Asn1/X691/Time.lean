import Asn1.X680.Semantics

/-!
# The time types in PER (X.691 32)

X.691 32 encodes a value of TIME, of the useful and defined time types and of the additional time
types (subtypes of TIME) as a value of one of the *encoding types* of 32.2–32.11. X.691 writes those
types in ASN.1, in an environment of AUTOMATIC TAGS (32.1.4); `timeEncModule` is that module, and
`Tests/asn1/x691-time.asn` is the same text, which `Tests/X691Time.lean` reads with the front end
and compares with the terms here.

Which encoding type is used depends on the property settings (X.680 38.2, Table 6) that *all* the
abstract values of the type share (32.1.2, Table 2):
- a row of Table 2 applies when every value has one of the settings its column 2 lists (and, for
  the rows of date-times and intervals, the same date and time rows, and for Fn rows the same n);
- the value is then the corresponding value of the column 3 type, or of its instantiation with the
  date and time rows' types (32.4.2, 32.5.1, …);
- otherwise (32.11) it is a value of MIXED-ENCODING, a CHOICE of every row.

The other clauses of X.691 encode the resulting value of the encoding type: `TimeAs` only says which
type and which value.
-/

namespace Asn1.X691

open Asn1.X680

/-! ## The encoding types (32.2–32.11), as ASN.1 notation -/

namespace TimeEnc

def iv (i : Int) : Bound := .val (.int i)

/-- `lo..hi` -/
def rangeE (lo hi : Bound) : ElemSet := .elem (.range lo false hi false)

/-- `INTEGER (root, ..., adds)` -/
def intC (root : ElemSet) (ext : Bool := false) (adds : Option ElemSet := none) : Ty :=
  .constrained (.integer []) (.mk root ext adds)

/-- `INTEGER (lo..hi)` -/
def intR (lo hi : Int) : Ty := intC (rangeE (iv lo) (iv hi))

/-- `INTEGER (lo..hi, ..., lo2..MAX)` -/
def intX (lo hi lo2 : Int) : Ty := intC (rangeE (iv lo) (iv hi)) true (some (rangeE (iv lo2) .max))

/-- `INTEGER (MIN..MAX)` -/
def intAny : Ty := intC (rangeE .min .max)

/-- `INTEGER (lo..MAX)` -/
def intAbove (lo : Int) : Ty := intC (rangeE (iv lo) .max)

/-- `SEQUENCE { … }` with mandatory components -/
def seqT (cs : List (String × Ty)) : Ty := .sequence (cs.map fun (n, t) => .mk n t .mandatory) none []

/-- `SEQUENCE { … }` with components marked as given -/
def seqP (cs : List (String × Ty × Presence)) : Ty :=
  .sequence (cs.map fun (n, t, p) => .mk n t p) none []

def choiceT (as : List (String × Ty)) : Ty := .choice (as.map fun (n, t) => .mk n t) none

/-- `Name {Arg, …}`, the actual parameters type references -/
def inst (n : String) (args : List String) : Ty := .paramRef none n (args.map fun a => .type (.ref a))

/-- 32.2.3 -/
def yearEncoding : Ty := choiceT [
  ("immediate", intR 2005 2020),
  ("near-future", intR 2021 2276),
  ("near-past", intR 1749 2004),
  ("remainder", intC (.union (rangeE .min (iv 1748)) (rangeE (iv 2277) .max)))]

/-- 32.2.5–32.2.14: a date's components after the year, with the year's type. -/
def dateSeq (year : String) (rest : List (String × Ty)) : Ty := seqT (("year", .ref year) :: rest)

/-- 32.2: the types of rows 1 to 14, in row order. -/
def dateTypes : List (String × Ty) := [
  ("CENTURY-ENCODING", intR 0 99),
  ("ANY-CENTURY-ENCODING", intAny),
  ("YEAR-ENCODING", yearEncoding),
  ("ANY-YEAR-ENCODING", intAny),
  ("YEAR-MONTH-ENCODING", dateSeq "YEAR-ENCODING" [("month", intR 1 12)]),
  ("ANY-YEAR-MONTH-ENCODING", dateSeq "ANY-YEAR-ENCODING" [("month", intR 1 12)]),
  ("DATE-ENCODING", dateSeq "YEAR-ENCODING" [("month", intR 1 12), ("day", intR 1 31)]),
  ("ANY-DATE-ENCODING", dateSeq "ANY-YEAR-ENCODING" [("month", intR 1 12), ("day", intR 1 31)]),
  ("YEAR-DAY-ENCODING", dateSeq "YEAR-ENCODING" [("day", intR 1 366)]),
  ("ANY-YEAR-DAY-ENCODING", dateSeq "ANY-YEAR-ENCODING" [("day", intR 1 366)]),
  ("YEAR-WEEK-ENCODING", dateSeq "YEAR-ENCODING" [("week", intR 1 53)]),
  ("ANY-YEAR-WEEK-ENCODING", dateSeq "ANY-YEAR-ENCODING" [("week", intR 1 53)]),
  ("YEAR-WEEK-DAY-ENCODING", dateSeq "YEAR-ENCODING" [("week", intR 1 53), ("day", intR 1 7)]),
  ("ANY-YEAR-WEEK-DAY-ENCODING", dateSeq "ANY-YEAR-ENCODING" [("week", intR 1 53), ("day", intR 1 7)])]

/-- 32.3.3 -/
def timeDifference : Ty := seqP [
  ("sign", .enumerated [("positive", none), ("negative", none)] none, .mandatory),
  ("hours", intR 0 15, .mandatory),
  ("minutes", intR 1 59, .optional)]

def hoursT : Ty := intR 0 24
def minutesT : Ty := intR 0 59
def secondsT : Ty := intR 0 60
def fractionT : Ty := intX 0 999 1000

/-- 32.3.1–32.3.18: the types of rows 15 to 32, in row order. -/
def timeTypes : List (String × Ty) := [
  ("HOURS-ENCODING", hoursT),
  ("HOURS-UTC-ENCODING", hoursT),
  ("HOURS-AND-DIFF-ENCODING", seqT [("local-hours", hoursT), ("time-difference", .ref "TIME-DIFFERENCE")]),
  ("MINUTES-ENCODING", seqT [("hours", hoursT), ("minutes", minutesT)]),
  ("MINUTES-UTC-ENCODING", seqT [("hours", hoursT), ("minutes", minutesT)]),
  ("MINUTES-AND-DIFF-ENCODING", seqT [
    ("local-time", seqT [("hours", hoursT), ("minutes", minutesT)]),
    ("time-difference", .ref "TIME-DIFFERENCE")]),
  ("TIME-OF-DAY-ENCODING", seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT)]),
  ("TIME-OF-DAY-UTC-ENCODING", seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT)]),
  ("TIME-OF-DAY-AND-DIFF-ENCODING", seqT [
    ("local-time", seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT)]),
    ("time-difference", .ref "TIME-DIFFERENCE")]),
  ("HOURS-AND-FRACTION-ENCODING", seqT [("hours", hoursT), ("fraction", fractionT)]),
  ("HOURS-UTC-AND-FRACTION-ENCODING", seqT [("hours", hoursT), ("fraction", fractionT)]),
  ("HOURS-AND-DIFF-AND-FRACTION-ENCODING", seqT [("local-hours", hoursT), ("fraction", fractionT),
    ("time-difference", .ref "TIME-DIFFERENCE")]),
  ("MINUTES-AND-FRACTION-ENCODING", seqT [("hours", hoursT), ("minutes", minutesT), ("fraction", fractionT)]),
  ("MINUTES-UTC-AND-FRACTION-ENCODING",
    seqT [("hours", hoursT), ("minutes", minutesT), ("fraction", fractionT)]),
  ("MINUTES-AND-DIFF-AND-FRACTION-ENCODING", seqT [
    ("local-time", seqT [("hours", hoursT), ("minutes", minutesT), ("fraction", fractionT)]),
    ("time-difference", .ref "TIME-DIFFERENCE")]),
  ("TIME-OF-DAY-AND-FRACTION-ENCODING",
    seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT), ("fraction", fractionT)]),
  ("TIME-OF-DAY-UTC-AND-FRACTION-ENCODING",
    seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT), ("fraction", fractionT)]),
  ("TIME-OF-DAY-AND-DIFF-AND-FRACTION-ENCODING", seqT [
    ("local-time", seqT [("hours", hoursT), ("minutes", minutesT), ("seconds", secondsT),
      ("fraction", fractionT)]),
    ("time-difference", .ref "TIME-DIFFERENCE")])]

/-- 32.6.1 -/
def durationIntervalEncoding : Ty := seqP [
  ("years", intX 0 31 32, .optional),
  ("months", intX 0 15 16, .optional),
  ("weeks", intX 0 63 64, .optional),
  ("days", intX 0 31 32, .optional),
  ("hours", intX 0 31 32, .optional),
  ("minutes", intX 0 63 64, .optional),
  ("seconds", intX 0 63 64, .optional),
  ("fractional-part", seqT [("number-of-digits", intX 1 3 4), ("fractional-value", intX 0 999 1000)],
    .optional)]

def recurrenceC : String × Ty × Presence := ("recurrence", .integer [], .optional)
def durationC : String × Ty × Presence := ("duration", .ref "DURATION-INTERVAL-ENCODING", .mandatory)
def dt : Ty := inst "DATE-TIME-ENCODING" ["Date-Type", "Time-Type"]

/-- A dummy reference that stands for a type (X.683 8.3: no governor). -/
def dummy (n : String) : Param := ⟨none, n⟩

def dateP : List Param := [dummy "Date-Type"]
def timeP : List Param := [dummy "Time-Type"]
def bothP : List Param := [dummy "Date-Type", dummy "Time-Type"]

def pa (n : String) (ps : List Param) (cs : List (String × Ty × Presence)) : ParamAssign :=
  .type n ps (seqP cs)

def m (t : Ty) : Ty × Presence := (t, .mandatory)

/-- 32.4.1, 32.5, 32.7, 32.8, 32.10, 32.11.6: the parameterized encoding types. -/
def paramTypes : List ParamAssign := [
  pa "DATE-TIME-ENCODING" bothP [("date", m (.ref "Date-Type")), ("time", m (.ref "Time-Type"))],
  pa "START-END-DATE-INTERVAL-ENCODING" dateP [("start", m (.ref "Date-Type")), ("end", m (.ref "Date-Type"))],
  pa "START-END-TIME-INTERVAL-ENCODING" timeP [("start", m (.ref "Time-Type")), ("end", m (.ref "Time-Type"))],
  pa "START-END-DATE-TIME-INTERVAL-ENCODING" bothP [("start", m dt), ("end", m dt)],
  pa "START-DATE-DURATION-INTERVAL-ENCODING" dateP [("start", m (.ref "Date-Type")), durationC],
  pa "START-TIME-DURATION-INTERVAL-ENCODING" timeP [("start", m (.ref "Time-Type")), durationC],
  pa "START-DATE-TIME-DURATION-INTERVAL-ENCODING" bothP [("start", m dt), durationC],
  pa "DURATION-END-DATE-INTERVAL-ENCODING" dateP [durationC, ("end", m (.ref "Date-Type"))],
  pa "DURATION-END-TIME-INTERVAL-ENCODING" timeP [durationC, ("end", m (.ref "Time-Type"))],
  pa "DURATION-END-DATE-TIME-INTERVAL-ENCODING" bothP [durationC, ("end", m dt)],
  pa "REC-START-END-DATE-INTERVAL-ENCODING" dateP
    [recurrenceC, ("start", m (.ref "Date-Type")), ("end", m (.ref "Date-Type"))],
  pa "REC-START-END-TIME-INTERVAL-ENCODING" timeP
    [recurrenceC, ("start", m (.ref "Time-Type")), ("end", m (.ref "Time-Type"))],
  pa "REC-START-END-DATE-TIME-INTERVAL-ENCODING" bothP [recurrenceC, ("start", m dt), ("end", m dt)],
  pa "REC-START-DATE-DURATION-INTERVAL-ENCODING" dateP
    [recurrenceC, ("start", m (.ref "Date-Type")), durationC],
  pa "REC-START-TIME-DURATION-INTERVAL-ENCODING" timeP
    [recurrenceC, ("start", m (.ref "Time-Type")), durationC],
  pa "REC-START-DATE-TIME-DURATION-INTERVAL-ENCODING" bothP [recurrenceC, ("start", m dt), durationC],
  pa "REC-DURATION-END-DATE-INTERVAL-ENCODING" dateP
    [recurrenceC, durationC, ("end", m (.ref "Date-Type"))],
  pa "REC-DURATION-END-TIME-INTERVAL-ENCODING" timeP
    [recurrenceC, durationC, ("end", m (.ref "Time-Type"))],
  pa "REC-DURATION-END-DATE-TIME-INTERVAL-ENCODING" bothP [recurrenceC, durationC, ("end", m dt)],
  .type "FRACTIONAL-TIME" timeP
    (seqT [("number-of-digits", intAbove 1), ("time-value", .ref "Time-Type")])]

end TimeEnc

open TimeEnc

/-! ## Table 2 -/

/-- A setting in column 2 of Table 2: a setting as written, or "Ln", "HFn", "HMFn", "HMSFn" (any
number `n`). -/
inductive SettingPat where
  | is (s : String)
  | numbered (prefix_ : String)
  deriving DecidableEq, Repr

def SettingPat.accepts : SettingPat → String → Bool
  | .is s, x => x == s
  | .numbered p, x =>
    let r := x.toList.drop p.length
    x.toList.take p.length == p.toList && !r.isEmpty && r.all Char.isDigit

/-- The Date settings of rows 1–14, two rows each, and the Time accuracies of rows 15–32 (three
rows each, then their Fn versions). -/
def dateScales : List String := ["C", "Y", "YM", "YMD", "YD", "YW", "YWD"]
def timeAccuracies : List String := ["H", "HM", "HMS"]
def zoneSettings : List String := ["L", "Z", "LD"]

/-- Interval-type and Rec-Interval rows 34–53, by their first row: SE, D, SD, DE. -/
def intervalSettings (r : Nat) : List (String × SettingPat) :=
  let point (k : Nat) : List (String × SettingPat) :=
    [("SE-point", .is (["Date", "Time", "Date-Time"].getD k ""))]
  if 34 ≤ r ∧ r ≤ 36 then [("Basic", .is "Interval"), ("Interval-type", .is "SE")] ++ point (r - 34)
  else if r = 37 then [("Basic", .is "Interval"), ("Interval-type", .is "D")]
  else if 38 ≤ r ∧ r ≤ 40 then [("Basic", .is "Interval"), ("Interval-type", .is "SD")] ++ point (r - 38)
  else if 41 ≤ r ∧ r ≤ 43 then [("Basic", .is "Interval"), ("Interval-type", .is "DE")] ++ point (r - 41)
  else if 44 ≤ r ∧ r ≤ 46 then [("Basic", .is "Rec-Interval"), ("Interval-type", .is "SE")] ++ point (r - 44)
  else if r = 47 then [("Basic", .is "Rec-Interval"), ("Interval-type", .is "D")]
  else if 48 ≤ r ∧ r ≤ 50 then [("Basic", .is "Rec-Interval"), ("Interval-type", .is "SD")] ++ point (r - 48)
  else [("Basic", .is "Rec-Interval"), ("Interval-type", .is "DE")] ++ point (r - 51)

/-- X.691 Table 2, column 2: the property settings of row `r`, as alternatives ("… or …"). -/
def table2 (r : Nat) : List (List (String × SettingPat)) :=
  if 1 ≤ r ∧ r ≤ 14 then
    let sc : String := dateScales.getD ((r - 1) / 2) ""
    let base : List (String × SettingPat) := [("Basic", .is "Date"), ("Date", .is sc)]
    -- odd rows: Year=Basic or Year=Proleptic; even rows: Year=Negative or Year=Ln
    if r % 2 = 1 then [base ++ [("Year", .is "Basic")], base ++ [("Year", .is "Proleptic")]]
    else [base ++ [("Year", .is "Negative")], base ++ [("Year", .numbered "L")]]
  else if 15 ≤ r ∧ r ≤ 32 then
    let k := r - 15
    let acc : String := timeAccuracies.getD ((k % 9) / 3) ""
    let time : SettingPat := if k < 9 then .is acc else .numbered (acc ++ "F")
    [[("Basic", .is "Time"), ("Time", time), ("Local-or-UTC", .is (zoneSettings.getD (k % 3) ""))]]
  else if r = 33 then [[("Basic", .is "Date-Time")]]
  else if 34 ≤ r ∧ r ≤ 53 then [intervalSettings r]
  else []

/-- Table 2, column 3: the type of rows 1–32, 37 and 47, and the parameterized type of the others. -/
def rowTypeName (r : Nat) : String :=
  if 1 ≤ r ∧ r ≤ 14 then (dateTypes.getD (r - 1) ("", .null)).1
  else if 15 ≤ r ∧ r ≤ 32 then (timeTypes.getD (r - 15) ("", .null)).1
  else match r with
    | 33 => "DATE-TIME-ENCODING"
    | 34 => "START-END-DATE-INTERVAL-ENCODING"
    | 35 => "START-END-TIME-INTERVAL-ENCODING"
    | 36 => "START-END-DATE-TIME-INTERVAL-ENCODING"
    | 37 => "DURATION-INTERVAL-ENCODING"
    | 38 => "START-DATE-DURATION-INTERVAL-ENCODING"
    | 39 => "START-TIME-DURATION-INTERVAL-ENCODING"
    | 40 => "START-DATE-TIME-DURATION-INTERVAL-ENCODING"
    | 41 => "DURATION-END-DATE-INTERVAL-ENCODING"
    | 42 => "DURATION-END-TIME-INTERVAL-ENCODING"
    | 43 => "DURATION-END-DATE-TIME-INTERVAL-ENCODING"
    | 44 => "REC-START-END-DATE-INTERVAL-ENCODING"
    | 45 => "REC-START-END-TIME-INTERVAL-ENCODING"
    | 46 => "REC-START-END-DATE-TIME-INTERVAL-ENCODING"
    | 47 => "REC-DURATION-INTERVAL-ENCODING"
    | 48 => "REC-START-DATE-DURATION-INTERVAL-ENCODING"
    | 49 => "REC-START-TIME-DURATION-INTERVAL-ENCODING"
    | 50 => "REC-START-DATE-TIME-DURATION-INTERVAL-ENCODING"
    | 51 => "REC-DURATION-END-DATE-INTERVAL-ENCODING"
    | 52 => "REC-DURATION-END-TIME-INTERVAL-ENCODING"
    | 53 => "REC-DURATION-END-DATE-TIME-INTERVAL-ENCODING"
    | _ => ""

/-- X.691 32.11.2: the main determining rows that require a date determining row (the rows whose
values carry a date). -/
def needsDate (r : Nat) : Bool := r ∈ [33, 34, 36, 38, 40, 41, 43, 44, 46, 48, 50, 51, 53]

/-- X.691 32.11.3: the main determining rows that require a time determining row. -/
def needsTime (r : Nat) : Bool := r ∈ [33, 35, 36, 39, 40, 42, 43, 45, 46, 49, 50, 52, 53]

/-- Table 2, column 2 of rows 33–53: the date rows whose additional settings all values must share:
"one of rows 1 to 14" for a date, "one of rows 7, 8, 9, 10, 13 and 14" for a date-time. -/
def dateRowsAllowed (r : Nat) : List Nat :=
  if r ∈ [34, 38, 41, 44, 48, 51] then List.range' 1 14 else [7, 8, 9, 10, 13, 14]

/-- Rows 24–32: a time with a fraction of n digits (32.1.3). -/
def isFracRow (r : Nat) : Bool := 24 ≤ r && r ≤ 32

/-! ## Which row a value is in (32.11.1–32.11.3) -/

/-- The value has every setting of an alternative of column 2. -/
def settingsMatch (props : List (String × String)) (alt : List (String × SettingPat)) : Bool :=
  alt.all fun (p, pat) => props.any fun (q, s) => q == p && pat.accepts s

/-- X.691 32.1.2, 32.11.1: the value has the property settings listed in a row of column 2. -/
def rowMatches (r : Nat) (v : TimeV) : Bool := (table2 r).any (settingsMatch v.props)

/-- X.691 32.11.2, 32.11.3, and the "additional property settings" of rows 33–53: the value has
the settings a row lists other than Basic. -/
def additionalMatch (r : Nat) (v : TimeV) : Bool :=
  (table2 r).any fun alt => settingsMatch v.props (alt.filter (·.1 != "Basic"))

/-- X.691 32.11.1: the main determining row. -/
def mainRow (v : TimeV) : Option Nat := (List.range' 1 53).find? (rowMatches · v)

/-- X.691 32.11.2: the date determining row. -/
def dateRowOf (v : TimeV) : Option Nat := (List.range' 1 14).find? (additionalMatch · v)

/-- X.691 32.11.3: the time determining row. -/
def timeRowOf (v : TimeV) : Option Nat := (List.range' 15 18).find? (additionalMatch · v)

/-- The time of day a value carries, if any (an interval's points share their accuracy,
`IntervalV.Wf`). -/
def _root_.Asn1.X680.PointV.tod? : PointV → Option TimeOfDayV
  | .time t | .dateTime _ t => some t
  | .date _ => none

def _root_.Asn1.X680.IntervalV.tod? : IntervalV → Option TimeOfDayV
  | .se a _ | .sd a _ => a.tod?
  | .de _ b => b.tod?
  | .d _ => none

def _root_.Asn1.X680.TimeV.tod? : TimeV → Option TimeOfDayV
  | .point p => p.tod?
  | .interval i | .recurring _ i => i.tod?

/-- The n of "Fn": the number of digits of the fraction (32.1.3, 32.11.6, 32.11.9). -/
def fracDigitsOf (v : TimeV) : Option Nat := v.tod?.map (·.frac.length)

/-- The rows that decide a value's encoding: the main row, and the date and time determining rows
when the main row has them. -/
structure Rows where
  main : Nat
  date : Option Nat := none
  time : Option Nat := none
  deriving DecidableEq, Repr

/-- X.691 32.11.1–32.11.3: the rows of a value. -/
def rowsOf (v : TimeV) : Option Rows :=
  match mainRow v with
  | none => none
  | some r =>
    let d := if needsDate r then dateRowOf v else none
    let t := if needsTime r then timeRowOf v else none
    if (needsDate r && d.isNone) || (needsTime r && t.isNone) then none
    else some ⟨r, d, t⟩

/-- X.691 32.1.2, 32.1.3, Table 2: the rows `c` apply to a type whose values are `vals`: every value
has the settings of row `c.main`, the same date determining row (one of those allowed) and the same
time determining row, if the row has them, and, if a time row is 24 to 32, the same n in Fn.

OPEN (ledger X691-53): 32.1.3 says "for rows 24 to 32 to be applicable"; rows 33–53 instantiate
their Time-Type with the types of rows 24–32, which have no number-of-digits either, so the same n
is required of their time determining row.

OPEN (ledger X691-54): "the same additional property settings specified in one of rows …" is read
as: all values have the same date (time) determining row, and it is one of the rows listed.

OPEN (ledger X691-55): for a type with no values every row applies vacuously; `TimeAs` then takes
the row of the value it encodes. -/
def RowApplies (vals : TimeV → Prop) (c : Rows) : Prop :=
  1 ≤ c.main ∧ c.main ≤ 53 ∧
  (∀ x, vals x → rowMatches c.main x = true) ∧
  (if needsDate c.main then ∃ dr ∈ dateRowsAllowed c.main, c.date = some dr ∧
      ∀ x, vals x → dateRowOf x = some dr
   else c.date = none) ∧
  (if needsTime c.main then ∃ tr, c.time = some tr ∧ ∀ x, vals x → timeRowOf x = some tr
   else c.time = none) ∧
  -- 32.1.3
  ((isFracRow c.main || c.time.any isFracRow) = true →
    ∃ n, ∀ x, vals x → fracDigitsOf x = some n)

/-! ## The values of the encoding types (32.2–32.10) -/

/-- 32.2.3: the alternative of YEAR-ENCODING whose range holds the year.

OPEN (ledger X691-57): 32.2.3 sets "the integer value" to the year without naming the alternative;
the ranges are disjoint and cover every year, so it is the one whose range holds it. -/
def yearEncodingVal (y : Int) : Val :=
  .choice (if 2005 ≤ y ∧ y ≤ 2020 then "immediate" else if 2021 ≤ y ∧ y ≤ 2276 then "near-future"
    else if 1749 ≤ y ∧ y ≤ 2004 then "near-past" else "remainder") (.int y)

/-- 32.2.1–32.2.14: the value of the type of date row `r` (odd rows use YEAR-ENCODING, 32.2.3; even
rows ANY-YEAR-ENCODING, 32.2.4).

OPEN (ledger X691-56): 32.2.1 ("the first two digits of the year component") and 32.2.2 ("the year
component … ignoring the last two digits") are both the century a "Date=C" value records (X.680
Table 7, [YYC], [±YYC], [±Y…YC]). -/
def dateVal (r : Nat) : DateV → Val
  | .c k => .int k
  | .y y => if r % 2 = 1 then yearEncodingVal y else .int y
  | .ym y mo => .seq [("year", if r % 2 = 1 then yearEncodingVal y else .int y), ("month", .int mo)]
  | .ymd y mo d =>
    .seq [("year", if r % 2 = 1 then yearEncodingVal y else .int y), ("month", .int mo), ("day", .int d)]
  | .yd y d => .seq [("year", if r % 2 = 1 then yearEncodingVal y else .int y), ("day", .int d)]
  | .yw y w => .seq [("year", if r % 2 = 1 then yearEncodingVal y else .int y), ("week", .int w)]
  | .ywd y w d =>
    .seq [("year", if r % 2 = 1 then yearEncodingVal y else .int y), ("week", .int w), ("day", .int d)]

/-- 32.3.3: TIME-DIFFERENCE, the sign, hours and minutes of a time difference of `m` minutes; the
minutes omitted when zero.

OPEN (ledger X691-51): a time difference of zero ("+00", or "-00" if written) has sign positive. -/
def timeDifferenceVal (m : Int) : Val :=
  .seq ([("sign", .enum (if m < 0 then "negative" else "positive")), ("hours", .int (m.natAbs / 60))] ++
    (if m.natAbs % 60 = 0 then [] else [("minutes", .int (m.natAbs % 60))]))

/-- 32.3.1–32.3.18: the value of the type of time row `r`.
- The fraction is the fraction's digits as an integer, "multiplied by ten-to-the-power-N".
  OPEN (ledger X691-50): 32.3.13 and 32.3.14 say "fractional hours" for the fraction of a time with
  minutes; it is the fraction of the minutes (ISO 8601 4.2.2.4, and 32.3.15 for the same accuracy).
- With a time difference (Local-or-UTC=LD) the components are those of the local time (32.3.3). -/
def timeVal (r : Nat) (t : TimeOfDayV) : Val :=
  let k := r - 15
  let acc := (k % 9) / 3
  let frac := 9 ≤ k
  let base : List (String × Val) :=
    [("hours", .int t.hour)] ++
    (if 1 ≤ acc then [("minutes", .int (t.minute.getD 0))] else []) ++
    (if 2 ≤ acc then [("seconds", .int (t.second.getD 0))] else []) ++
    (if frac then [("fraction", .int t.frac.val)] else [])
  let td : List (String × Val) := match t.zone with
    | .diff m => [("time-difference", timeDifferenceVal m)]
    | _ => [("time-difference", timeDifferenceVal 0)]
  if k % 3 = 2 then
    -- 32.3.3, 32.3.12: the hours (and fraction) of the local time are components of their own;
    -- 32.3.6, 32.3.9, 32.3.15, 32.3.18: otherwise a local-time sequence
    if acc = 0 then .seq ([("local-hours", .int t.hour)] ++
        (if frac then [("fraction", .int t.frac.val)] else []) ++ td)
    else .seq ([("local-time", .seq base)] ++ td)
  -- 32.3.1, 32.3.2: hours alone are an integer
  else if acc = 0 ∧ ¬ frac then .int t.hour
  else .seq base

/-- 32.6.2–32.6.5: DURATION-INTERVAL-ENCODING. A zero time element without a fraction is absent
unless it is the least significant (32.6.3); `DurationV.norm` is exactly that, since only the least
significant element has a fraction (X.680 38.3.6.13). Weeks are present iff nothing else is
(32.6.2), which `DurationV.Wf` already says of the abstract value. -/
def durationVal (d : DurationV) : Val :=
  let d := d.norm
  let names := ["years", "months", "weeks", "days", "hours", "minutes", "seconds"]
  .seq ((names.zip d.elems).filterMap (fun (n, o) => o.map fun x => (n, .int x)) ++
    (if d.frac = [] then []
     else [("fractional-part", .seq [("number-of-digits", .int d.frac.length),
                                     ("fractional-value", .int d.frac.val)])]))

/-- 32.8–32.10: the recurrence component, absent for an unlimited number of recurrences. -/
def recurrenceVal : Option Nat → List (String × Val)
  | some n => [("recurrence", .int n)]
  | none => []

/-- The components of an interval (32.5, 32.7), each point as `pt` gives it. -/
def intervalComps (pt : PointV → Val) : IntervalV → List (String × Val)
  | .se a b => [("start", pt a), ("end", pt b)]
  | .d du => [("duration", durationVal du)]
  | .sd a du => [("start", pt a), ("duration", durationVal du)]
  | .de du b => [("duration", durationVal du), ("end", pt b)]

/-- The value of an encoding type for rows 33–53, each time point as `pt` gives it. -/
def shapeVal (pt : PointV → Val) : TimeV → Val
  | .point p => pt p
  -- 32.6
  | .interval (.d du) => durationVal du
  | .interval i => .seq (intervalComps pt i)
  -- 32.8–32.10
  | .recurring n i => .seq (recurrenceVal n ++ intervalComps pt i)

/-- 32.2–32.4: a time point as a value of the date row `dr`'s type, the time row `tr`'s type, or
DATE-TIME-ENCODING {…} (32.4.2). -/
def pointVal (dr tr : Nat) : PointV → Val
  | .date d => dateVal dr d
  | .time t => timeVal tr t
  | .dateTime d t => .seq [("date", dateVal dr d), ("time", timeVal tr t)]

/-- 32.11.7: a date as DATE-TYPE: the alternative of its date determining row. -/
def dateTypeVal (dr : Nat) (d : DateV) : Val := .choice s!"row-{dr}" (dateVal dr d)

/-- 32.11.8, 32.11.9: a time as TIME-TYPE: number-of-digits present iff the time determining row
is 24 to 32. -/
def timeTypeVal (tr : Nat) (t : TimeOfDayV) : Val :=
  .seq ((if isFracRow tr then [("number-of-digits", .int t.frac.length)] else []) ++
    [("time-type", .choice s!"row-{tr}" (timeVal tr t))])

/-- 32.11: a time point inside MIXED-ENCODING's rows 33–53, through DATE-TYPE and TIME-TYPE. -/
def pointMixedVal (dr tr : Nat) : PointV → Val
  | .date d => dateTypeVal dr d
  | .time t => timeTypeVal tr t
  | .dateTime d t => .seq [("date", dateTypeVal dr d), ("time", timeTypeVal tr t)]

/-- Table 2 column 3: the value of the type of rows `c` (32.2–32.10). -/
def directVal (c : Rows) (v : TimeV) : Val :=
  shapeVal (pointVal (c.date.getD c.main) (c.time.getD c.main)) v

/-- X.691 32.11.4, 32.11.5: the value of MIXED-ENCODING: the alternative of the main determining
row; rows 24–32 through FRACTIONAL-TIME (32.11.6), and the points of rows 33–53 through DATE-TYPE
and TIME-TYPE (32.11.7, 32.11.8). -/
def mixedVal (c : Rows) (v : TimeV) : Val :=
  .choice s!"row-{c.main}" <|
    match v with
    | .point (.time t) =>
      if isFracRow c.main then
        .seq [("number-of-digits", .int t.frac.length), ("time-value", timeVal c.main t)]
      else timeVal c.main t
    | .point (.date d) => dateVal c.main d
    | _ => shapeVal (pointMixedVal (c.date.getD 0) (c.time.getD 0)) v

/-! ## The module of encoding types, and its instantiations -/

/-- The name of the type a row (with its date and time rows) is encoded as: the type of column 3,
or its instantiation (32.4.2, 32.5.1–32.10.6: "an instantiation of this type with the Date-Type
[and Time-Type] actual parameters set to the types specified in Table 2 column 3" of the date and
time rows), written `NAME {ARG, ARG}`.

OPEN (ledger X691-52): X.691 names no instantiation; `timeEncModule` holds each one as a type
assignment of that name, whose type is the "ParameterizedType" (X.683 9.2) itself. -/
def encName (c : Rows) : String :=
  let args := (c.date.map rowTypeName).toList ++ (c.time.map rowTypeName).toList
  if args = [] then rowTypeName c.main
  else rowTypeName c.main ++ " {" ++ ", ".intercalate args ++ "}"

/-- Every instantiation that Table 2 can call for, as a type assignment whose name is `encName`.
A type of the module, so that `TimeAs` can name it; the parameterized assignments themselves are
`paramTypes`. -/
def instances : List (String × Ty) :=
  (List.range' 33 21).flatMap fun r =>
    let ds : List (Option Nat) := if needsDate r then (dateRowsAllowed r).map some else [none]
    let ts : List (Option Nat) := if needsTime r then (List.range' 15 18).map some else [none]
    ds.flatMap fun d => ts.filterMap fun t =>
      if d.isNone && t.isNone then none
      else
        let c : Rows := ⟨r, d, t⟩
        some (encName c, inst (rowTypeName r) ((d.map rowTypeName).toList ++ (t.map rowTypeName).toList))

/-- 32.11.5: MIXED-ENCODING. -/
def mixedEncoding : Ty :=
  let dateArgs : List String := ["DATE-TYPE"]
  let timeArgs : List String := ["TIME-TYPE"]
  choiceT ((List.range' 1 53).map fun r =>
    (s!"row-{r}",
     if r ≤ 23 ∨ r = 37 ∨ r = 47 then .ref (rowTypeName r)
     else if r ≤ 32 then inst "FRACTIONAL-TIME" [rowTypeName r]
     else inst (rowTypeName r) ((if needsDate r then dateArgs else []) ++ (if needsTime r then timeArgs else []))))

/-- 32.11.7: DATE-TYPE. -/
def dateType : Ty := choiceT ((List.range' 1 14).map fun r => (s!"row-{r}", .ref (rowTypeName r)))

/-- 32.11.8: TIME-TYPE. -/
def timeType : Ty := seqP [
  ("number-of-digits", intAbove 1, .optional),
  ("time-type", choiceT ((List.range' 15 18).map fun r => (s!"row-{r}", .ref (rowTypeName r))),
    .mandatory)]

/-- The type assignments of 32.2–32.11, in the order X.691 gives them. -/
def timeEncTypes : List (String × Ty) :=
  dateTypes ++ (timeTypes.take 3) ++ [("TIME-DIFFERENCE", timeDifference)] ++ timeTypes.drop 3 ++
  [("DURATION-INTERVAL-ENCODING", durationIntervalEncoding),
   ("REC-DURATION-INTERVAL-ENCODING", seqP [recurrenceC, durationC]),
   ("MIXED-ENCODING", mixedEncoding),
   ("DATE-TYPE", dateType),
   ("TIME-TYPE", timeType)]

/-- X.691 32.1.4, 32.2–32.11: the encoding types, as a module with AUTOMATIC TAGS, together with
the instantiations of the parameterized ones that Table 2 calls for (`instances`). -/
def timeEncModule : Module :=
  { name := "X691-TIME-ENCODINGS", header := ⟨.automatic, false⟩,
    types := timeEncTypes ++ instances, params := paramTypes }

/-! ## The encoding of a time value -/

/-- X.691 32.1.2, Table 2, 32.11: a time value `v`, of a type whose values (as PER-visible
constraints restrict them, 10.3.13 and 32.1.1) are those satisfying `vals`, is encoded as the value
`w` of the type named `name` in `timeEncModule`:
- if a row of Table 2 applies to the type (`RowApplies`), the row `v` is in, `w` its value of the
  type of column 3 (or of its instantiation);
- otherwise (32.11), its value of MIXED-ENCODING.
`v` is a value of the type, so a row that applies is the row of `v`. -/
def TimeAs (vals : TimeV → Prop) (v : TimeV) (name : String) (w : Val) : Prop :=
  ∃ c, rowsOf v = some c ∧
    ((RowApplies vals c ∧ name = encName c ∧ w = directVal c v) ∨
     ((¬ ∃ c', RowApplies vals c') ∧ name = "MIXED-ENCODING" ∧ w = mixedVal c v))

end Asn1.X691
