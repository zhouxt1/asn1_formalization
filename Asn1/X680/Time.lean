/-!
# The time type (X.680 38)

A TIME abstract value is a date, a time of day, a date and a time of day, a time interval, or a
recurring time interval (Table 6, "Basic"), in the sense of ISO 8601. X.680 characterizes the
abstract values by their *time properties* and the *settings* of those properties (38.2, Table 6),
and gives each abstract value a value notation (38.3, Table 7).

`TimeV` holds the components of a value as its notation writes them. Two notations differ without
differing in abstract value only in the ways 38.3.4 NOTE 1 lists:
- the comma or full stop of a decimal fraction, and `±hh` against `±hh:00`, which `TimeV` does not
  record;
- the time difference of an interval's end point, which may be omitted when it is the start's, and
  which `TimeV` always records;
- zero components of a duration (38.2.3), which `TimeV` records as written. `TimeV.norm` removes
  them, as X.691 32.6.3 does.

The props of a value (`TimeV.props`) are its property settings, and the SETTINGS subtype notation
(51.10) selects by them.
-/

namespace Asn1.X680

/-- Decimal digits, most significant first: a decimal fraction (38.3.6.12, Table 7). Its length is
the accuracy, so `5` and `50` are different fractions. -/
abbrev Digits := List (Fin 10)

/-- The fraction's digits as a whole number. -/
def Digits.val (ds : Digits) : Nat := ds.foldl (fun a d => 10 * a + d.val) 0

/-- The number of decimal digits that a whole number requires (Table 6, "Year=Ln", "Recurrence=Rn"). -/
def decDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-! ## The abstract values -/

/-- X.680 Table 6, "Date": the time scale and accuracy of a date, with its components. A year, or a
century, is any integer; Table 6, "Year", classifies it. -/
inductive DateV where
  /-- "Date=C", ISO 8601 4.1.2.3 c): a century, the year without its last two digits -/
  | c (century : Int)
  /-- "Date=Y", ISO 8601 4.1.2.3 b) -/
  | y (year : Int)
  /-- "Date=YM", ISO 8601 4.1.2.3 a) -/
  | ym (year : Int) (month : Nat)
  /-- "Date=YMD", ISO 8601 4.1.2.2 -/
  | ymd (year : Int) (month day : Nat)
  /-- "Date=YD", ISO 8601 4.1.3.2: an ordinal date -/
  | yd (year : Int) (day : Nat)
  /-- "Date=YW", ISO 8601 4.1.4.3 -/
  | yw (year : Int) (week : Nat)
  /-- "Date=YWD", ISO 8601 4.1.4.2 -/
  | ywd (year : Int) (week day : Nat)
  deriving DecidableEq, Repr

/-- X.680 Table 6, "Local-or-UTC". -/
inductive Zone where
  /-- "L": local time of day only -/
  | local_
  /-- "Z": UTC -/
  | utc
  /-- "LD": local time of day, which is ahead of UTC by this many minutes (ISO 8601 4.2.5.1) -/
  | diff (minutes : Int)
  deriving DecidableEq, Repr

/-- A time of day (ISO 8601 4.2). Table 6, "Time", is its accuracy: the components present, and the
digits of the decimal fraction of the last of them. -/
structure TimeOfDayV where
  hour : Nat
  minute : Option Nat := none
  second : Option Nat := none
  frac : Digits := []
  zone : Zone := .local_
  deriving DecidableEq, Repr

/-- A time point: Table 6, "Basic=Date", "Basic=Time" and "Basic=Date-Time", and the start and end
points of intervals ("SE-point"). -/
inductive PointV where
  | date (d : DateV)
  | time (t : TimeOfDayV)
  | dateTime (d : DateV) (t : TimeOfDayV)
  deriving DecidableEq, Repr

/-- X.680 38.3.6: a duration, its time elements as written, and the decimal fraction of the least
significant of them (38.3.6.13). -/
structure DurationV where
  years : Option Nat := none
  months : Option Nat := none
  weeks : Option Nat := none
  days : Option Nat := none
  hours : Option Nat := none
  minutes : Option Nat := none
  seconds : Option Nat := none
  frac : Digits := []
  deriving DecidableEq, Repr

/-- Table 6, "Interval-type". -/
inductive IntervalV where
  /-- "SE": a start and an end point -/
  | se (start end_ : PointV)
  /-- "D": a duration -/
  | d (dur : DurationV)
  /-- "SD": a start point and a duration -/
  | sd (start : PointV) (dur : DurationV)
  /-- "DE": a duration and an end point -/
  | de (dur : DurationV) (end_ : PointV)
  deriving DecidableEq, Repr

/-- X.680 38.2: a time abstract value. -/
inductive TimeV where
  /-- "Basic=Date", "Basic=Time" or "Basic=Date-Time" -/
  | point (p : PointV)
  /-- "Basic=Interval" -/
  | interval (i : IntervalV)
  /-- "Basic=Rec-Interval": the number of recurrences, `none` for "Recurrence=Unlimited" -/
  | recurring (n : Option Nat) (i : IntervalV)
  deriving DecidableEq, Repr

/-! ## The proleptic Gregorian calendar (ISO 8601 3.2.1, 4.1; X.680 Annex J.2.2) -/

def isLeap (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- ISO 8601 3.2.1: the days of month `m` in year `y`. -/
def monthDays (y : Int) (m : Nat) : Nat :=
  match m with
  | 2 => if isLeap y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

def yearDays (y : Int) : Nat := if isLeap y then 366 else 365

/-- The day of the week of 1 January of year `y`, 1 for Monday to 7 for Sunday (ISO 8601 2.2.8). The
Gregorian calendar repeats every 400 years, so this is Gauss's rule, taken modulo 7 with the
remainders of Euclidean division. -/
def jan1Weekday (y : Int) : Nat :=
  let p := y - 1
  let d := (1 + 5 * (p % 4) + 4 * (p % 100) + 6 * (p % 400)) % 7
  if d = 0 then 7 else d.toNat

/-- ISO 8601 2.2.10: a year has 53 calendar weeks if it begins on a Thursday, or is a leap year that
begins on a Wednesday; otherwise 52. -/
def yearWeeks (y : Int) : Nat :=
  if jan1Weekday y = 4 || (isLeap y && jan1Weekday y = 3) then 53 else 52

/-! ## Time properties and their settings (38.2, Table 6) -/

/-- Table 6, "Year", for a year. -/
def yearSetting (y : Int) : String :=
  if 1582 ≤ y ∧ y ≤ 9999 then "Basic"
  else if 0 ≤ y ∧ y ≤ 1581 then "Proleptic"
  else if -9999 ≤ y ∧ y ≤ -1 then "Negative"
  else s!"L{decDigits y.natAbs}"

/-- Table 6, "Year", for a century: Basic for 15 to 99, Proleptic for 00 to 14, Negative for −99 to
−01, and "Ln" for a century whose decimal representation requires n − 2 digits. -/
def centurySetting (c : Int) : String :=
  if 15 ≤ c ∧ c ≤ 99 then "Basic"
  else if 0 ≤ c ∧ c ≤ 14 then "Proleptic"
  else if -99 ≤ c ∧ c ≤ -1 then "Negative"
  else s!"L{decDigits c.natAbs + 2}"

def DateV.scale : DateV → String
  | .c _ => "C" | .y _ => "Y" | .ym .. => "YM" | .ymd .. => "YMD" | .yd .. => "YD"
  | .yw .. => "YW" | .ywd .. => "YWD"

def DateV.yearOf : DateV → Int
  | .c k => k | .y k | .ym k _ | .ymd k _ _ | .yd k _ | .yw k _ | .ywd k _ _ => k

def DateV.year : DateV → String
  | .c k => centurySetting k
  | d => yearSetting d.yearOf

/-- Table 6, "Time": H, HM, HMS, HFn, HMFn or HMSFn. -/
def TimeOfDayV.accuracy (t : TimeOfDayV) : String :=
  let f := if t.frac = [] then "" else s!"F{t.frac.length}"
  match t.minute, t.second with
  | none, _ => "H" ++ f
  | some _, none => "HM" ++ f
  | some _, some _ => "HMS" ++ f

def Zone.setting : Zone → String
  | .local_ => "L" | .utc => "Z" | .diff _ => "LD"

/-- The components after the hour are all zero. -/
def TimeOfDayV.restZero (t : TimeOfDayV) : Bool :=
  t.minute.all (· = 0) && t.second.all (· = 0) && t.frac.all (·.val = 0)

/-- Table 6, "Midnight", and 38.2.2: hour 00 with nothing after it but zeros is midnight at the
start of a day, hour 24 likewise is midnight at the end of a day. Other times have no setting. -/
def TimeOfDayV.midnight (t : TimeOfDayV) : List String :=
  if t.restZero then
    if t.hour = 0 then ["Start"] else if t.hour = 24 then ["End"] else []
  else []

/-- Table 6, "Basic", of a point, and "SE-point" of an interval's points. -/
def PointV.basic : PointV → String
  | .date _ => "Date" | .time _ => "Time" | .dateTime .. => "Date-Time"

def DateV.props (d : DateV) : List (String × String) := [("Date", d.scale), ("Year", d.year)]

def TimeOfDayV.props (t : TimeOfDayV) : List (String × String) :=
  [("Time", t.accuracy), ("Local-or-UTC", t.zone.setting)] ++ t.midnight.map (("Midnight", ·))

def PointV.props : PointV → List (String × String)
  | .date d => d.props
  | .time t => t.props
  | .dateTime d t => d.props ++ t.props

/-- The settings an interval's points give it. An interval has a single setting for Date, Year,
Time and Local-or-UTC (Table 6, the NOTEs in column 1), and `IntervalV.Wf` makes the two points
agree on them. Midnight is not so restricted, so an interval from 00:00 to 24:00 has both settings. -/
def IntervalV.props : IntervalV → List (String × String)
  | .se a b => [("Interval-type", "SE"), ("SE-point", a.basic)] ++ a.props ++ b.props
  | .d _ => [("Interval-type", "D")]
  | .sd a _ => [("Interval-type", "SD"), ("SE-point", a.basic)] ++ a.props
  | .de _ b => [("Interval-type", "DE"), ("SE-point", b.basic)] ++ b.props

/-- Table 6, "Recurrence": "Unlimited", or "Rn" for a number of recurrences that requires n digits
(G.3.5: R15 has "Recurrence=R2"). -/
def recurrenceSetting : Option Nat → String
  | none => "Unlimited"
  | some k => s!"R{decDigits k}"

/-- X.680 38.2.1, Table 6: every (property, setting) pair the value has. Every value has a Basic
setting (51.10.6). -/
def TimeV.props : TimeV → List (String × String)
  | .point p => ("Basic", p.basic) :: p.props
  | .interval i => ("Basic", "Interval") :: i.props
  | .recurring n i => ("Basic", "Rec-Interval") :: ("Recurrence", recurrenceSetting n) :: i.props

/-- X.680 51.10.5: the value satisfies a "PropertyAndSettingPair" if it has no setting for the
property, or has that setting.

OPEN (ledger X680-13): an interval can have two settings of Midnight, one from each point. We take
51.10.5 b) to require that every setting the value has for the property is the one named, which
is what the EXAMPLE of 51.10.5 says of "Midnight=Start": it excludes "those that have the property
setting Midnight=End". -/
def TimeV.satisfies (v : TimeV) (ps : List (String × String)) : Bool :=
  ps.all fun (p, s) => (v.props.filter (·.1 == p)).all (·.2 == s)

/-! ## Which values exist -/

/-- ISO 8601 4.1: the components of a date are in range. -/
def DateV.Wf : DateV → Bool
  | .c _ | .y _ => true
  | .ym _ m => 1 ≤ m && m ≤ 12
  | .ymd yr m dy => 1 ≤ m && m ≤ 12 && 1 ≤ dy && dy ≤ monthDays yr m
  | .yd yr dy => 1 ≤ dy && dy ≤ yearDays yr
  | .yw yr w => 1 ≤ w && w ≤ yearWeeks yr
  | .ywd yr w dy => 1 ≤ w && w ≤ yearWeeks yr && 1 ≤ dy && dy ≤ 7

/-- ISO 8601 4.2: a time of day. Hours are 00 to 24, and 24 only for midnight at the end of a day
(38.2.2); minutes 00 to 59; seconds 00 to 60, 60 being a leap second (ISO 8601 4.2.1, and X.691
32.3.7's INTEGER (0..60)). Seconds need minutes (ISO 8601 4.2.2.3). The time difference is at most
15 hours either way (Table 6, "Local-or-UTC"). -/
def TimeOfDayV.Wf (t : TimeOfDayV) : Bool :=
  t.hour ≤ 24 && (t.hour = 24 → t.restZero) && t.minute.all (· ≤ 59) && t.second.all (· ≤ 60) &&
  (t.second.isSome → t.minute.isSome) &&
  match t.zone with
  | .diff m => m.natAbs ≤ 15 * 60
  | _ => true

/-- A complete date: calendar, ordinal or week date (ISO 8601 4.1.2.2, 4.1.3.2, 4.1.4.2). -/
def DateV.complete : DateV → Bool
  | .ymd .. | .yd .. | .ywd .. => true
  | _ => false

/-- A time point exists if its date and time of day do.

OPEN (ledger X680-14): Table 6 refers "Basic=Date-Time" to ISO 8601 4.3, where the date is a
complete date, and X.691 Table 2 row 33 lists only the Date settings YMD, YD and YWD for it. X.680
says no more. We take a date and time of day to have a complete date. -/
def PointV.Wf : PointV → Bool
  | .date d => d.Wf
  | .time t => t.Wf
  | .dateTime d t => d.Wf && d.complete && t.Wf

/-- The time elements of a duration, most significant first: years, months, weeks, days, hours,
minutes, seconds (38.3.6.2–38.3.6.4). -/
def DurationV.elems (d : DurationV) : List (Option Nat) :=
  [d.years, d.months, d.weeks, d.days, d.hours, d.minutes, d.seconds]

def DurationV.ofElems (xs : List (Option Nat)) (frac : Digits) : DurationV :=
  ⟨xs.getD 0 none, xs.getD 1 none, xs.getD 2 none, xs.getD 3 none, xs.getD 4 none, xs.getD 5 none,
   xs.getD 6 none, frac⟩

/-- X.680 38.3.6.1: a duration has at least one time element, and a week designation stands alone
(38.2.3 NOTE 2). -/
def DurationV.Wf (d : DurationV) : Bool :=
  d.elems.any Option.isSome &&
  (d.weeks.isSome → [d.years, d.months, d.days, d.hours, d.minutes, d.seconds].all Option.isNone)

/-- The interval's points agree on everything but Midnight (Table 6, the NOTEs to Date, Year, Time,
Local-or-UTC and SE-point). Their time differences may differ (Table 7, "End point component"). -/
def PointV.sameShape (a b : PointV) : Bool :=
  a.basic == b.basic &&
    (a.props.filter (·.1 != "Midnight")) == (b.props.filter (·.1 != "Midnight"))

def IntervalV.Wf : IntervalV → Bool
  | .se a b => a.Wf && b.Wf && a.sameShape b
  | .d du => du.Wf
  | .sd a du | .de du a => a.Wf && du.Wf

/-- X.680 38: the abstract values of TIME. -/
def TimeV.Wf : TimeV → Bool
  | .point p => p.Wf
  | .interval i => i.Wf
  | .recurring _ i => i.Wf

/-! ## One abstract value, many notations -/

/-- Least significant first: the least significant element present stays as it is, and every
zero element above it goes. -/
def dropZerosAbove : List (Option Nat) → List (Option Nat)
  | [] => []
  | none :: r => none :: dropZerosAbove r
  | some x :: r => some x :: r.map fun o => if o = some 0 then none else o

/-- X.680 38.2.3: including or omitting a zero time element that is not the least significant
element of a duration does not change the abstract value (38.3.6.14 EXAMPLE 2). The normal form
omits them, as X.691 32.6.3 does. -/
def DurationV.norm (d : DurationV) : DurationV :=
  .ofElems (dropZerosAbove d.elems.reverse).reverse d.frac

def IntervalV.norm : IntervalV → IntervalV
  | .se a b => .se a b
  | .d du => .d du.norm
  | .sd a du => .sd a du.norm
  | .de du b => .de du.norm b

/-- Two TIME values are the same abstract value iff their normal forms are equal. -/
def TimeV.norm : TimeV → TimeV
  | .point p => .point p
  | .interval i => .interval i.norm
  | .recurring n i => .recurring n i.norm

/-! ## Order (51.11, 51.12, 51.13) -/

/-- Lexicographic order on lists of the same length. -/
def lexLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

def lexLt (as bs : List Int) : Bool := lexLe as bs && !lexLe bs as

def DateV.key : DateV → List Int
  | .c k => [k] | .y k => [k] | .ym k m => [k, m] | .ymd k m dy => [k, m, dy] | .yd k dy => [k, dy]
  | .yw k w => [k, w] | .ywd k w dy => [k, w, dy]

def TimeOfDayV.key (t : TimeOfDayV) : List Int :=
  [(t.hour : Int), t.minute.getD 0, t.second.getD 0] ++ t.frac.map fun x => (x.val : Int)

/-- The position of a point on its time scale. Points of the same shape (`PointV.sameShape`) have
keys of the same length, so the keys order them; 24:00 on day x comes before 00:00 on day x + 1
(38.2.2 NOTE 1). -/
def PointV.key : PointV → List Int
  | .date d => d.key
  | .time t => t.key
  | .dateTime d t => d.key ++ t.key

def PointV.zone : PointV → Option Zone
  | .date _ => none
  | .time t | .dateTime _ t => some t.zone

/-- X.680 51.12.5: `p` has the settings of the endpoint `a` (Midnight aside) and, for
"Local-or-UTC=LD", the same time difference, and lies between `a` and `b` (51.4). -/
def PointV.between (a : PointV) (aOpen : Bool) (b : PointV) (bOpen : Bool) (p : PointV) : Bool :=
  a.sameShape p && a.zone == p.zone &&
    (if aOpen then lexLt a.key p.key else lexLe a.key p.key) &&
    (if bOpen then lexLt p.key b.key else lexLe p.key b.key)

/-- The index of the least significant time element present. -/
def DurationV.last (d : DurationV) : Nat :=
  (d.elems.zipIdx.filter (·.1.isSome)).getLast?.map (·.2) |>.getD 0

/-- Each element's value, an absent element counting as zero (38.2.3). -/
def DurationV.vec (d : DurationV) : List Int := d.elems.map fun o => (o.getD 0 : Int)

/-- X.680 51.11.4: `x` has the same values as the endpoints for the elements above the least
significant one, the same least significant element to the same accuracy, and lies between the
endpoints in it. The endpoints must agree above it (51.11.3), so `a` stands for both there.

Elements above the least significant one are compared with zero standing for an absent element,
since including or omitting a zero element does not change the abstract value (38.2.3). -/
def DurationV.between (a : DurationV) (aOpen : Bool) (b : DurationV) (bOpen : Bool) (x : DurationV) :
    Bool :=
  let l := a.last
  let key (d : DurationV) : List Int := (d.vec.getD l 0) :: d.frac.map (·.val)
  x.last == l && x.frac.length == a.frac.length && x.vec.take l == a.vec.take l &&
    (if aOpen then lexLt (key a) (key x) else lexLe (key a) (key x)) &&
    (if bOpen then lexLt (key x) (key b) else lexLe (key x) (key b))

/-! ## Value notation (38.3)

`parse` reads the contents of a "tstring" (38.3.2), that is, the notation without its quotation
marks. It accepts every notation that 38.3 and Table 7 allow for some arrangement of components,
including those whose components are out of range; `TimeV.Wf` says which of those are values. -/

namespace Notation

/-- A parser: what it read, and the rest of the input. -/
abbrev P (α : Type) := List Char → Option (α × List Char)

def digit? (c : Char) : Option Nat := if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- One or more digits, as many as there are. -/
def digits (s : List Char) : Option (List Nat × List Char) :=
  let ds := s.takeWhile Char.isDigit
  if ds = [] then none else some (ds.map (·.toNat - '0'.toNat), s.drop ds.length)

def decOf (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

def toDigits (ds : List Nat) : Digits := ds.map fun d => ⟨d % 10, Nat.mod_lt _ (by decide)⟩

/-- The next `n` characters, which are digits, as a number. -/
def digitsN (n : Nat) (s : List Char) : Option (Nat × List Char) :=
  let ds := s.take n
  if ds.length = n ∧ ds.all Char.isDigit then some (decOf (ds.map (·.toNat - '0'.toNat)), s.drop n)
  else none

/-- Table 7, "Decimal fraction component": a comma or full stop and one or more digits; or nothing. -/
def frac (s : List Char) : Digits × List Char :=
  match s with
  | c :: r => if c = ',' ∨ c = '.' then
      match digits r with
      | some (ds, r') => (toDigits ds, r')
      | none => ([], s)
    else ([], s)
  | [] => ([], s)

/-- A year or a century (Table 7, "Year component"): `inl` a year, `inr` a century.
- "Year=Basic" or "Year=Proleptic": [YYYY], or [YYC] for a century;
- "Year=Negative": [−YYYY], or [−YYC];
- "Year=Ln": [±] and n digits, or [±] and n − 2 digits and [C].
A year that "requires" n digits has no leading zero. -/
def yearOrCentury (s : List Char) : Option ((Int ⊕ Int) × List Char) :=
  match s with
  | c :: r =>
    if c = '+' ∨ c = '-' then
      match digits r with
      | some (ds, r') =>
        let v : Int := if c = '-' then -(decOf ds : Int) else decOf ds
        let neg := c = '-' ∧ decOf ds ≠ 0
        let large (k : Nat) := k ≤ ds.length ∧ ds.head? ≠ some 0
        match r' with
        | 'C' :: r'' => if (neg ∧ ds.length = 2) ∨ large 3 then some (.inr v, r'') else none
        | _ => if (neg ∧ ds.length = 4) ∨ large 5 then some (.inl v, r') else none
      | none => none
    else
      match digits s with
      | some (ds, r') =>
        match r' with
        | 'C' :: r'' => if ds.length = 2 then some (.inr (decOf ds), r'') else none
        | _ => if ds.length = 4 then some (.inl (decOf ds), r') else none
      | none => none
  | [] => none

/-- A date (Table 7: year, then [-MM] and [-DD], or [-DDD], or [-Www] and [-D]). -/
def date (s : List Char) : Option (DateV × List Char) :=
  match yearOrCentury s with
  | some (.inr c, r) => some (.c c, r)
  | some (.inl y, r) =>
    match r with
    | '-' :: 'W' :: r' =>
      match digitsN 2 r' with
      | some (w, '-' :: r'') => (digitsN 1 r'').map fun (d, r3) => (.ywd y w d, r3)
      | some (w, r'') => some (.yw y w, r'')
      | none => none
    | '-' :: r' =>
      match digits r' with
      | some (ds, r'') =>
        if ds.length = 3 then some (.yd y (decOf ds), r'')
        else if ds.length = 2 then
          match r'' with
          | '-' :: r3 => (digitsN 2 r3).map fun (d, r4) => (.ymd y (decOf ds) d, r4)
          | _ => some (.ym y (decOf ds), r'')
        else none
      | none => none
    | _ => some (.y y, r)
  | none => none

/-- Table 7, "UTC designator component" and "Time difference component": [Z], [±hh] or [±hh:mm];
or nothing, for local time of day. -/
def zone (s : List Char) : Option (Zone × List Char) :=
  match s with
  | 'Z' :: r => some (.utc, r)
  | c :: r =>
    if c = '+' ∨ c = '-' then
      let sgn : Int := if c = '-' then -1 else 1
      match digitsN 2 r with
      | some (h, ':' :: r') => (digitsN 2 r').map fun (m, r'') => (.diff (sgn * (60 * h + m)), r'')
      | some (h, r') => some (.diff (sgn * 60 * h), r')
      | none => none
    else some (.local_, s)
  | [] => some (.local_, s)

/-- A time of day: [hh], then [:mm], then [:ss], a decimal fraction of the last, and the zone
(Table 7; 38.3.5: the zone last). -/
def timeOfDay (s : List Char) : Option (TimeOfDayV × List Char) :=
  match digitsN 2 s with
  | some (h, r) =>
    let (mi, r) : Option Nat × List Char := match r with
      | ':' :: r' => match digitsN 2 r' with
        | some (m, r'') => (some m, r'')
        | none => (none, r)
      | _ => (none, r)
    let (se, r) : Option Nat × List Char := match mi, r with
      | some _, ':' :: r' => match digitsN 2 r' with
        | some (x, r'') => (some x, r'')
        | none => (none, r)
      | _, _ => (none, r)
    let (f, r) := frac r
    (zone r).map fun (z, r') => ({ hour := h, minute := mi, second := se, frac := f, zone := z }, r')
  | none => none

/-- A time point: a date, a time of day, or a date, [T] and a time of day (Table 7, "Hours
component"). Two digits alone are an hour, four a year. -/
def point (s : List Char) : Option (PointV × List Char) :=
  match date s with
  | some (d, 'T' :: r) => (timeOfDay r).map fun (t, r') => (.dateTime d t, r')
  | some (d, r) => some (.date d, r)
  | none => (timeOfDay s).map fun (t, r) => (.time t, r)

/-- 38.3.6.11: one or more digits, no leading zero unless the digit zero alone. -/
def designationNumber (s : List Char) : Option (Nat × List Char) :=
  match digits s with
  | some (ds, r) => if ds.length > 1 ∧ ds.head? = some 0 then none else some (decOf ds, r)
  | none => none

/-- 38.3.6.4–38.3.6.10: designations, each a number, perhaps a fraction, and its designator, as
long as the designator is one of `letters`. -/
def designations (letters : List Char) : Nat → List Char → List (Char × Nat × Digits) × List Char
  | 0, s => ([], s)
  | k + 1, s =>
    match designationNumber s with
    | some (v, r) =>
      let (f, r) := frac r
      match r with
      | c :: r' => if c ∈ letters then
          let (more, r'') := designations letters k r'
          ((c, v, f) :: more, r'')
        else ([], s)
      | [] => ([], s)
    | none => ([], s)

/-- 38.3.6.2, 38.3.6.3: the designators appear at most once, in order, and only the last has a
fraction (38.3.6.13). -/
def ordered (order : List Char) (ds : List (Char × Nat × Digits)) : Bool :=
  let idx := ds.map fun (c, _, _) => order.idxOf c
  (idx.zip idx.tail).all (fun (i, j) => i < j) && (ds.dropLast.all fun (_, _, f) => f = [])

/-- 38.3.6: [P], then a year-month-day designation (years, months, days) or a week designation, then
[T] and an hours-mins-secs designation; at least one designation. -/
def duration (s : List Char) : Option (DurationV × List Char) :=
  match s with
  | 'P' :: r =>
    let (dp, r) := designations ['Y', 'M', 'W', 'D'] 4 r
    let (tp, r, hasT) : List (Char × Nat × Digits) × List Char × Bool := match r with
      | 'T' :: r' => let (tp, r'') := designations ['H', 'M', 'S'] 3 r'; (tp, r'', true)
      | _ => ([], r, false)
    let get (ds : List (Char × Nat × Digits)) (c : Char) : Option Nat :=
      (ds.find? (·.1 == c)).map (·.2.1)
    let f := ((dp ++ tp).getLast?.map (·.2.2)).getD []
    if ordered ['Y', 'M', 'W', 'D'] dp && ordered ['H', 'M', 'S'] tp && (hasT → tp ≠ []) &&
        (dp ++ tp ≠ []) && (dp ≠ [] → tp ≠ [] → (dp.getLast?.map (·.2.2)) = some []) then
      some ({ years := get dp 'Y', months := get dp 'M', weeks := get dp 'W', days := get dp 'D',
              hours := get tp 'H', minutes := get tp 'M', seconds := get tp 'S', frac := f }, r)
    else none
  | _ => none

/-- Splits at each solidus. -/
def splitSolidus (s : List Char) : List (List Char) := s.splitOn '/'

/-- A whole time point. -/
def pointAll (s : List Char) : Option PointV :=
  match point s with
  | some (p, []) => some p
  | _ => none

def durationAll (s : List Char) : Option DurationV :=
  match duration s with
  | some (d, []) => some d
  | _ => none

/-- Table 7, "Time interval": start/end, duration, start/duration, duration/end. The end point may
omit its time difference when it is the start point's (Table 7, "End point component"). -/
def interval : List (List Char) → Option IntervalV
  | [d] => (durationAll d).map .d
  | [a, b] =>
    match a, b with
    | 'P' :: _, _ => do let d ← durationAll a; let e ← pointAll b; pure (.de d e)
    | _, 'P' :: _ => do let p ← pointAll a; let d ← durationAll b; pure (.sd p d)
    | _, _ => do
      let p ← pointAll a
      let e ← pointAll b
      let e := match p.zone, e with
        | some (.diff m), .time t => if t.zone = .local_ then .time { t with zone := .diff m } else e
        | some (.diff m), .dateTime d t =>
          if t.zone = .local_ then .dateTime d { t with zone := .diff m } else e
        | _, _ => e
      pure (.se p e)
  | _ => none

/-- X.680 38.3: the abstract value a "tstring"'s contents denote, if it is one. -/
def parse (s : List Char) : Option TimeV :=
  match splitSolidus s with
  | ('R' :: n) :: rest =>
    let cnt : Option (Option Nat) :=
      if n = [] then some none
      else match digits n with
        | some (ds, []) => some (some (decOf ds))
        | _ => none
    match cnt, interval rest with
    | some k, some i => some (.recurring k i)
    | _, _ => none
  | [p] => match p with
    | 'P' :: _ => (durationAll p).map (.interval ∘ .d)
    | _ => (pointAll p).map .point
  | parts => (interval parts).map .interval

end Notation

/-- X.680 38.3.2: `s`, the contents of a "tstring", is value notation for `v`. -/
def TimeV.Notates (s : List Char) (v : TimeV) : Prop :=
  ∃ w, Notation.parse s = some w ∧ w.Wf ∧ w.norm = v.norm

/-! ## GeneralizedTime (46) and UTCTime (47)

Their values are VisibleString values in a format (46.3, 47.3). These read the format. -/

namespace Notation

/-- X.680 46.3: [YYYYMMDD] (ISO 8601 4.1.2.2 basic format), the time of day [hh], [hhmm] or [hhmmss]
(4.2.2.2, 4.2.2.3), a decimal fraction of the last (4.2.2.4), then nothing (case a), [Z] (case b)
or the time difference [±hh] or [±hhmm] (case c). The result is the date and time of day it
writes, with Year ignored: GeneralizedTime has four-digit years. -/
def generalizedTime (s : List Char) : Option (DateV × TimeOfDayV) := do
  let (y, r) ← digitsN 4 s
  let (mo, r) ← digitsN 2 r
  let (d, r) ← digitsN 2 r
  let (h, r) ← digitsN 2 r
  let (mi, r) : Option Nat × List Char := match digitsN 2 r with
    | some (m, r') => (some m, r')
    | none => (none, r)
  let (se, r) : Option Nat × List Char := match mi, digitsN 2 r with
    | some _, some (x, r') => (some x, r')
    | _, _ => (none, r)
  let (f, r) := frac r
  let (z, r) ← match r with
    | 'Z' :: r' => some (Zone.utc, r')
    | c :: r' =>
      if c = '+' ∨ c = '-' then
        let sgn : Int := if c = '-' then -1 else 1
        match digitsN 2 r' with
        | some (zh, r'') => match digitsN 2 r'' with
          | some (zm, r3) => if zh ≤ 23 ∧ zm ≤ 59 then some (.diff (sgn * (60 * zh + zm)), r3) else none
          | none => if zh ≤ 23 then some (.diff (sgn * 60 * zh), r'') else none
        | none => none
      else none
    | [] => some (.local_, [])
  if r = [] then some (.ymd y mo d, { hour := h, minute := mi, second := se, frac := f, zone := z })
  else none

/-- X.680 46.2, 46.3: a calendar date, and a time of day that is not midnight at the end of a day
(46.2 a)): hours 00 to 23, minutes 00 to 59, seconds 00 to 60 (ISO 8601 4.2.1, a leap second). The
time difference is in hours 00 to 23 and minutes 00 to 59, as ISO 8601 4.2.5.1 writes it. -/
def generalizedTimeOk (s : List Char) : Bool :=
  match generalizedTime s with
  | some (d, t) => d.Wf && t.hour ≤ 23 && t.minute.all (· ≤ 59) && t.second.all (· ≤ 60)
  | none => false

/-- X.680 47.3: [YYMMDD], [hhmm] or [hhmmss], then [Z] or [±hhmm]. -/
def utcTime (s : List Char) : Option (Nat × Nat × Nat × Nat × Nat × Option Nat × Zone) := do
  let (yy, r) ← digitsN 2 s
  let (mo, r) ← digitsN 2 r
  let (d, r) ← digitsN 2 r
  let (h, r) ← digitsN 2 r
  let (mi, r) ← digitsN 2 r
  let (se, r) : Option Nat × List Char := match digitsN 2 r with
    | some (x, r') => (some x, r')
    | none => (none, r)
  match r with
  | ['Z'] => some (yy, mo, d, h, mi, se, .utc)
  | c :: r' =>
    if c = '+' ∨ c = '-' then
      let sgn : Int := if c = '-' then -1 else 1
      match digitsN 2 r' with
      | some (zh, r'') => match digitsN 2 r'' with
        | some (zm, []) => if zh ≤ 23 ∧ zm ≤ 59 then some (yy, mo, d, h, mi, se, .diff (sgn * (60 * zh + zm)))
                           else none
        | _ => none
      | none => none
    else none
  | [] => none

/-- X.680 47.3 a)–c): MM 01 to 12, DD 01 to 31, hh 00 to 23, mm 00 to 59, ss 00 to 59.

OPEN (ledger X680-15): 47.3 a) bounds DD by 31, not by the month's length; we take it as written. -/
def utcTimeOk (s : List Char) : Bool :=
  match utcTime s with
  | some (_, mo, d, h, mi, se, _) =>
    1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ 31 && h ≤ 23 && mi ≤ 59 && se.all (· ≤ 59)
  | none => false

end Notation

/-! ## Property settings as written (51.10.3, 51.10.4, Table 13) -/

/-- Table 6, column 1: the property names. -/
def propertyNames : List String :=
  ["Basic", "Date", "Year", "Time", "Local-or-UTC", "Interval-type", "SE-point", "Recurrence",
   "Midnight"]

/-- `s` is the prefix followed by a positive decimal number of at least `min`. -/
def numbered (pre : String) (min : Nat) (s : String) : Bool :=
  s.startsWith pre &&
    match (s.drop pre.length).toNat? with
    | some k => min ≤ k && (s.drop pre.length).toString.all Char.isDigit
    | none => false

/-- Table 6, column 2: the settings of a property. -/
def settingOk : String → String → Bool
  | "Basic", s => s ∈ ["Date", "Time", "Date-Time", "Interval", "Rec-Interval"]
  | "Date", s => s ∈ ["C", "Y", "YM", "YMD", "YD", "YW", "YWD"]
  | "Year", s => s ∈ ["Basic", "Proleptic", "Negative"] || numbered "L" 5 s
  | "Time", s => s ∈ ["H", "HM", "HMS"] || numbered "HF" 1 s || numbered "HMF" 1 s ||
      numbered "HMSF" 1 s
  | "Local-or-UTC", s => s ∈ ["L", "Z", "LD"]
  | "Interval-type", s => s ∈ ["SE", "D", "SD", "DE"]
  | "SE-point", s => s ∈ ["Date", "Time", "Date-Time"]
  | "Recurrence", s => s == "Unlimited" || numbered "R" 1 s
  | "Midnight", s => s ∈ ["Start", "End"]
  | _, _ => false

/-- X.680 51.10.6, Table 13: the property names a Basic setting prohibits. -/
def prohibitedWith : String → List String
  | "Date" => ["Time", "Local-or-UTC", "Midnight", "Interval-type", "SE-point", "Recurrence"]
  | "Time" => ["Date", "Year", "Interval-type", "SE-point", "Recurrence"]
  | "Date-Time" => ["Interval-type", "SE-point", "Recurrence"]
  | "Interval" => ["Recurrence"]
  | _ => []

/-- X.680 51.10.3, 51.10.4, 51.10.6: a "PropertySettingsList" is well formed. -/
def settingsOk (ps : List (String × String)) : Bool :=
  (ps.map (·.1)).Nodup && ps.all (fun (p, s) => p ∈ propertyNames && settingOk p s) &&
    match ps.find? (·.1 == "Basic") with
    | some (_, b) => ps.all fun (p, _) => p ∉ prohibitedWith b
    | none => true

/-! ## The useful time types (38.4) -/

/-- X.680 38.4.1: DATE is TIME (SETTINGS "Basic=Date Date=YMD Year=Basic"). -/
def dateSettings : List (String × String) := [("Basic", "Date"), ("Date", "YMD"), ("Year", "Basic")]

/-- X.680 38.4.2: TIME-OF-DAY is TIME (SETTINGS "Basic=Time Time=HMS Local-or-UTC=L"). -/
def timeOfDaySettings : List (String × String) :=
  [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "L")]

/-- X.680 38.4.3: DATE-TIME is TIME (SETTINGS "Basic=Date-Time Date=YMD Year=Basic Time=HMS
Local-or-UTC=L"). -/
def dateTimeSettings : List (String × String) :=
  [("Basic", "Date-Time"), ("Date", "YMD"), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "L")]

/-- X.680 38.4.4: DURATION is TIME (SETTINGS "Basic=Interval Interval-type=D"). -/
def durationSettings : List (String × String) := [("Basic", "Interval"), ("Interval-type", "D")]

end Asn1.X680
