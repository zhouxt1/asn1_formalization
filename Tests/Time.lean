import Asn1.X680.Semantics

/-! TIME (X.680 38), its subtype notations (51.10–51.13), GeneralizedTime (46) and UTCTime (47),
checked against X.680's own examples. -/

open Asn1.X680

def tv (s : String) : Option TimeV := Notation.parse s.toList

/-- The value notation denotes a value with exactly these settings. -/
def hasProps (s : String) (ps : List (String × String)) : Bool :=
  match tv s with
  | some v => v.Wf && v.props == ps
  | none => false

/-! ## G.3: value notation and property settings

Each example's comment gives "the settings needed to define a subtype of the TIME type that contains
all similar abstract values". -/

-- G.3.1
#guard hasProps "1985-04-12" [("Basic", "Date"), ("Date", "YMD"), ("Year", "Basic")]
#guard hasProps "1985-102" [("Basic", "Date"), ("Date", "YD"), ("Year", "Basic")]
#guard hasProps "1985-W15-5" [("Basic", "Date"), ("Date", "YWD"), ("Year", "Basic")]
#guard hasProps "1985-W15" [("Basic", "Date"), ("Date", "YW"), ("Year", "Basic")]
#guard hasProps "1985-04" [("Basic", "Date"), ("Date", "YM"), ("Year", "Basic")]
#guard hasProps "1985" [("Basic", "Date"), ("Date", "Y"), ("Year", "Basic")]
#guard hasProps "+11985-04-12" [("Basic", "Date"), ("Date", "YMD"), ("Year", "L5")]
#guard hasProps "-0002-04-12" [("Basic", "Date"), ("Date", "YMD"), ("Year", "Negative")]
#guard hasProps "19C" [("Basic", "Date"), ("Date", "C"), ("Year", "Basic")]

-- G.3.2
#guard hasProps "15:27:46" [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "L")]
#guard hasProps "15:28" [("Basic", "Time"), ("Time", "HM"), ("Local-or-UTC", "L")]
#guard hasProps "15:27:35,5" [("Basic", "Time"), ("Time", "HMSF1"), ("Local-or-UTC", "L")]
#guard hasProps "23:20:30Z" [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "Z")]
#guard hasProps "23Z" [("Basic", "Time"), ("Time", "H"), ("Local-or-UTC", "Z")]
#guard hasProps "15:27:46+01:00" [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "LD")]
#guard hasProps "15:27:46-05:00" [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "LD")]
-- time7: "alternative value notation for the same abstract value" as time6
#guard tv "15:27:46+01" = tv "15:27:46+01:00"

-- G.3.3
#guard hasProps "1985-04-12T10:15:30"
  [("Basic", "Date-Time"), ("Date", "YMD"), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "L")]
#guard hasProps "1985-102T23:50:30Z"
  [("Basic", "Date-Time"), ("Date", "YD"), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "Z")]
#guard hasProps "1985-W14-5T23:50:30"
  [("Basic", "Date-Time"), ("Date", "YWD"), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "L")]
-- date-time2 writes the time difference "+02.00", which Table 7 does not allow (ledger X680-18);
-- with a colon it has the settings given
#guard tv "1985-04-01T01:30:00+02.00" = none
#guard hasProps "1985-04-01T01:30:00+02:00"
  [("Basic", "Date-Time"), ("Date", "YMD"), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "LD")]

-- G.3.4
def dt (d : String) : List (String × String) :=
  [("Date", d), ("Year", "Basic"), ("Time", "HMS"), ("Local-or-UTC", "L")]
#guard hasProps "1985-04-12T23:20:50/1985-06-25T10:30:00"
  ([("Basic", "Interval"), ("Interval-type", "SE"), ("SE-point", "Date-Time")] ++ dt "YMD" ++ dt "YMD")
-- interval2 and interval3 are the same abstract value; their comments say "Local-or-UTC=L", but
-- they have time differences, so "Local-or-UTC=LD" (ledger X680-18)
#guard tv "1985-04-12T12:30:00+02:00/1985-04-12T13:30:00+02:00" =
  tv "1985-04-12T12:30:00+02:00/1985-04-12T13:30:00"
#guard (tv "1985-04-12T12:30:00+02:00/1985-04-12T13:30:00").map
  (·.satisfies [("Local-or-UTC", "LD")]) = some true
#guard hasProps "1985-04-12/1985-06-25"
  [("Basic", "Interval"), ("Interval-type", "SE"), ("SE-point", "Date"), ("Date", "YMD"),
   ("Year", "Basic"), ("Date", "YMD"), ("Year", "Basic")]
#guard hasProps "P2Y10M15DT10H20M30S" [("Basic", "Interval"), ("Interval-type", "D")]
#guard hasProps "P1Y6M" [("Basic", "Interval"), ("Interval-type", "D")]
#guard hasProps "PT72H" [("Basic", "Interval"), ("Interval-type", "D")]
#guard hasProps "1985-04-12T23:20:00/P1Y2M15DT12H"
  ([("Basic", "Interval"), ("Interval-type", "SD"), ("SE-point", "Date-Time")] ++ dt "YMD")
#guard hasProps "P1Y2M15DT12H/1985-04-12T23:20:00"
  ([("Basic", "Interval"), ("Interval-type", "DE"), ("SE-point", "Date-Time")] ++ dt "YMD")

-- G.3.5
#guard hasProps "R15/P2Y10M15DT10H20M30S"
  [("Basic", "Rec-Interval"), ("Recurrence", "R2"), ("Interval-type", "D")]
#guard hasProps "R/P2Y15DT10H20M30S"
  [("Basic", "Rec-Interval"), ("Recurrence", "Unlimited"), ("Interval-type", "D")]
#guard hasProps "R2/P1Y6M" [("Basic", "Rec-Interval"), ("Recurrence", "R1"), ("Interval-type", "D")]
#guard hasProps "R/P1Y2M15DT12H/1985-04-12T23:20:50"
  ([("Basic", "Rec-Interval"), ("Recurrence", "Unlimited"), ("Interval-type", "DE"),
    ("SE-point", "Date-Time")] ++ dt "YMD")

/-! ## Which notations are values -/

-- 38.2.2: midnight at the end of a day, and nothing later
#guard hasProps "24:00:00" [("Basic", "Time"), ("Time", "HMS"), ("Local-or-UTC", "L"), ("Midnight", "End")]
#guard hasProps "00:00" [("Basic", "Time"), ("Time", "HM"), ("Local-or-UTC", "L"), ("Midnight", "Start")]
#guard (tv "24:00:01").map TimeV.Wf = some false
-- ISO 8601: 2020 has 53 weeks (it begins on a Wednesday and is a leap year), 2021 has 52
#guard (tv "2020-W53").map TimeV.Wf = some true
#guard (tv "2021-W53").map TimeV.Wf = some false
#guard (tv "2023-02-29").map TimeV.Wf = some false
#guard (tv "2024-02-29").map TimeV.Wf = some true
#guard (tv "1900-02-29").map TimeV.Wf = some false
#guard (tv "2000-366").map TimeV.Wf = some true
-- 1 January 1985 was a Tuesday, 2015 a Thursday, 2000 a Saturday, 1 AD (year 1) a Monday
#guard [jan1Weekday 1985, jan1Weekday 2015, jan1Weekday 2000, jan1Weekday 1] = [2, 4, 6, 1]
-- 38.2.3 NOTE 2: weeks stand alone; 38.3.6.11: no leading zeros; 38.3.6.13: a fraction is last
#guard (tv "P1W2D").map TimeV.Wf = some false
#guard tv "P01Y" = none
#guard tv "P0.5YT1H" = none
-- Table 6: a time difference of at most 15 hours
#guard (tv "12:00+16:00").map TimeV.Wf = some false
-- Table 6, Year: a five-digit year has a sign, and no leading zero
#guard tv "11985-04-12" = none
#guard tv "+01985-04-12" = none

/-! ## 38.2.3, 38.3.6.14: durations -/

def sameDur (a b : String) : Bool := (tv a).map TimeV.norm == (tv b).map TimeV.norm

-- EXAMPLE 1: different accuracies are different abstract values
#guard !sameDur "P29M" "P29M0D"
#guard !sameDur "P29M0D" "P29MT0S"
#guard !sameDur "P29MT0.00H" "P29MT0.000S"
#guard sameDur "P29M" "P0Y29M"
#guard sameDur "P29MT0S" "P0Y29M0DT0H0M0S"
#guard sameDur "P29MT0.00H" "P0Y29M0DT0,00H"
-- EXAMPLE 2: all the same abstract value
#guard ["P0Y29M0DT0H0.00M", "P0Y29M0DT0.00M", "P0Y29MT0H0.00M", "P0Y29MT0.00M", "P29M0DT0H0.00M",
        "P29M0DT0.00M", "P29MT0H0.00M"].all (sameDur "P29MT0.00M")
-- different elements are different abstract values, whatever their length
#guard !sameDur "P29M" "P2Y5M"

-- 38.4.4.2: the DURATION-EQUIVALENT value of P0Y29M0DT0H0.00M
#guard (match tv "P0Y29M0DT0H0.00M" with
  | some (.interval (.d d)) => some d.equiv
  | _ => none) matches
  some (.seq [("months", .int 29), ("minutes", .int 0),
              ("fractional-part", .seq [("number-of-digits", .int 2), ("fractional-value", .int 0)])])

/-! ## 51.10: property settings -/

-- 51.10.5 EXAMPLE: SETTINGS "Midnight=Start" keeps dates and every time but midnight at the end
#guard (tv "1985-04-12").map (·.satisfies [("Midnight", "Start")]) = some true
#guard (tv "00:00:00").map (·.satisfies [("Midnight", "Start")]) = some true
#guard (tv "12:00:00").map (·.satisfies [("Midnight", "Start")]) = some true
#guard (tv "24:00:00").map (·.satisfies [("Midnight", "Start")]) = some false
-- 38.4: the useful time types
#guard (tv "1985-04-12").map (·.satisfies dateSettings) = some true
#guard (tv "1985-102").map (·.satisfies dateSettings) = some false
#guard (tv "1500-04-12").map (·.satisfies dateSettings) = some false
#guard (tv "15:27:46").map (·.satisfies timeOfDaySettings) = some true
#guard (tv "15:27:46Z").map (·.satisfies timeOfDaySettings) = some false
#guard (tv "1985-04-12T10:15:30").map (·.satisfies dateTimeSettings) = some true
#guard (tv "PT72H").map (·.satisfies durationSettings) = some true
#guard (tv "R/PT72H").map (·.satisfies durationSettings) = some false
-- 51.10.3, 51.10.4, Table 13
#guard settingsOk [("Basic", "Date"), ("Date", "YMD"), ("Year", "Basic")]
#guard settingsOk [("Basic", "Time"), ("Time", "HMSF3"), ("Local-or-UTC", "Z")]
#guard settingsOk [("Year", "L7")]
#guard !settingsOk [("Year", "L4")]
#guard !settingsOk [("Basic", "Date"), ("Time", "HMS")]
#guard !settingsOk [("Basic", "Date"), ("Basic", "Time")]
#guard !settingsOk [("Colour", "Blue")]

/-! ## 51.11–51.13: ranges -/

def inRange (lo hi x : String) : Bool :=
  match tv lo, tv hi, tv x with
  | some (.interval (.d a)), some (.interval (.d b)), some (.interval (.d d)) => a.between false b false d
  | some (.point a), some (.point b), some (.point p) => a.between false b false p
  | _, _, _ => false

-- 51.11.4 EXAMPLE: TIME("PT2M0.000S".."PT2M59.000S"), 2 minutes and 0 to 59 seconds, to a millisecond
#guard inRange "PT2M0.000S" "PT2M59.000S" "PT2M30.500S"
#guard inRange "PT2M0.000S" "PT2M59.000S" "PT0H2M59.000S"
#guard !inRange "PT2M0.000S" "PT2M59.000S" "PT2M30.5S"
#guard !inRange "PT2M0.000S" "PT2M59.000S" "PT3M30.000S"
#guard !inRange "PT2M0.000S" "PT2M59.000S" "PT1H2M30.000S"
#guard !inRange "PT2M0.000S" "PT2M59.000S" "PT2M59.001S"
-- 51.12.4 NOTE: TIME("00:00".."09:00") and TIME("21:00".."24:00")
#guard inRange "00:00" "09:00" "05:30"
#guard !inRange "00:00" "09:00" "05:30:00"
#guard !inRange "00:00" "09:00" "05:30Z"
#guard !inRange "00:00" "09:00" "10:00"
#guard inRange "21:00" "24:00" "24:00"
#guard inRange "21:00" "24:00" "23:59"
-- 51.12.5: the same time difference
#guard inRange "00:00+01" "09:00+01" "05:30+01:00"
#guard !inRange "00:00+01" "09:00+01" "05:30+02"
-- 38.2.2 NOTE 1: 24:00 on day x is before 00:00 on day x + 1
#guard inRange "1985-04-12T24:00" "1985-04-12T24:00" "1985-04-12T24:00"
#guard !inRange "1985-04-13T00:00" "1985-04-14T00:00" "1985-04-12T24:00"
-- 51.13: recurrences, Unlimited above every number
example : TimeInRange (.val (.int 1)) false (.val (.int 10)) false (.recurring (some 7) (.d {})) := by
  simp [TimeInRange, RecAbove, RecBelow]
example : ¬ TimeInRange (.val (.int 1)) false (.val (.int 10)) false (.recurring none (.d {})) := by
  simp [TimeInRange, RecAbove, RecBelow]
example : TimeInRange (.val (.int 1)) false .max false (.recurring none (.d {})) := by
  simp [TimeInRange, RecAbove, RecBelow]

/-! ## 46, 47 -/

-- 46.3 EXAMPLES a)–e)
#guard ["19851106210627.3", "19851106210627.3Z", "19851106210627.3-0500", "198511062106.456",
        "1985110621.14159"].all (Notation.generalizedTimeOk ·.toList)
-- 46.2 a): not midnight at the end of a day; ISO 8601: a real date
#guard !Notation.generalizedTimeOk "19851106240000".toList
#guard !Notation.generalizedTimeOk "19850229120000".toList
-- 47.3 EXAMPLES 1, 2
#guard ["8201021200Z", "8201020700-0500", "0101021200Z", "0101020700-0500", "820102120000Z"].all
  (Notation.utcTimeOk ·.toList)
-- 47.3 c): Z or a time difference is required; a) month 01 to 12
#guard !Notation.utcTimeOk "8201021200".toList
#guard !Notation.utcTimeOk "8213021200Z".toList

/-! ## Through the semantics -/

def M : Module := { name := "M", header := ⟨.explicit, false⟩ }
def H0 : ContentsHook := fun _ _ _ _ _ => True

def date1 : Val := .time (.point (.date (.ymd 1985 4 12)))
def date2 : Val := .time (.point (.date (.yd 1985 102)))

attribute [local simp] sem timeVSet VSet.plain

/-- 38.4.1: DATE contains G.3.1's date1, at any fuel. -/
example (k : Nat) : (sem [M] H0 (k + 1) (.ofModule M) [] .date).all date1 := by
  simp only [sem, timeVSet, VSet.plain, date1]
  exact ⟨_, rfl, by decide, by decide⟩

/-- 38.4.1: but not the ordinal date date2. -/
example (k : Nat) : ¬ (sem [M] H0 (k + 1) (.ofModule M) [] .date).all date2 := by
  simp only [sem, timeVSet, VSet.plain, date2]
  rintro ⟨t, ht, -, hs⟩
  cases ht
  exact absurd hs (by decide)
