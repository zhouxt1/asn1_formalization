import Asn1.Parse.Values
import Asn1.X680.Checker

/-! The front end and the validity rules together, on ASN.1 text. -/

open Asn1.Parse Asn1.X680

/-- ASN.1 text, read and checked: the rules broken, by assignment. -/
def broken (src : String) : List String :=
  match parseModules src with
  | .ok ms =>
    let (E, _) := readValues (resolveAll ms).1
    (checkEnv E 60).map (·.name)
  | .error e => ["parse error: " ++ e]

def bad : String := "
Bad DEFINITIONS ::= BEGIN
  DupNames ::= SEQUENCE { a INTEGER, a BOOLEAN }
  DupTags ::= CHOICE { a INTEGER, b INTEGER }
  SetTags ::= SET { a [0] INTEGER, b [0] BOOLEAN }
  OptRun ::= SEQUENCE { a [1] INTEGER OPTIONAL, b [1] BOOLEAN }
  ImplicitChoice ::= [2] IMPLICIT CHOICE { x INTEGER, y BOOLEAN }
  Nested ::= SET { a INTEGER, b CHOICE { c BOOLEAN, ... }, d CHOICE { e REAL, ... } }
  EnumDup ::= ENUMERATED { x(1), y(1) }
  NamedDup ::= INTEGER { one(1), uno(1) }
  Unknown ::= SEQUENCE { a Missing }
  Good ::= SEQUENCE { a [0] INTEGER OPTIONAL, b [1] BOOLEAN, c CHOICE { x [2] NULL, y [3] NULL } }
  Twice ::= INTEGER
  Twice ::= BOOLEAN
END"

-- every rule broken is found, and nothing in Good
#guard broken bad = ["", "DupNames", "DupTags", "SetTags", "OptRun", "ImplicitChoice", "Nested",
  "EnumDup", "NamedDup", "Unknown"]

-- X.680 52.8.1 is legal, and 52.8.3's SET is in an AUTOMATIC TAGS module
#guard broken "M DEFINITIONS ::= BEGIN A ::= SET { a INTEGER, b CHOICE { c BOOLEAN, d NULL, ... } } END" = []
#guard broken "M DEFINITIONS AUTOMATIC TAGS ::= BEGIN
  A ::= SET { a INTEGER, b CHOICE { c BOOLEAN, ... }, d CHOICE { e REAL, ... } } END" = []

/-- Values are read against their governors. -/
def valuesOf (src : String) : List (String × Val) :=
  match parseModules src with
  | .ok ms => ((readValues (resolveAll ms).1).1.flatMap (·.values)).map fun (n, _, v) => (n, v)
  | .error _ => []

#guard (valuesOf "M DEFINITIONS ::= BEGIN
  id-x OBJECT IDENTIFIER ::= { iso member-body(2) 840 }
  id-y OBJECT IDENTIFIER ::= { id-x 7 }
  n INTEGER ::= -5
  e ENUMERATED { red, green } ::= green
  END").length = 4
#guard (match (valuesOf "M DEFINITIONS ::= BEGIN e ENUMERATED { red, green } ::= green END") with
  | [(_, .enum "green")] => true | _ => false)
#guard (match (valuesOf "M DEFINITIONS ::= BEGIN x OBJECT IDENTIFIER ::= { iso member-body(2) 840 } END") with
  | [(_, .oid [1, 2, 840])] => true | _ => false)

-- X.680 13.10, 13.11: a module imported under another name, by its object identifier
-- (RFC 5911 imports EnrollmentMessageSyntax-2009 as EnrollmentMessageSyntax)
#guard broken "
A-2009 { iso(1) 3 9 } DEFINITIONS ::= BEGIN T ::= INTEGER END
B DEFINITIONS ::= BEGIN
  IMPORTS T FROM A { iso(1) 3 9 };
  U ::= SEQUENCE { t T }
END" = []
-- without the identifier, the name must match
#guard broken "
A-2009 { iso(1) 3 9 } DEFINITIONS ::= BEGIN T ::= INTEGER END
B DEFINITIONS ::= BEGIN
  IMPORTS T FROM A;
  U ::= SEQUENCE { t T }
END" = ["T (module A not found)", "U"]

-- X.681 11.7, X.680 14.1: an object or object set setting names something that exists
-- (found by differential testing)
#guard broken "
M DEFINITIONS ::= BEGIN
  C1 ::= CLASS { &code INTEGER UNIQUE }
  C2 ::= CLASS { &id INTEGER UNIQUE, &inner C1 OPTIONAL, &Inners C1 OPTIONAL }
  f C2 ::= { &id 1, &inner noSuchObject }
  g C2 ::= { &id 2, &Inners { noSuchObject } }
END" = ["f", "g"]
#guard broken "
M DEFINITIONS ::= BEGIN
  C1 ::= CLASS { &code INTEGER UNIQUE }
  C2 ::= CLASS { &id INTEGER UNIQUE, &inner C1 OPTIONAL, &Inners C1 OPTIONAL }
  a C1 ::= { &code 1 }
  f C2 ::= { &id 1, &inner a, &Inners { a } }
END" = []

-- X.680 25.12, 16.2, 51.5: a DEFAULT or a value assignment's value has a length its SIZE allows
#guard broken "
M DEFINITIONS ::= BEGIN
  o OCTET STRING (SIZE (2)) ::= '0102030405'H
  S ::= SEQUENCE { b BIT STRING (SIZE (4)) DEFAULT '10101'B }
END" = ["S", "o"]
#guard broken "
M DEFINITIONS ::= BEGIN
  o OCTET STRING (SIZE (2)) ::= '0102'H
  S ::= SEQUENCE { b BIT STRING (SIZE (4)) DEFAULT '1010'B }
  -- with a NamedBitList the encoding rules may add trailing 0 bits (X.680 22), so a shorter value is not rejected
  T ::= SEQUENCE { b BIT STRING { a(0), d(3) } (SIZE (4)) DEFAULT '10'B }
END" = []

-- found by mutation testing: clauses a front end must enforce
-- X.680 25.14, 20.2, 19.5, 22.4: the rules for types hold in the type of a value assignment too
#guard broken "
M DEFINITIONS ::= BEGIN
  v1 SEQUENCE { a INTEGER, b BOOLEAN } ::= { a 1, b TRUE }
  v2 ENUMERATED { x, x } ::= x
  v3 INTEGER { one(1), uno(1) } ::= 1
END" = ["v2", "v3"]
-- X.680 51.4.2, 51.5.2, 51.7.2: a constraint applies to the types it is defined for
#guard broken "
M DEFINITIONS ::= BEGIN
  A ::= INTEGER (SIZE (1..4))
  B ::= BOOLEAN (1..5)
  C ::= OCTET STRING (FROM (\"a\"))
  D ::= OCTET STRING (SIZE (1..4))
  E ::= IA5String (FROM (\"a\"..\"z\") ^ SIZE (1..4))
  F ::= INTEGER (1..5)
  G ::= SEQUENCE SIZE (1..4) OF INTEGER
END" = ["A", "B", "C"]
-- X.680 31.2.5: no UNIVERSAL class tag
#guard broken "
M DEFINITIONS ::= BEGIN
  A ::= [UNIVERSAL 40] IMPLICIT INTEGER
  B ::= [APPLICATION 40] IMPLICIT INTEGER
END" = ["A"]
-- X.680 51.8.10.1: PRESENT and ABSENT only on a component marked OPTIONAL
#guard broken "
M DEFINITIONS ::= BEGIN
  S ::= SEQUENCE { a INTEGER, b BOOLEAN OPTIONAL }
  P1 ::= S (WITH COMPONENTS { ..., a PRESENT })
  P2 ::= S (WITH COMPONENTS { ..., b PRESENT })
END" = ["P1"]
-- X.680 13.1: SymbolList is comma-separated; 20.1: a comma before the ellipsis
#guard (broken "M DEFINITIONS ::= BEGIN EXPORTS A B; A ::= INTEGER B ::= INTEGER END") != []
#guard (broken "M DEFINITIONS ::= BEGIN EXPORTS A, , B; A ::= INTEGER B ::= INTEGER END") != []
#guard (broken "M DEFINITIONS ::= BEGIN EXPORTS A, B; A ::= INTEGER B ::= INTEGER END") = []
#guard (broken "M DEFINITIONS ::= BEGIN E ::= ENUMERATED { a, b ..., c } END") != []
#guard (broken "M DEFINITIONS ::= BEGIN E ::= ENUMERATED { a, b, ..., c } END") = []
-- X.680 13.8, 13.17, 32.3: the object identifier of a module, and an AssignedIdentifier, are well formed
#guard (broken "M { Joint-iso-itu-t 230 } DEFINITIONS ::= BEGIN A ::= INTEGER END") != []
#guard (broken "M { joint-iso-itu-t 230 } DEFINITIONS ::= BEGIN A ::= INTEGER END") = []
#guard (broken "M DEFINITIONS ::= BEGIN IMPORTS B FROM N { itu-t- 4 }; A ::= INTEGER END") != []
#guard (broken "N { itu-t 4 } DEFINITIONS ::= BEGIN B ::= INTEGER END M DEFINITIONS ::= BEGIN IMPORTS B FROM N { itu-t 4 }; A ::= B END") = []

-- found by fuzzing (AFL++): references that name nothing
-- X.683 8.3: the class that governs a parameter exists
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE }
  P { NoSuchClass : S } ::= SEQUENCE { a INTEGER } (CONSTRAINED BY { S })
  Q { C : S } ::= SEQUENCE { a C.&id ({S}) }
END" = ["P"]
-- X.681 14.1, Annex C, 9.14: `X.&f` and `INSTANCE OF X` name a class, and X has the field
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE, &T }
  A ::= SEQUENCE { a NoSuchClass.&T }
  B ::= SEQUENCE { a C.&nosuch }
  D ::= INSTANCE OF NoSuchClass
  E ::= SEQUENCE { a C.&T, b TYPE-IDENTIFIER.&Type }
END" = ["A", "B", "D"]
-- X.681 9.4: a field of a class definition names a class or type that exists
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE, &inner NoSuchClass OPTIONAL }
  D ::= CLASS { &id INTEGER UNIQUE, &inner C OPTIONAL }
END" = ["C"]
-- X.683 9.2: an actual parameter that is a value names one (an enumeration item does)
#guard broken "M DEFINITIONS ::= BEGIN
  P {ELEM, INTEGER : b} ::= SEQUENCE { x ELEM, y INTEGER (0..b) }
  E ::= ENUMERATED { one, two }
  Q {E : e} ::= SEQUENCE { x E DEFAULT e }
  A ::= P {INTEGER, noSuchValue}
  B ::= P {INTEGER, 5}
END" = ["A"]
-- X.683 8.3: the body of a parameterized type names types and classes that exist
#guard broken "M DEFINITIONS ::= BEGIN
  P {ELEM} ::= SEQUENCE { x ELEM, y NoSuchType }
  Q {ELEM} ::= SEQUENCE { x ELEM }
END" != []
-- X.680 51.8: WITH COMPONENTS applies to SEQUENCE, SET and CHOICE (and REAL), WITH COMPONENT to SEQUENCE OF and SET OF
#guard broken "M DEFINITIONS ::= BEGIN
  A ::= INTEGER (WITH COMPONENTS { a PRESENT })
  S ::= SEQUENCE OF INTEGER
  B ::= S (WITH COMPONENT (1..5))
  C ::= INTEGER (WITH COMPONENT (1..5))
  D ::= REAL (WITH COMPONENTS { ..., base (10) })
END" = ["A", "C"]
-- X.680 53.1: an exception specification names something
#guard (broken "M DEFINITIONS ::= BEGIN C ::= CHOICE { a INTEGER, ... ! , b BOOLEAN } END") != []
#guard (broken "M DEFINITIONS ::= BEGIN C ::= CHOICE { a INTEGER, ... ! 5 , b BOOLEAN } END") = []
-- a REAL with an exponent beyond what a rational can hold is left unread, not a panic (found by AFL++)
#guard broken "M DEFINITIONS ::= BEGIN
  a REAL ::= 3.0E99999999999999999999
  b REAL ::= { mantissa -1, base 10, exponent 9223372036854775808 }
END" = []
-- X.680 Table 11: no value range, SIZE or FROM on EXTERNAL or EMBEDDED PDV; SIZE on CHARACTER STRING (found by AFL++)
#guard broken "M DEFINITIONS ::= BEGIN
  A ::= EXTERNAL (SIZE (2))
  B ::= EMBEDDED PDV (SIZE (2))
  C ::= CHARACTER STRING (SIZE (2))
  D ::= EXTERNAL (1..5)
  E ::= EXTERNAL (FROM (\"a\"))
  F ::= EXTERNAL (WITH COMPONENTS { ..., identification PRESENT })
END" = ["A", "B", "D", "E"]
-- X.681 9.8, 9.10: `&v &T` names a type field of the same class (found by AFL++)
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE, &Type, &dflt &Nope OPTIONAL }
  D ::= CLASS { &id INTEGER UNIQUE, &Type, &dflt &Type OPTIONAL }
  E ::= CLASS { &id INTEGER UNIQUE, &Type, &S &Nope OPTIONAL }
END" = ["C", "E"]
-- X.683 9.2: a type written as an actual parameter obeys the rules of a type (found by AFL++)
#guard broken "M DEFINITIONS ::= BEGIN
  P {ELEM} ::= SEQUENCE { x ELEM }
  A ::= P {OCTET STRING (1..5)}
  B ::= P {INTEGER (SIZE (2))}
  C ::= P {OCTET STRING (SIZE (0..4, ...))}
END" = ["A", "B"]
-- found by fuzzing (AFL++), fixed after it
-- X.683 8.6, 8.10: each dummy is used; the right side is not only a dummy
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { x INTEGER }
  Q {T} ::= T
  R {T} ::= SEQUENCE { x T }
END" = ["P", "Q"]
-- X.680 25.5, 27.2: COMPONENTS OF a sequence (set) type
#guard broken "M DEFINITIONS ::= BEGIN
  S ::= SEQUENCE { COMPONENTS OF INTEGER, b BOOLEAN }
  U ::= SET { COMPONENTS OF S }
  V ::= SEQUENCE { COMPONENTS OF W, c NULL }
  W ::= SEQUENCE { a BOOLEAN }
END" = ["S", "U"]
-- X.681 9.7: one identifier value, one object
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE, &v INTEGER }
  S C ::= { { &id 16, &v 1 } | { &id 16, &v 2 } }
  T C ::= { { &id 16, &v 1 } | { &id 16, &v 1 } | { &id 17, &v 1 } }
END" = ["S"]
-- X.680 C.6.1: a value reference has a value mapping to its governor; 16.2 inside a SEQUENCE value
#guard broken "M DEFINITIONS ::= BEGIN
  c INTEGER ::= d
  d BOOLEAN ::= TRUE
  T ::= INTEGER (0..d)
  s SEQUENCE { a INTEGER (0..5) } ::= { a 9 }
  v VisibleString ::= w
  w IA5String ::= \"a\"
END" = ["T", "c", "s"]
-- the type rules hold in class definitions, objects and parameterized bodies
#guard broken "M DEFINITIONS ::= BEGIN
  C ::= CLASS { &id INTEGER UNIQUE, &level INTEGER (SIZE (1..4)) OPTIONAL, &Type }
  o C ::= { &id 1, &Type SEQUENCE { a INTEGER, a BOOLEAN } }
  P {T} ::= SEQUENCE { x T, y INTEGER (SIZE (1)) }
  R {E} ::= CHOICE { a [0] E, b [0] BOOLEAN }
END" = ["C", "o", "P", "R"]

-- 51.6, Table 11: on an open type, a type in parentheses is a type constraint; with INCLUDES it is a
-- contained subtype, which Table 11 does not allow there
#guard broken "M DEFINITIONS ::= BEGIN C ::= CLASS { &Type } T ::= SEQUENCE { a C.&Type (INCLUDES INTEGER) } END" = ["T"]
#guard broken "M DEFINITIONS ::= BEGIN C ::= CLASS { &Type } T ::= SEQUENCE { a C.&Type (INTEGER) } END" = []
-- 13.7, 13.10: two modules with one name, unless their definitive identifiers differ
#guard moduleNamesTwice [("M", none), ("N", none), ("M", none)] = ["M"]
#guard moduleNamesTwice [("M", some [1, 2, 3]), ("M", none)] = ["M"]
#guard moduleNamesTwice [("M", some [1, 2, 3]), ("M", some [1, 2, 4])] = []

-- X.683 8.5: a parameterized body is valid when some actual parameters make it so. A COMPONENTS OF
-- a dummy brings components the checker does not see, so the rules about all of them are left
-- undecided: with `T` a SEQUENCE { x [1] INTEGER }, the run of `a` ends before `b`, and `x` is a
-- component of the body
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { a [0] INTEGER OPTIONAL, COMPONENTS OF T, b [0] INTEGER }
  S ::= SEQUENCE { x [1] INTEGER }
  U ::= P {S} END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { COMPONENTS OF T } (WITH COMPONENTS { ..., x (1..5) })
  S ::= SEQUENCE { x INTEGER }
  U ::= P {S} END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { a INTEGER, COMPONENTS OF T } (WITH COMPONENTS { a (1), x ABSENT })
  S ::= SEQUENCE { x INTEGER OPTIONAL }
  U ::= P {S} END" = []
-- ... while written out, the same types are checked
#guard broken "M DEFINITIONS ::= BEGIN
  U ::= SEQUENCE { a [0] INTEGER OPTIONAL, b [0] INTEGER } END" = ["U"]
#guard broken "M DEFINITIONS ::= BEGIN
  U ::= SEQUENCE { a INTEGER } (WITH COMPONENTS { ..., x (1..5) }) END" = ["U", "U"]
-- and IMPLICIT on a dummy is still wrong (X.680 31.2.7)
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { a [0] IMPLICIT T }
  U ::= P {INTEGER} END" = ["P"]

-- 50.5: EXCEPT takes the root of each side from the roots, so a SIZE whose constraint has additions
-- excludes only its root sizes from the root
#guard broken "M DEFINITIONS ::= BEGIN
  O ::= OCTET STRING (SIZE (1..10) EXCEPT SIZE (1..2, ..., 3))
  o O ::= '010203'H END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  O ::= OCTET STRING (SIZE (1..10) EXCEPT SIZE (1..2, ..., 3))
  o O ::= '0102'H END" = ["o"]
-- 51.7: FROM permits the characters of the strings its constraint selects: "ab" EXCEPT "b" selects
-- "ab", which has a "b"; and a FROM with additions permits only its root's characters in the root
#guard broken "M DEFINITIONS ::= BEGIN
  S ::= IA5String (FROM (\"ab\" EXCEPT \"b\"))
  s S ::= \"b\" END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  S ::= IA5String (SIZE (1) EXCEPT FROM (\"a\", ..., \"b\"))
  s S ::= \"b\" END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  S ::= IA5String (FROM (\"a\"))
  s S ::= \"b\" END" = ["s"]
-- 51.4.2: only the values in a range are values of the parent: an open end need not be
#guard broken "M DEFINITIONS ::= BEGIN
  T ::= INTEGER (0..10)
  U ::= T (-1<..5)
  V ::= T (0..<11)
  W ::= T (0..11) END" = ["W"]
-- 49.7: a type selects some value; the constraint inside a SIZE need not, where others do
#guard broken "M DEFINITIONS ::= BEGIN
  D ::= OCTET STRING (SIZE (3 ^ 4))
  F ::= OCTET STRING (SIZE (3 ^ 4) | SIZE (1)) END" = ["D"]

-- X.683 8.5: in a parameterized body the checker does not see what the dummies stand for, and decides
-- nothing that depends on it: a selection from a dummy, a field of a dummy class
#guard broken "M DEFINITIONS ::= BEGIN
  P {T} ::= SEQUENCE { a x < T }
  C ::= CHOICE { x INTEGER }
  U ::= P {C} END" = []
#guard broken "M DEFINITIONS ::= BEGIN
  P {C} ::= SET { a C.&id, b INTEGER }
  CL ::= CLASS { &id OBJECT IDENTIFIER }
  U ::= P {CL} END" = []
-- while what does not depend on the dummies is still checked
#guard broken "M DEFINITIONS AUTOMATIC TAGS ::= BEGIN
  P {T} ::= SEQUENCE { a [0] T OPTIONAL, b [0] INTEGER } END" = ["P"]
