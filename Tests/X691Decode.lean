import Asn1.Parse.Values
import Asn1.X691.Decode

/-! The PER decoder (`Asn1/X691/Decode.lean`) on the worked examples of X.691 Annex A (A.1–A.4), in
all four variants: each complete encoding the standard prints decodes, as BASIC-PER and as
CANONICAL-PER (every value there is canonical), to the value Annex A gives. -/

open Asn1 Asn1.Parse Asn1.X680 Asn1.X691

namespace Asn1.X691.DecodeTest

def hexOctets (s : String) : Octets :=
  let ds := (s.toList.filter fun c => c.isDigit || ('A' ≤ c && c ≤ 'F')).map fun c =>
    if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
  let rec go : List Nat → Octets
    | a :: b :: r => octet (16 * a + b) :: go r
    | _ => []
  go ds

def envOf (src : String) : Env := match parseModules src with
  | .ok ms => (readValues (resolveAll ms).1).1
  | .error _ => []

def run (src typ hex : String) (v : Variant) : String :=
  let E := envOf src
  match E.head? with
  | some m => match decode E v 400 m (.ref typ) (hexOctets hex) with
    | .ok x => X690.showVal x
    | .error e => "REJECT " ++ e
  | none => "no module"

def AL : Variant := ⟨true, false⟩
def UN : Variant := ⟨false, false⟩
def CAL : Variant := ⟨true, true⟩
def CUN : Variant := ⟨false, true⟩

def a1 : String := "A1 DEFINITIONS ::= BEGIN\nPersonnelRecord ::= [APPLICATION 0] IMPLICIT SET {\n  name Name, title [0] VisibleString, number EmployeeNumber, dateOfHire [1] Date,\n  nameOfSpouse [2] Name, children [3] IMPLICIT SEQUENCE OF ChildInformation DEFAULT {} }\nChildInformation ::= SET { name Name, dateOfBirth [0] Date}\nName ::= [APPLICATION 1] IMPLICIT SEQUENCE { givenName VisibleString, initial VisibleString, familyName VisibleString}\nEmployeeNumber ::= [APPLICATION 2] IMPLICIT INTEGER\nDate ::= [APPLICATION 3] IMPLICIT VisibleString\nEND\n"
def a2 : String := "A2 DEFINITIONS ::= BEGIN\nPersonnelRecord ::= [APPLICATION 0] IMPLICIT SET {\n  name Name, title [0] VisibleString, number EmployeeNumber, dateOfHire [1] Date,\n  nameOfSpouse [2] Name, children [3] IMPLICIT SEQUENCE OF ChildInformation DEFAULT {} }\nChildInformation ::= SET { name Name, dateOfBirth [0] Date}\nName ::= [APPLICATION 1] IMPLICIT SEQUENCE { givenName NameString, initial NameString (SIZE(1)), familyName NameString}\nEmployeeNumber ::= [APPLICATION 2] IMPLICIT INTEGER\nDate ::= [APPLICATION 3] IMPLICIT VisibleString (FROM(\"0\"..\"9\") ^ SIZE(8))\nNameString ::= VisibleString (FROM(\"a\"..\"z\" | \"A\"..\"Z\" | \"-.\") ^ SIZE(1..64))\nEND\n"
def a3 : String := "A3 DEFINITIONS ::= BEGIN\nPersonnelRecord ::= [APPLICATION 0] IMPLICIT SET {\n  name Name, title [0] VisibleString, number EmployeeNumber, dateOfHire [1] Date,\n  nameOfSpouse [2] Name, children [3] IMPLICIT SEQUENCE (SIZE(2, ...)) OF ChildInformation OPTIONAL, ... }\nChildInformation ::= SET { name Name, dateOfBirth [0] Date, ..., sex [1] IMPLICIT ENUMERATED {male(1), female(2), unknown(3)} OPTIONAL }\nName ::= [APPLICATION 1] IMPLICIT SEQUENCE { givenName NameString, initial NameString (SIZE(1)), familyName NameString, ... }\nEmployeeNumber ::= [APPLICATION 2] IMPLICIT INTEGER (0..9999, ...)\nDate ::= [APPLICATION 3] IMPLICIT VisibleString (FROM(\"0\"..\"9\") ^ SIZE(8, ..., 9..20))\nNameString ::= VisibleString (FROM(\"a\"..\"z\" | \"A\"..\"Z\" | \"-.\") ^ SIZE(1..64, ...))\nEND\n"
def a4 : String := "A4 DEFINITIONS AUTOMATIC TAGS ::= BEGIN\nAx ::= SEQUENCE { a INTEGER (250..253), b BOOLEAN,\n  c CHOICE { d INTEGER, ..., [[ e BOOLEAN, f IA5String ]], ... },\n  ..., [[ g NumericString (SIZE(3)), h BOOLEAN OPTIONAL ]], ...,\n  i BMPString OPTIONAL, j PrintableString OPTIONAL }\nEND\n"

def a1Val : String := "{ name { givenName \"John\", initial \"P\", familyName \"Smith\" }, number 51, title \"Director\", dateOfHire \"19710917\", nameOfSpouse { givenName \"Mary\", initial \"T\", familyName \"Smith\" }, children { { name { givenName \"Ralph\", initial \"T\", familyName \"Smith\" }, dateOfBirth \"19571111\" }, { name { givenName \"Susan\", initial \"B\", familyName \"Jones\" }, dateOfBirth \"19590717\" } } }"
#guard run a1 "PersonnelRecord" "80044A6F686E015005536D6974680133084469726563746F72083139373130393137044D617279015405536D697468020552616C7068015405536D69746808313935373131313105537573616E0142054A6F6E6573083139353930373137" AL = a1Val
#guard run a1 "PersonnelRecord" "80044A6F686E015005536D6974680133084469726563746F72083139373130393137044D617279015405536D697468020552616C7068015405536D69746808313935373131313105537573616E0142054A6F6E6573083139353930373137" CAL = a1Val
#guard run a1 "PersonnelRecord" "824ADFA3700D005A7B74F4D0026611134F2CB8FA6FE410C5CB762C1CB16E09370F2F20350169EDD3D340102D2C3B386801A80B4F6E9E9A0218B96ADD8B162C4169F5E787700C20595BF765E610C5CB572C1BB16E" UN = a1Val
#guard run a1 "PersonnelRecord" "824ADFA3700D005A7B74F4D0026611134F2CB8FA6FE410C5CB762C1CB16E09370F2F20350169EDD3D340102D2C3B386801A80B4F6E9E9A0218B96ADD8B162C4169F5E787700C20595BF765E610C5CB572C1BB16E" CUN = a1Val
def a2Val : String := "{ name { givenName \"John\", initial \"P\", familyName \"Smith\" }, number 51, title \"Director\", dateOfHire \"19710917\", nameOfSpouse { givenName \"Mary\", initial \"T\", familyName \"Smith\" }, children { { name { givenName \"Ralph\", initial \"T\", familyName \"Smith\" }, dateOfBirth \"19571111\" }, { name { givenName \"Susan\", initial \"B\", familyName \"Jones\" }, dateOfBirth \"19590717\" } } }"
#guard run a2 "PersonnelRecord" "864A6F686E5010536D6974680133084469726563746F72197109170C4D6172795410536D697468021052616C70685410536D6974681957111110537573616E42104A6F6E657319590717" AL = a2Val
#guard run a2 "PersonnelRecord" "864A6F686E5010536D6974680133084469726563746F72197109170C4D6172795410536D697468021052616C70685410536D6974681957111110537573616E42104A6F6E657319590717" CAL = a2Val
#guard run a2 "PersonnelRecord" "865D51D2888A5125F180998444D3CB2E3E9BF90CB8848B867396E8A88A5125F181089B93D71AA2294497C632AE222222985CE521885D54C170CAC838B8" UN = a2Val
#guard run a2 "PersonnelRecord" "865D51D2888A5125F180998444D3CB2E3E9BF90CB8848B867396E8A88A5125F181089B93D71AA2294497C632AE222222985CE521885D54C170CAC838B8" CUN = a2Val
def a3Val : String := "{ name { givenName \"John\", initial \"P\", familyName \"Smith\" }, number 51, title \"Director\", dateOfHire \"19710917\", nameOfSpouse { givenName \"Mary\", initial \"T\", familyName \"Smith\" }, children { { name { givenName \"Ralph\", initial \"T\", familyName \"Smith\" }, dateOfBirth \"19571111\" }, { name { givenName \"Susan\", initial \"B\", familyName \"Jones\" }, dateOfBirth \"19590717\", sex female } } }"
#guard run a3 "PersonnelRecord" "40C04A6F686E5008536D697468000033084469726563746F720019710917034D6172795408536D697468010052616C70685408536D69746800195711118200537573616E42084A6F6E65730019590717010140" AL = a3Val
#guard run a3 "PersonnelRecord" "40C04A6F686E5008536D697468000033084469726563746F720019710917034D6172795408536D697468010052616C70685408536D69746800195711118200537573616E42084A6F6E65730019590717010140" CAL = a3Val
#guard run a3 "PersonnelRecord" "40CBAA3A5108A5125F180330889A7965C7D37F20CB8848B819CE5BA2A114A24BE30113727AE3542294497C619571111822985CE521842EAA60B832B20E2E020280" UN = a3Val
#guard run a3 "PersonnelRecord" "40CBAA3A5108A5125F180330889A7965C7D37F20CB8848B819CE5BA2A114A24BE30113727AE3542294497C619571111822985CE521842EAA60B832B20E2E020280" CUN = a3Val
def a4Val : String := "{ a 253, b true, c e : true, g \"123\", h true }"
#guard run a4 "Ax" "9E000180010291A4" AL = a4Val
#guard run a4 "Ax" "9E000180010291A4" CAL = a4Val
#guard run a4 "Ax" "9E000600040A4690" UN = a4Val
#guard run a4 "Ax" "9E000600040A4690" CUN = a4Val

-- 11.1: an octet after the complete encoding, and a padding bit that is not zero, are rejected
#guard (run a4 "Ax" "9E000180010291A400" AL).startsWith "REJECT"
#guard (run a4 "Ax" "9E000180010291A5" AL).startsWith "REJECT"

end Asn1.X691.DecodeTest
