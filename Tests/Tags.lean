import Asn1.X680.Tags

/-! Tags, checked against X.680's examples. -/

open Asn1.X680

def U (k : Nat) : Tag := ⟨.universal, k⟩
def C (k : Nat) : Tag := ⟨.context, k⟩
def auto : Module := { name := "A", header := ⟨.automatic, false⟩ }
def expl : Module := { name := "X", header := ⟨.explicit, false⟩ }

def tagsOfEntries (m : Module) (r : List Comp) (e : Option (List ExtAdd)) (r2 : List Comp) :=
  (entryTags [m] 50 (.ofModule m) r e r2).map (·.2)

-- 25.10: root components from 0, extension additions after the largest root number
#guard autoNumber [false, false, true, true] = [0, 1, 2, 3]
#guard autoNumber [true, true] = [0, 1]
-- the root after a second ellipsis is numbered with the root (OPEN X680-10)
#guard autoNumber [false, true, true, false] = [0, 2, 3, 1]

-- an automatically tagged SEQUENCE { a INTEGER, b BOOLEAN, ..., c NULL }
#guard tagsOfEntries auto [.mk "a" (.integer []) .mandatory, .mk "b" .boolean .mandatory]
    (some [.one (.mk "c" .null .optional)]) [] = [some [C 0], some [C 1], some [C 2]]

-- 25.3 NOTE 1: `T ::= SEQUENCE { a INTEGER, b [1] BOOLEAN, c OCTET STRING }` is not automatically
-- tagged, even in an AUTOMATIC TAGS module
#guard tagsOfEntries auto [.mk "a" (.integer []) .mandatory,
    .mk "b" (.tagged (C 1) .default_ .boolean) .mandatory, .mk "c" .octetString .mandatory] none [] =
  [some [U 2], some [C 1], some [U 4]]

-- 29.9 example 1, not AUTOMATIC: `A ::= CHOICE { b B, c NULL }`,
-- `B ::= CHOICE { d [0] NULL, e [1] NULL }`. A's values carry [0], [1] or UNIVERSAL 5.
def ex1 : Module where
  name := "Ex1"
  header := ⟨.explicit, false⟩
  types := [("B", .choice [.mk "d" (.tagged (C 0) .default_ .null),
    .mk "e" (.tagged (C 1) .default_ .null)] none)]
#guard tagsOf [ex1] 50 (.ofModule ex1) (.choice [.mk "b" (.ref "B"), .mk "c" .null] none) = some [C 0, C 1, U 5]

-- 13.19: the same, with B imported from another module
def ex1b : Module := { name := "Ex1b", header := ⟨.explicit, false⟩, imports := [("B", "Ex1")] }
#guard tagsOf [ex1, ex1b] 50 (.ofModule ex1b) (.choice [.mk "b" (.ref "B"), .mk "c" .null] none) =
  some [C 0, C 1, U 5]

-- X.681 14.2 NOTE 2: an open type's tag is indeterminate
#guard tagsOf [expl] 50 (.ofModule expl) .openType = none

-- 31.2.7: in an AUTOMATIC or IMPLICIT module, a tag on an untagged CHOICE is explicit, and on
-- anything else implicit; in an EXPLICIT module it is explicit
#guard isExplicit [auto] 50 (.ofModule auto) .default_ (.choice [] none) = true
#guard isExplicit [auto] 50 (.ofModule auto) .default_ .null = false
#guard isExplicit [expl] 50 (.ofModule expl) .default_ .null = true

-- 8.6: universal before application before context before private, then by number
#guard (U 30).lt (C 0) && (C 0).lt (C 1) && !(C 1).lt (C 0) && (⟨.application, 9⟩ : Tag).lt (C 0)
