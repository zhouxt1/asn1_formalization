import Asn1.X680.Enumerated

/-! X.680 20.5 and 20.6's examples. -/

open Asn1.X680

def id' (s : String) : String × Option Int := (s, none)
def nn (s : String) (k : Int) : String × Option Int := (s, some k)

-- 20.5: A ::= ENUMERATED {a, b, ..., c(0)} is invalid, since both 'a' and 'c' equal 0
#guard enumNumbers [id' "a", id' "b"] (some [nn "c" 0]) = [("a", 0), ("b", 1), ("c", 0)]
-- B ::= ENUMERATED {a, b, ..., c, d(2)} is invalid, since both 'c' and 'd' equal 2
#guard enumNumbers [id' "a", id' "b"] (some [id' "c", nn "d" 2]) = [("a", 0), ("b", 1), ("c", 2), ("d", 2)]
-- C ::= ENUMERATED {a, b(3), ..., c(1)}, valid, 'c' = 1
#guard enumNumbers [id' "a", nn "b" 3] (some [nn "c" 1]) = [("a", 0), ("b", 3), ("c", 1)]
-- 20.6: A ::= ENUMERATED {a, b, ..., c}, c = 2
#guard enumNumbers [id' "a", id' "b"] (some [id' "c"]) = [("a", 0), ("b", 1), ("c", 2)]
-- B ::= ENUMERATED {a, b, c(0), ..., d}, d = 3
#guard enumNumbers [id' "a", id' "b", nn "c" 0] (some [id' "d"]) =
  [("a", 1), ("b", 2), ("c", 0), ("d", 3)]
-- C ::= ENUMERATED {a, b, ..., c(3), d}, d = 4
#guard enumNumbers [id' "a", id' "b"] (some [nn "c" 3, id' "d"]) = [("a", 0), ("b", 1), ("c", 3), ("d", 4)]
-- D ::= ENUMERATED {a, z(25), ..., d}, d = 1
#guard enumNumbers [id' "a", nn "z" 25] (some [id' "d"]) = [("a", 0), ("z", 25), ("d", 1)]
