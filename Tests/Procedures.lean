import Asn1.X691.Procedures

/-! Checks against the worked examples in X.691's own NOTEs. -/

open Asn1 Asn1.X691

/-- Render bits as a 0/1 string. -/
def showBits (bs : Bits) : String := String.ofList (bs.map fun b => if b then '1' else '0')

def items (n : Nat) : Assoc := .comps (List.replicate n [])

-- 11.9.3.6 NOTE: four items, one length octet 0 0000100
#guard (unconstrainedLength (items 4)).map Field.bits = [[false] ++ nnbFn 7 4]
#guard showBits ((unconstrainedLength (items 4)).head!.bits) = "00000100"
-- 11.9.3.7 NOTE: 130 items, 10 000000 10000010
#guard showBits ((unconstrainedLength (items 130)).head!.bits) = "1000000010000010"
-- 11.9.3.8.1 NOTE 2: 144K + 1 items are three fragments (64K, 64K, 16K), then a length of 1
#guard ((unconstrainedLength (items (144 * 1024 + 1))).map (showBits ∘ Field.bits)) =
  ["11000100", "11000100", "11000001", "00000001"]
-- 11.9.3.8.3 NOTE: a last fragment that is an exact multiple of 16K is followed by a zero length
#guard ((unconstrainedLength (items (16 * 1024))).map (showBits ∘ Field.bits)) =
  ["11000001", "00000000"]
-- 11.9.3.3 NOTE 1: IA5String (SIZE (3..6)) takes a 2-bit length, (SIZE (40000..40254)) an 8-bit one,
-- (SIZE (0..32000)) a two-octet aligned one, and (SIZE (64000)) none
#guard (constrainedWhole ⟨true, false⟩ 3 6 4).fields = [.unaligned (nnbFn 2 1)]
#guard (constrainedWhole ⟨true, false⟩ 40000 40254 40000).fields = [.unaligned (nnbFn 8 0)]
#guard (constrainedWhole ⟨true, false⟩ 0 32000 5).fields = [.aligned (nnbFn 16 5)]
#guard (constrainedWhole ⟨true, false⟩ 64000 64000 64000).fields = []
-- 11.1.4: an empty outermost encoding is one zero octet
#guard complete ⟨true, false⟩ .other [] = List.replicate 8 false
-- 11.1.3.2: in an ASN.1 bitstring, UNALIGNED, a single 0 bit
#guard complete ⟨false, false⟩ .bitString [] = [false]
-- 11.1.4: padding before an octet-aligned field, and at the end
#guard showBits (complete ⟨true, false⟩ .other [.unaligned [true], .aligned (nnbFn 8 255)]) =
  "1000000011111111"
#guard showBits (complete ⟨false, false⟩ .other [.unaligned [true], .aligned (nnbFn 8 255)]) =
  "1111111110000000"
