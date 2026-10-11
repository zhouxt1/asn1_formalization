import Asn1.Bits

/-!
# Field-lists and the complete encoding (X.691 10.5, 11.1)

PER does not encode a value straight into bits. Each value encodes into a *field-list* (10.5), a
sequence of bit-fields, each of them either unaligned or "octet-aligned in the ALIGNED variant"
(10.5.3). Only the outermost value's field-list becomes bits, in 11.1, and that is where the
ALIGNED variant inserts its padding. Keeping that two-step structure means one definition per
type covers ALIGNED and UNALIGNED, as it does in the text.
-/

namespace Asn1.X691

/-- X.691 7: the four PER encodings are ALIGNED or UNALIGNED, and BASIC or CANONICAL. -/
structure Variant where
  aligned : Bool
  canonical : Bool
  deriving DecidableEq, Repr

/-- X.691 10.5.3 b) and c): a bit-field. `aligned` is "a bit-field (octet-aligned in the ALIGNED
variant)". The UNALIGNED variant ignores the flag (11.1.3). -/
inductive Field where
  | unaligned (bs : Bits)
  | aligned (bs : Bits)
  deriving DecidableEq, Repr, Inhabited

/-- X.691 10.5.3 d) -/
abbrev FieldList := List Field

/-- The bits of a field, before any padding. -/
def Field.bits : Field → Bits
  | .unaligned bs => bs
  | .aligned bs => bs

/-- Zero bits to the next multiple of eight (11.1.3.1, 11.1.4). -/
def pad8 (acc : Bits) : Bits := acc ++ List.replicate ((8 - acc.length % 8) % 8) false

/-- X.691 11.1.2–11.1.4: each field in turn is concatenated onto the end of the encoding so far.
In the ALIGNED variant, an octet-aligned field first gets zero bits up to a multiple of eight. -/
def concatFields (aligned : Bool) : Bits → FieldList → Bits
  | acc, [] => acc
  | acc, .unaligned bs :: fs => concatFields aligned (acc ++ bs) fs
  | acc, .aligned bs :: fs => concatFields aligned ((if aligned then pad8 acc else acc) ++ bs) fs

/-- X.691 11.1.1: what carries the outermost value's encoding. 11.1.3 treats an ASN.1 bitstring
(case b) differently from the rest. -/
inductive Carrier where
  /-- 11.1.1 b) -/
  | bitString
  /-- 11.1.1 a), c), d), e): an octetstring, an open type, an external or embedded pdv,
  or a carrier protocol not defined in ASN.1 -/
  | other
  deriving DecidableEq, Repr

/-- X.691 11.1: the complete encoding of the outermost value's field-list.
- ALIGNED (11.1.4): an empty result becomes one zero octet, and anything else is padded to a
  multiple of eight bits.
- UNALIGNED (11.1.3): the same, except inside an ASN.1 bitstring (11.1.3.2), where an empty
  result becomes a single 0 bit and nothing is padded. -/
def complete (v : Variant) (c : Carrier) (fl : FieldList) : Bits :=
  let bs := concatFields v.aligned [] fl
  if !v.aligned && c == .bitString then
    if bs = [] then [false] else bs
  else
    if bs = [] then List.replicate 8 false else pad8 bs

end Asn1.X691
