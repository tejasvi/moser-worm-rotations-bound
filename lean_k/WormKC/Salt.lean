import WormKC.Pack

/-!
# Tagged box literals

`decodeBoxS s` is `decodeBox (s / 65536)`: the low 16 bits of the literal are a tag that the decoder drops.
Lean hashes a `Nat` literal by its low 64 bits, and the packed boxes of one top walk often agree there (their
first coordinates coincide). Every term the kernel builds from such literals then falls into one hash bucket, and
a walk over `n` of them costs about `n²`. Distinct tags keep the literals of one declaration hash-distinct.
`decodeBoxS (b * 65536 + t)` unfolds to `decodeBox` of a literal equal to `b`, so a cover fact about
`decodeBox b` serves it by evaluation.
-/

namespace WormCore.K

/-- `decodeBox` of a literal whose low 16 bits are a tag. -/
def decodeBoxS (s : Nat) : Array Int × Array Int := decodeBox (s / 65536)

end WormCore.K
