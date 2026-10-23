import WormKC.Walk

/-!
# K data: packed pieces (core Lean only)

A module holds a table of records (a Braun tree, explicit constructor term) and its pieces. A piece is a box, a
packed code stream (base 16, little-endian, symbols `1..15`, ended by the value `0`) and a packed index stream
(16-bit fields, `cnt` of them). `pieceOKK` decodes both and runs `walkG`; it also checks that the box has 12
coordinates and lies in the root box, so one kernel evaluation gives everything `cov_of_pieceOKK` needs.
The decoders are untrusted: the cover lemma holds for whatever lists they produce.
-/

namespace WormCore.K

open WormCore

/-- Braun tree: index `0` is the root; index `i ≥ 1` goes left (odd `i`) to `(i - 1) / 2` or right (even `i`)
to `(i - 2) / 2`. -/
inductive BTree (α : Type) where
  | leaf : BTree α
  | node : α → BTree α → BTree α → BTree α

def BTree.get {α : Type} : BTree α → Nat → Option α
  | .leaf, _ => none
  | .node v l r, i =>
    if i = 0 then some v
    else if i % 2 = 1 then l.get (i / 2) else r.get (i / 2 - 1)

/-- Code symbols: `1..10` the digits, `11`, `12` the letters `a`, `b`, `13` = `L`, `14` = `K`, `15` = `P`. -/
def symChar (s : Nat) : Char :=
  ['?', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'L', 'K', 'P'].getD s '?'

def decodeCodes : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else symChar (n % 16) :: decodeCodes fuel (n / 16)

def decodeIdx : Nat → Nat → List Nat
  | 0, _ => []
  | cnt + 1, n => n % 65536 :: decodeIdx cnt (n / 65536)

/-! ### Packed records and boxes (bit fields, little-endian) -/

/-- The low `k` bits and the rest. -/
def rd (n k : Nat) : Nat × Nat := (n % 2 ^ k, n / 2 ^ k)

/-- A sign bit and a `k`-bit magnitude. -/
def rdInt (n k : Nat) : Int × Nat :=
  match rd n 1 with
  | (s, n1) => match rd n1 k with
    | (m, n2) => (if s = 0 then (m : Int) else -(m : Int), n2)

def rdNats (k : Nat) : Nat → Nat → List Nat × Nat
  | 0, n => ([], n)
  | c + 1, n => match rd n k with
    | (v, n1) => match rdNats k c n1 with
      | (vs, n2) => (v :: vs, n2)

def rdInts (k : Nat) : Nat → Nat → List Int × Nat
  | 0, n => ([], n)
  | c + 1, n => match rdInt n k with
    | (v, n1) => match rdInts k c n1 with
      | (vs, n2) => (v :: vs, n2)

/-- Chord trees: tag `0` small, `1` vertex fan (5-bit position), `2` cut (two 5-bit positions, then both trees). -/
def rdCT : Nat → Nat → CT × Nat
  | 0, n => (.small, n)
  | f + 1, n => match rd n 2 with
    | (tag, n1) =>
      if tag = 1 then match rd n1 5 with
        | (r, n2) => (.vfan r, n2)
      else if tag = 2 then match rd n1 5 with
        | (s, n2) => match rd n2 5 with
          | (t, n3) => match rdCT f n3 with
            | (L, n4) => match rdCT f n4 with
              | (R, n5) => (.cut s t L R, n5)
      else (.small, n1)

/-- A structure: kind (2 bits: small, fan, chord), vertex count and 5-bit vertex ids, then the fan point (two
signed 62-bit numbers) or the chord tree. -/
def rdSt (n : Nat) : St × Nat :=
  match rd n 2 with
  | (kind, n1) => match rd n1 5 with
    | (len, n2) => match rdNats 5 len n2 with
      | (vs, n3) =>
        if kind = 1 then match rdInt n3 62 with
          | (zx, n4) => match rdInt n4 62 with
            | (zy, n5) => (.fan vs zx zy, n5)
        else if kind = 2 then match rdCT 40 n3 with
          | (t, n4) => (.chord vs t, n4)
        else (.small vs, n3)

def rdSts : Nat → Nat → List (St × Int) × Nat
  | 0, n => ([], n)
  | c + 1, n => match rdSt n with
    | (st, n1) => match rdInt n1 62 with
      | (w, n2) => match rdSts c n2 with
        | (rest, n3) => ((st, w) :: rest, n3)

/-- A record: a 4-bit count of weighted structures. -/
def decodeRec (n : Nat) : Rec := match rd n 4 with
  | (c, n1) => ⟨(rdSts c n1).1⟩

/-- Box coordinates from coordinate `i` on: depth `d` (6 bits), index `k` (`d` bits), giving
`[lo_i + k w, lo_i + (k + 1) w]` with `w = (hi_i - lo_i) / 2^d` for the root box (dyadic encoding). -/
def rdCoords : Nat → Nat → Nat → List (Int × Int) × Nat
  | _, 0, n => ([], n)
  | i, c + 1, n => match rd n 6 with
    | (d, n1) => match rd n1 d with
      | (k, n2) =>
        let w := (rootW.hi[i]! - rootW.lo[i]!) / ((2 ^ d : Nat) : Int)
        let lo := rootW.lo[i]! + (k : Int) * w
        match rdCoords (i + 1) c n2 with
        | (rest, n3) => ((lo, lo + w) :: rest, n3)

/-- A dyadic sub-box of the root box. -/
def decodeBox (n : Nat) : Array Int × Array Int :=
  match rdCoords 0 12 n with
  | (cs, _) => ((cs.map (·.1)).toArray, (cs.map (·.2)).toArray)

def recsOf (tab : BTree Nat) (idx : List Nat) : List Rec := idx.map fun i => decodeRec ((tab.get i).getD 0)

/-- `BoxSub` as a `Bool`. -/
def boxSubB (lo hi lo' hi' : Array Int) : Bool :=
  (List.range 12).all fun i => decide (lo'[i]! ≤ lo[i]!) && decide (hi[i]! ≤ hi'[i]!)

/-- A piece: box sizes, box in the root, and the walk with leaf test `leafT` on the decoded data. -/
def pieceOKK (leafT : Nat → Array Int → Array Int → Rec → Bool) (tab : BTree Nat) (nb nc cnt ni : Nat) : Bool :=
  let B := decodeBox nb
  let cs := decodeCodes 1000000 nc
  (B.1.size == 12 && B.2.size == 12) && boxSubB B.1 B.2 rootW.lo rootW.hi &&
    walkDone (walkG leafT rdepthW (cs.length + 1) cs [B] (recsOf tab (decodeIdx cnt ni)))

/-- The top tree of a unit on packed codes; `out` lists the piece boxes in reverse walk order. -/
def topOKK (B : Array Int × Array Int) (nt : Nat) (out : List (Array Int × Array Int)) : Bool :=
  let cs := decodeCodes 1000000 nt
  decide (topWalk (cs.length + 1) cs [B] [] = some out)

/-- Skeleton symbols: `1..12` the split codes `0..9, a, b`, `13` = `U`. -/
def skelChar (s : Nat) : Char :=
  ['?', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'U'].getD s '?'

def decodeSkel : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else skelChar (n % 16) :: decodeSkel fuel (n / 16)

/-- `unitBoxes` on a character list (no `String`, so the kernel evaluates it directly). -/
def unitBoxesL (R : Root) (p : Nat) (cs : List Char) : Option (Array (Array Int × Array Int)) :=
  let cells := (List.range (ncells R / R.nparts)).map fun k => cellBox R (p + R.nparts * k)
  match skelWalk (2 * cs.length + 2) cs cells #[] with
  | some (acc, []) => some acc
  | _ => none

theorem unitBoxes_ofList (R : Root) (p : Nat) (cs : List Char) :
    unitBoxes R p (String.ofList cs) = unitBoxesL R p cs := by
  simp only [unitBoxes, unitBoxesL, String.length_ofList, String.toList_ofList]
  split <;> split <;> simp_all

end WormCore.K
