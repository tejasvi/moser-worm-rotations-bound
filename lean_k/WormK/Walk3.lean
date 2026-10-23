import WormK.Fast3

/-!
# The unit walk on structured data (no strings)

`walkK`: the same walk as `WormCore.unitWalk`, over a `List Char` of codes and a `List Rec`, with the kernel-form
leaf test `WormK3.leafOKK` (with the local refinement of `leafOKR`).
-/

namespace WormK3

open WormCore MoserWorm

def leafOKRK (F : Fam) (maxsmall : Nat) (tauHi : Int) : Nat → Array Int → Array Int → Rec → Bool
  | 0, lo, hi, r => leafOKK F maxsmall tauHi lo hi r
  | d + 1, lo, hi, r =>
    leafOKK F maxsmall tauHi lo hi r ||
      (let i := widestAngle F.k lo hi
       let s := lo[i]! + hi[i]!
       decide (s % 2 = 0) &&
         leafOKRK F maxsmall tauHi d lo (hi.set! i (s / 2)) r &&
         leafOKRK F maxsmall tauHi d (lo.set! i (s / 2)) hi r)

def walkK (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) :
    Nat → List Char → List (Array Int × Array Int) → List Rec → Option (List Rec)
  | 0, _, _, _ => none
  | _ + 1, [], [], recs => some recs
  | fuel + 1, c :: cs, (lo, hi) :: st, recs =>
    if c = 'L' ∨ c = 'K' then
      match recs with
      | r :: rs => if leafOKRK F maxsmall tauHi rdepth lo hi r then walkK F maxsmall tauHi rdepth fuel cs st rs else none
      | [] => none
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => walkK F maxsmall tauHi rdepth fuel cs (l :: u :: st) recs
        | none => none
      | none => none
  | _, _, _, _ => none

/-- A piece: a subtree from its box, with its codes and records; all records used. -/
def pieceOK (box : Array Int × Array Int) (codes : List Char) (recs : List Rec) : Bool :=
  match walkK famW maxsmallW tauHiW rdepthW (codes.length + 1) codes [box] recs with
  | some [] => true
  | _ => false

end WormK3
