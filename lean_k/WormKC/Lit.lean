import Lean
import WormKC.Pack

/-!
# Literal elaborators for generated K data (untrusted)

They build the data terms directly as raw natural-number literals and Braun-tree constructors, so elaborating a
generated module does not synthesize one `OfNat` instance per literal. The kernel checks every statement about
the terms they produce; their correctness does not matter for soundness.
-/

namespace WormCore.K

open Lean Elab Term Meta

/-- `nat_lit% "123"`: the raw natural-number literal `123` (decimal digits). -/
elab "nat_lit% " s:str : term => do
  match s.getString.toNat? with
  | some n => return mkRawNatLit n
  | none => throwError "nat_lit%: not a natural number"

/-- The Braun tree of `xs` (index `0` at the root, odd indices left, even right), as constructor terms. -/
partial def braunExpr (xs : Array Expr) : Expr :=
  if xs.isEmpty then mkApp (mkConst ``BTree.leaf) (mkConst ``Nat)
  else
    let odd := (List.range xs.size).filter (fun i => i % 2 = 1) |>.map (xs[·]!) |>.toArray
    let even := (List.range xs.size).filter (fun i => i % 2 = 0 ∧ i > 0) |>.map (xs[·]!) |>.toArray
    mkApp4 (mkConst ``BTree.node) (mkConst ``Nat) xs[0]! (braunExpr odd) (braunExpr even)

/-- `nat_btree% "a b c …"`: the Braun tree of the listed natural numbers (decimal, space separated). -/
elab "nat_btree% " s:str : term => do
  let toks := (s.getString.splitOn " ").filter (· ≠ "")
  let mut xs : Array Expr := #[]
  for t in toks do
    match t.toNat? with
    | some n => xs := xs.push (mkRawNatLit n)
    | none => throwError "nat_btree%: bad entry"
  return braunExpr xs

end WormCore.K
