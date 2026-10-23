import WormCore.Family

/-!
# A kernel-friendly evaluation of the worm leaf bound

`leafBoundK` computes the same value as `WormCore.leafBound`:

* the quadratic model is computed only on the active variables, and only from the edges whose bodies match (the
  dense `16 × 16` model of `model` evaluates `MTerm` for every entry and edge);
* products with the zero centre coordinates `y₀ₐ` (`a % 4 ≠ 2`) are skipped (exact: `x · 0 = 0`);
* the off-diagonal Gershgorin sums do not depend on `β` and are computed once;
* products with point intervals use two endpoint products (`mulPt`), comparisons use a constructor match.
-/

namespace WormK

open WormCore MoserWorm

/-! ## Primitives -/

/-- `a ≤ b` by a constructor match (no subtraction). -/
def ile (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m

def imin (a b : Int) : Int := cond (ile a b) a b
def imax (a b : Int) : Int := cond (ile a b) b a

/-- `⌊x / 2⁵⁶⌋`. -/
def shr (x : Int) : Int :=
  match x with
  | .ofNat n => .ofNat (n >>> 56)
  | .negSucc n => .negSucc (n >>> 56)

/-- `⌈x / 2⁵⁶⌉`. -/
def cshr (x : Int) : Int := -(shr (-x))

/-- `DIval.mul` with constructor-match comparisons and shifts. -/
def fmul (a b : DIval) : DIval :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨shr (imin (imin p1 p2) (imin p3 p4)), cshr (imax (imax p1 p2) (imax p3 p4))⟩

/-- `a.mul (DIval.pt c)`. -/
def mulPt (a : DIval) (c : Int) : DIval :=
  let p := a.lo * c
  let q := a.hi * c
  cond (ile p q) ⟨shr p, cshr q⟩ ⟨shr q, cshr p⟩

def fdet (a b : V2) : DIval := (fmul a.1 b.2).sub (fmul a.2 b.1)

/-- The `j`-th column of a vertex with rotated body point `rq`. -/
def lc (j : Nat) (rq : V2) : V2 :=
  match j with
  | 0 => (DIval.ofInt 1, DIval.pt 0)
  | 1 => (DIval.pt 0, DIval.ofInt 1)
  | 2 => rq
  | _ => V2.J rq

/-- Edge data: bodies, centre positions and rotated body points of both ends. -/
structure Edge where
  b1 : Nat
  b2 : Nat
  x1 : V2
  x2 : V2
  r1 : V2
  r2 : V2

def edges (C : Ctx) (l : List Nat) : List Edge :=
  (cycPairs l).map fun p => ⟨C.F.body[p.1]!, C.F.body[p.2]!, C.X0[p.1]!, C.X0[p.2]!, C.RQ[p.1]!, C.RQ[p.2]!⟩

/-- Active variable data: index, `y₀`, `w`. -/
structure AV where
  a : Nat
  y0 : Int
  w : Int

/-- `g_k` (half of the sum over the edges). -/
def gK (es : List Edge) (k : Nat) : DIval :=
  (isum (es.map fun e =>
    (if e.b2 ≠ 0 ∧ k / 4 = e.b2 - 1 then fdet e.x1 (lc (k % 4) e.r2) else DIval.pt 0).add
      (if e.b1 ≠ 0 ∧ k / 4 = e.b1 - 1 then fdet (lc (k % 4) e.r1) e.x2 else DIval.pt 0))).half

/-- `M_kl` from the matching edges only. -/
def mKL (es : List Edge) (k l : Nat) : DIval :=
  (isum ((es.filter fun e => e.b1 == k / 4 + 1 && e.b2 == l / 4 + 1).map fun e =>
    fdet (lc (k % 4) e.r1) (lc (l % 4) e.r2))).half

/-- Structure data independent of `β`: `F₀`, and per active variable `a`: `g_a`, the row `H_a·` (without `β`), the
off-diagonal Gershgorin sum. -/
structure SD where
  F0 : DIval
  rows : List (AV × DIval × List (AV × DIval) × DIval)

def sdOf (C : Ctx) (ad : List AV) (l : List Nat) : SD :=
  let es := edges C l
  let F0 := (isum (es.map fun e => fdet e.x1 e.x2)).half
  let rows := ad.map fun u =>
    let row := ad.map fun v => (v, (mKL es u.a v.a).add (mKL es v.a u.a))
    let off := isum ((row.filter fun p => p.1.a ≠ u.a).map fun p => (mulPt (mulPt p.2 u.w) p.1.w).abs)
    (u, gK es u.a, row, off)
  ⟨F0, rows⟩

/-- The bound and gradient of one structure for `β` (same values as `boundParts`). -/
def partsK (sd : SD) (β : Int) : DIval × List DIval :=
  let hb := fun (u v : AV) (h : DIval) => if u.a = v.a ∧ u.a % 4 ≥ 2 then h.add (DIval.pt (2 * β)) else h
  let g2 := fun (u : AV) (g : DIval) => if u.a % 4 = 2 then g.add (DIval.pt (2 * β)) else g
  let cRows := sd.rows.filter fun r => r.1.a % 4 = 2
  let lin := isum (cRows.map fun r => mulPt (g2 r.1 r.2.1) r.1.y0)
  let quad := isum (cRows.flatMap fun r =>
    (r.2.2.1.filter fun p => p.1.a % 4 = 2).map fun p => (mulPt (mulPt (hb r.1 p.1 p.2) r.1.y0) p.1.y0).half)
  let Fy0 := (sd.F0.add lin).add quad
  let grad := sd.rows.map fun r =>
    (g2 r.1 r.2.1).add (isum ((r.2.2.1.filter fun p => p.1.a % 4 = 2).map fun p => mulPt (hb r.1 p.1 p.2) p.1.y0))
  let pen := isum (sd.rows.map fun r =>
    let haa := hb r.1 r.1 ((r.2.2.1.find? fun p => p.1.a = r.1.a).map (·.2) |>.getD (DIval.pt 0))
    (r.2.2.2.sub (mulPt (mulPt haa r.1.w) r.1.w)).pos)
  (Fy0.sub pen.half, grad)

/-- Sum of a list of gradients (componentwise). -/
def addGrads : List (List DIval) → List DIval → List DIval
  | [], acc => acc
  | g :: gs, acc => addGrads gs (List.zipWith DIval.add acc g)

def comboK (ad : List AV) (sds : List (SD × Int)) (β : Int) : DIval :=
  let parts := sds.map fun p => (partsK p.1 β, p.2)
  let gsum := addGrads (parts.map fun pt => pt.1.2.map fun g => mulPt g pt.2) (ad.map fun _ => DIval.pt 0)
  (isum (parts.map fun pt => mulPt pt.1.1 pt.2)).sub
    (isum (List.zipWith (fun u g => mulPt g.abs u.w) ad gsum))

def leafBoundK (C : Ctx) (sts : List (St × Int)) : Int :=
  let nv := 4 * C.F.k
  let act := (List.range nv).filter fun a => bodyUsed C sts (a / 4 + 1)
  let ad := act.map fun a => (⟨a, y0At C a, wAt C a⟩ : AV)
  let sds := sts.map fun p => (sdOf C ad p.1.verts, p.2)
  betas.foldl (fun best β => max best (comboK ad sds β).lo) (-(1000 * dfxOne))

def leafOKK (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) : Bool :=
  let C := mkCtx F lo hi
  decide (r.sts ≠ []) &&
  r.sts.all (fun (st, lam) => decide (0 ≤ lam) && stOK C maxsmall st) &&
  decide ((r.sts.map (·.2)).foldl (· + ·) 0 ≤ dfxOne) &&
  decide (tauHi < leafBoundK C r.sts)

end WormK
