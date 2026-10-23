import WormK.Fast

/-!
# The whole leaf test in kernel-friendly form

* the 24 box coordinates are passed through `intK` (continuation-passing on the constructors), so that every per-body
  term (`angK`, `trK`, `vtxK`) has literal arguments: equal terms of different leaves of one declaration are evaluated
  once (kernel cache);
* products with the exact unit columns (`x · 0`, `x · 2⁵⁶`) are done without multiplication;
* the zero blocks of the Hessian (no edge between the two bodies) are skipped;
* validity uses the same primitives (`fmul`).
Every function computes the same values as the corresponding function of `WormCore`.
-/

namespace WormK2

open WormCore MoserWorm
open WormK (ile imin imax shr cshr fmul mulPt fdet)

/-! ## Constructor-forcing continuations -/

def natK {β : Type} (n : Nat) (k : Nat → β) : β :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

def intK {β : Type} (x : Int) (k : Int → β) : β :=
  match x with
  | .ofNat n => natK n fun L => k (.ofNat L)
  | .negSucc n => natK n fun L => k (.negSucc L)

/-- Force the first `n` entries of a coordinate array, in order. -/
def arrK {β : Type} : Nat → List Int → (List Int → β) → β
  | 0, _, k => k []
  | _ + 1, [], k => k []
  | n + 1, x :: xs, k => intK x fun x' => arrK n xs fun ys => k (x' :: ys)

/-! ## Per-body data from literal coordinates -/

structure Ang where
  s : DIval
  c : DIval
  h : Int

structure Tr where
  tc : V2
  hx : Int
  hy : Int
  trad : DIval

def angK (tl th : Int) : Ang :=
  let t := (tl + th).fdiv 2
  let hθ := max (th - t) (t - tl)
  let sc := DIval.sincosIv ⟨toLo t, toHi t⟩
  ⟨sc.1, sc.2, toHi hθ⟩

def trK (xl xh yl yh : Int) : Tr :=
  let tx := (xl + xh).fdiv 2
  let ty := (yl + yh).fdiv 2
  let hx := toHi (max (xh - tx) (tx - xl))
  let hy := toHi (max (yh - ty) (ty - yl))
  ⟨(⟨toLo tx, toHi tx⟩, ⟨toLo ty, toHi ty⟩), hx, hy, DIval.norm2 (DIval.pt hx) (DIval.pt hy)⟩

/-- Vertex data: body, rotated body point, centre position, movement bound. -/
structure VD where
  b : Nat
  rq : V2
  x0 : V2
  mv : DIval

instance : Inhabited VD := ⟨⟨0, V2.zero, V2.zero, DIval.pt 0⟩⟩

def vtxK (F : Fam) (g b : Nat) (A : Ang) (T : Tr) : VD :=
  let rq := V2.rot A.s A.c F.q[g]!
  ⟨b, rq, V2.add T.tc rq, (F.qn[g]!.mul (DIval.pt A.h)).add T.trad⟩

def vtx0 (F : Fam) (g : Nat) : VD := ⟨0, F.q[g]!, F.q[g]!, DIval.pt 0⟩

/-- The per-leaf context: the family, per body (1..4) its angle and translation data. -/
structure CK where
  F : Fam
  A1 : Ang
  A2 : Ang
  A3 : Ang
  A4 : Ang
  T1 : Tr
  T2 : Tr
  T3 : Tr
  T4 : Tr

def CK.ang (C : CK) (b : Nat) : Ang :=
  match b with
  | 1 => C.A1
  | 2 => C.A2
  | 3 => C.A3
  | _ => C.A4

def CK.tr (C : CK) (b : Nat) : Tr :=
  match b with
  | 1 => C.T1
  | 2 => C.T2
  | 3 => C.T3
  | _ => C.T4

def CK.vd (C : CK) (g : Nat) : VD :=
  match C.F.body[g]! with
  | 0 => vtx0 C.F g
  | 1 => vtxK C.F g 1 C.A1 C.T1
  | 2 => vtxK C.F g 2 C.A2 C.T2
  | 3 => vtxK C.F g 3 C.A3 C.T3
  | _ => vtxK C.F g 4 C.A4 C.T4

/-! ## Exact unit columns -/

/-- `x · 2⁵⁶ / 2⁵⁶` as an interval (`DIval.mul x (pt 2⁵⁶)`): the sorted end points. -/
def sortI (x : DIval) : DIval := cond (ile x.lo x.hi) x ⟨x.hi, x.lo⟩

def negI (x : DIval) : DIval := ⟨-x.hi, -x.lo⟩

/-- `det(x, lc j r)`. -/
def detXL (x : V2) (j : Nat) (r : V2) : DIval :=
  match j with
  | 0 => negI (sortI x.2)
  | 1 => sortI x.1
  | 2 => fdet x r
  | _ => fdet x (V2.J r)

/-- `det(lc j r, x)`. -/
def detLX (j : Nat) (r : V2) (x : V2) : DIval :=
  match j with
  | 0 => sortI x.2
  | 1 => negI (sortI x.1)
  | 2 => fdet r x
  | _ => fdet (V2.J r) x

/-- `det(lc j r1, lc l r2)`. -/
def detLL (j : Nat) (r1 : V2) (l : Nat) (r2 : V2) : DIval :=
  match j with
  | 0 => match l with
    | 0 => DIval.pt 0
    | 1 => DIval.pt dfxOne
    | 2 => sortI r2.2
    | _ => sortI r2.1
  | 1 => match l with
    | 0 => DIval.pt (-dfxOne)
    | 1 => DIval.pt 0
    | 2 => negI (sortI r2.1)
    | _ => sortI r2.2
  | 2 => detXL r1 l r2
  | _ => detXL (V2.J r1) l r2

/-! ## The bound -/

structure Edge where
  b1 : Nat
  b2 : Nat
  x1 : V2
  x2 : V2
  r1 : V2
  r2 : V2

def edgesK (C : CK) (l : List Nat) : List Edge :=
  (cycPairs l).map fun p =>
    let u := C.vd p.1
    let v := C.vd p.2
    ⟨u.b, v.b, u.x0, v.x0, u.rq, v.rq⟩

structure AV where
  a : Nat
  b : Nat
  j : Nat
  y0 : Int
  w : Int

def gK (es : List Edge) (u : AV) : DIval :=
  (isum (es.map fun e =>
    (cond (e.b2 == u.b) (detXL e.x1 u.j e.r2) (DIval.pt 0)).add
      (cond (e.b1 == u.b) (detLX u.j e.r1 e.x2) (DIval.pt 0)))).half

def mKL (es : List Edge) (u v : AV) : DIval :=
  (isum ((es.filter fun e => e.b1 == u.b && e.b2 == v.b).map fun e => detLL u.j e.r1 v.j e.r2)).half

/-- Rows: per active variable `u`: `g_u`, the entries `H_uv` (without `β`) of the present blocks (always the
diagonal), the off-diagonal Gershgorin sum. -/
structure Row where
  u : AV
  g : DIval
  ents : List (AV × DIval)
  off : DIval

structure SD where
  F0 : DIval
  rows : List Row

def sdOf (C : CK) (ad : List AV) (l : List Nat) : SD :=
  let es := edgesK C l
  let F0 := (isum (es.map fun e => fdet e.x1 e.x2)).half
  let present := fun (p q : Nat) => es.any fun e => (e.b1 == p && e.b2 == q) || (e.b1 == q && e.b2 == p)
  let rows := ad.map fun u =>
    let ents := (ad.filter fun v => v.a == u.a || present u.b v.b).map fun v =>
      (v, cond (present u.b v.b) ((mKL es u v).add (mKL es v u)) (DIval.pt 0))
    let off := isum ((ents.filter fun p => !(p.1.a == u.a)).map fun p => (mulPt (mulPt p.2 u.w) p.1.w).abs)
    ⟨u, gK es u, ents, off⟩
  ⟨F0, rows⟩

def partsK (sd : SD) (β : Int) : DIval × List DIval :=
  let b2 := DIval.pt (2 * β)
  let hb := fun (u v : AV) (h : DIval) => cond (u.a == v.a && 2 ≤ u.j) (h.add b2) h
  let g2 := fun (r : Row) => cond (r.u.j == 2) (r.g.add b2) r.g
  let cRows := sd.rows.filter fun r => r.u.j == 2
  let lin := isum (cRows.map fun r => mulPt (g2 r) r.u.y0)
  let quad := isum (cRows.flatMap fun r =>
    (r.ents.filter fun p => p.1.j == 2).map fun p => (mulPt (mulPt (hb r.u p.1 p.2) r.u.y0) p.1.y0).half)
  let Fy0 := (sd.F0.add lin).add quad
  let grad := sd.rows.map fun r =>
    (g2 r).add (isum ((r.ents.filter fun p => p.1.j == 2).map fun p => mulPt (hb r.u p.1 p.2) p.1.y0))
  let pen := isum (sd.rows.map fun r =>
    let haa := hb r.u r.u ((r.ents.find? fun p => p.1.a == r.u.a).map (·.2) |>.getD (DIval.pt 0))
    (r.off.sub (mulPt (mulPt haa r.u.w) r.u.w)).pos)
  (Fy0.sub pen.half, grad)

def addGrads : List (List DIval) → List DIval → List DIval
  | [], acc => acc
  | g :: gs, acc => addGrads gs (List.zipWith DIval.add acc g)

def comboK (ad : List AV) (sds : List (SD × Int)) (β : Int) : DIval :=
  let parts := sds.map fun p => (partsK p.1 β, p.2)
  let gsum := addGrads (parts.map fun pt => pt.1.2.map fun g => mulPt g pt.2) (ad.map fun _ => DIval.pt 0)
  (isum (parts.map fun pt => mulPt pt.1.1 pt.2)).sub
    (isum (List.zipWith (fun u g => mulPt g.abs u.w) ad gsum))

def avOf (C : CK) (a : Nat) : AV :=
  let b := a / 4 + 1
  let A := C.ang b
  let T := C.tr b
  let j := a % 4
  let cl := cLo A.h
  ⟨a, b, j, cond (j == 2) (cl.fdiv 2) 0,
    match j with
    | 0 => T.hx
    | 1 => T.hy
    | 2 => -(cl.fdiv 2)
    | _ => A.h⟩

def leafBoundK (C : CK) (sts : List (St × Int)) : Int :=
  let used := fun (b : Nat) => sts.any fun p => p.1.verts.any fun g => C.F.body[g]! == b
  let act := (List.range (4 * C.F.k)).filter fun a => used (a / 4 + 1)
  let ad := act.map (avOf C)
  let sds := sts.map fun p => (sdOf C ad p.1.verts, p.2)
  betas.foldl (fun best β => max best (comboK ad sds β).lo) (-(1000 * dfxOne))

/-! ## Validity -/

def dotK (a b : V2) : DIval := (fmul a.1 b.1).add (fmul a.2 b.2)

def pairMoveK (C : CK) (a b : Nat) : DIval :=
  let u := C.vd a
  let v := C.vd b
  if u.b = v.b then
    if u.b = 0 then DIval.pt 0 else (V2.norm (V2.sub C.F.q[b]! C.F.q[a]!)).mul (DIval.pt (C.ang u.b).h)
  else u.mv.add v.mv

def diffK (C : CK) (a b : Nat) : V2 :=
  let u := C.vd a
  let v := C.vd b
  if u.b = v.b ∧ u.b ≠ 0 then V2.rot (C.ang u.b).s (C.ang u.b).c (V2.sub C.F.q[b]! C.F.q[a]!)
  else V2.sub v.x0 u.x0

def det3K (C : CK) (a b i : Nat) : DIval :=
  let ba := (C.vd a).b
  if ba = (C.vd b).b ∧ ba = (C.vd i).b then
    V2.det (V2.sub C.F.q[b]! C.F.q[a]!) (V2.sub C.F.q[i]! C.F.q[a]!)
  else
    let u := diffK C a b
    let v := diffK C a i
    let eab := pairMoveK C a b
    let eai := pairMoveK C a i
    let err := ((eab.mul (V2.norm v)).add (eai.mul (V2.norm u))).add (eab.mul eai)
    let d := fdet u v
    ⟨(d.sub err).lo, (d.add err).hi⟩

def fanVarK (C : CK) (z : V2) (a b : Nat) : DIval :=
  let u := C.vd a
  let v := C.vd b
  let xa := V2.sub u.x0 z
  let xb := V2.sub v.x0 z
  if u.b = v.b then
    if u.b = 0 then DIval.pt 0
    else
      let A := C.ang u.b
      let T := C.tr u.b
      let w := V2.norm (V2.sub C.F.q[b]! C.F.q[a]!)
      let tz := V2.norm (V2.sub T.tc z)
      w.mul ((T.trad.mul ((DIval.ofInt 1).add (DIval.pt A.h))).add (tz.mul (DIval.pt A.h)))
  else
    (u.mv.mul ((V2.norm xb).add v.mv)).add ((V2.norm xa).mul v.mv)

def fanDetLoK (C : CK) (z : V2) (a b : Nat) : Int :=
  ((fdet (V2.sub (C.vd a).x0 z) (V2.sub (C.vd b).x0 z)).sub (fanVarK C z a b)).lo

def fanOKK (C : CK) (v : List Nat) (zx zy : Int) : Bool :=
  let m := v.length
  let z : V2 := (DIval.pt zx, DIval.pt zy)
  let va := v.toArray
  let xs := va.map fun g => V2.sub (C.vd g).x0 z
  let P : Array (Array Bool) := (List.range m).toArray.map fun i =>
    (List.range (m + 1)).toArray.map fun d =>
      decide (1 ≤ d) && decide (d < m) && decide (0 < (fdet xs[i]! xs[(i + d) % m]!).lo)
  let D : Array (Array Bool) := (List.range m).toArray.map fun i =>
    (List.range (m + 1)).toArray.map fun d =>
      decide (1 ≤ d) && decide (d < m) && decide (0 < (dotK xs[i]! xs[(i + d) % m]!).lo)
  decide (3 ≤ m) &&
  ((List.range m).all fun j => decide (0 < fanDetLoK C z va[j]! va[(j + 1) % m]!)) &&
  ((List.range m).any fun s0 => decide (windCost m (fun i d => (P[i]!)[d]!) (fun i d => (D[i]!)[d]!) s0 ≤ 7))

def vfanOKK (C : CK) (piece : List Nat) (r : Nat) : Bool :=
  let m := piece.length
  let l := piece.drop r ++ piece.take r
  ((List.range m).all fun i => decide (i < 2) || decide (0 < (det3K C (at' l 0) (at' l 1) (at' l i)).lo)) &&
  ((List.range m).all fun i => decide (i < 2) || decide (m ≤ i + 1) ||
    decide (0 < (det3K C (at' l 0) (at' l i) (at' l (i + 1))).lo))

def chordOKK (C : CK) (maxsmall : Nat) : CT → List Nat → Bool
  | .small, piece => decide (piece.length ≤ maxsmall)
  | .vfan r, piece => decide (r < piece.length) && decide (3 ≤ piece.length) && vfanOKK C piece r
  | .cut s t L R, piece =>
    let n := piece.length
    let dd := (t + n - s) % n
    let ps := at' piece s
    let pt := at' piece t
    decide (s < n) && decide (t < n) && decide (2 ≤ dd) && decide (dd + 2 ≤ n) &&
    decide (0 < ((V2.norm (diffK C ps pt)).sub (pairMoveK C ps pt)).lo) &&
    ((List.range dd).all fun k => decide (k = 0) || decide ((det3K C ps pt (at' piece (s + k))).hi ≤ 0)) &&
    ((List.range (n - dd)).all fun k => decide (k = 0) || decide (0 ≤ (det3K C ps pt (at' piece (t + k))).lo)) &&
    chordOKK C maxsmall L ((List.range (dd + 1)).map fun k => at' piece (s + k)) &&
    chordOKK C maxsmall R ((List.range (n - dd + 1)).map fun k => at' piece (t + k))

def stOKK (C : CK) (maxsmall : Nat) : St → Bool
  | .small v => decide (v.length ≤ maxsmall) && v.Nodup && v.all (· < C.F.body.size)
  | .fan v zx zy => v.Nodup && v.all (· < C.F.body.size) && fanOKK C v zx zy
  | .chord v t => v.Nodup && v.all (· < C.F.body.size) && chordOKK C maxsmall t v

/-! ## The leaf test -/

def leafCoreK (F : Fam) (maxsmall : Nat) (tauHi : Int) (r : Rec) (C : CK) : Bool :=
  decide (r.sts ≠ []) &&
  r.sts.all (fun (st, lam) => decide (0 ≤ lam) && stOKK C maxsmall st) &&
  decide ((r.sts.map (·.2)).foldl (· + ·) 0 ≤ dfxOne) &&
  decide (tauHi < leafBoundK C r.sts)

/-- The leaf test: force the coordinates, build the per-body data from the literals, test. -/
def leafOKK (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) : Bool :=
  arrK 12 lo.toList fun l => arrK 12 hi.toList fun h =>
    match l, h with
    | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11], [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] =>
      leafCoreK F maxsmall tauHi r
        ⟨F, angK l0 h0, angK l3 h3, angK l6 h6, angK l9 h9,
          trK l1 h1 l2 h2, trK l4 h4 l5 h5, trK l7 h7 l8 h8, trK l10 h10 l11 h11⟩
    | _, _ => false

end WormK2
