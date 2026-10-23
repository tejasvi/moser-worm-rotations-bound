import WormK.Fast2

/-!
# Direct-recursor primitives and leaf-independent (canonical) terms

* Int primitives on `Int.rec`/`Nat.rec` directly (`iadd`, `ineg`, `imul`, `ile`, `shr`): about a third of the
  kernel unfoldings of `+`, `*`, `-` with instances and matchers. Compiled code uses the core functions
  (`implemented_by`).
* Every expensive term is built from literal or canonical arguments only: the vertex data are obtained by
  continuation-passing (`withVD`), lists of vertex data are built the same way, so that equal per-vertex,
  per-edge and per-triple work of different leaves of one declaration is evaluated once (kernel cache).
* Products with the weight `2⁵⁶` (single structure) are exact (`sortI`).
-/

namespace WormK3

open WormCore MoserWorm
open WormK2 (natK intK arrK Ang Tr angK trK)

/-! ## Int primitives -/

def isnnImpl (m n : Nat) : Int := Int.subNatNat m n

@[implemented_by isnnImpl]
def isnn (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat (Nat.sub m n)) (fun k _ => Int.negSucc k) (Nat.sub n m)

def iaddImpl (a b : Int) : Int := a + b

@[implemented_by iaddImpl]
def iadd (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.add m n)) (fun n => isnn m (Nat.succ n)) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => isnn n (Nat.succ m))
      (fun n => Int.negSucc (Nat.succ (Nat.add m n))) b) a

def nnegImpl (n : Nat) : Int := -(n : Int)

/-- `-(n : Int)`. -/
@[implemented_by nnegImpl]
def nneg (n : Nat) : Int := Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun k _ => Int.negSucc k) n

def inegImpl (a : Int) : Int := -a

@[implemented_by inegImpl]
def ineg (a : Int) : Int := Int.rec (motive := fun _ => Int) (fun m => nneg m) (fun m => Int.ofNat (Nat.succ m)) a

def isub (a b : Int) : Int := iadd a (ineg b)

def imulImpl (a b : Int) : Int := a * b

@[implemented_by imulImpl]
def imul (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.mul m n)) (fun n => nneg (Nat.mul m (Nat.succ n))) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => nneg (Nat.mul (Nat.succ m) n))
      (fun n => Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b) a

def ileImpl (a b : Int) : Bool := decide (a ≤ b)

@[implemented_by ileImpl]
def ile (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Int.rec (motive := fun _ => Bool) (fun n => Nat.ble m n) (fun _ => false) b)
    (fun m => Int.rec (motive := fun _ => Bool) (fun _ => true) (fun n => Nat.ble n m) b) a

def nonnegImpl (a : Int) : Bool := decide (0 ≤ a)

@[implemented_by nonnegImpl]
def nonneg (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) a

/-- `0 < a`. -/
def pos (a : Int) : Bool := !(ile a 0)

def shrImpl (x : Int) : Int := x.fdiv dfxOne

/-- `⌊x / 2⁵⁶⌋`. -/
@[implemented_by shrImpl]
def shr (x : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.shiftRight n 56)) (fun n => Int.negSucc (Nat.shiftRight n 56)) x

def shr1Impl (x : Int) : Int := x.fdiv 2

/-- `⌊x / 2⌋`. -/
@[implemented_by shr1Impl]
def shr1 (x : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.shiftRight n 1)) (fun n => Int.negSucc (Nat.shiftRight n 1)) x

def cshr (x : Int) : Int := ineg (shr (ineg x))

def bselImpl {α : Type} (c : Bool) (t e : α) : α := if c then t else e

/-- `if c then t else e` (kernel: one `Bool.rec`). -/
@[implemented_by bselImpl]
def bsel {α : Type} (c : Bool) (t e : α) : α := Bool.rec (motive := fun _ => α) e t c

def kmin (a b : Int) : Int := bsel (ile a b) a b
def kmax (a b : Int) : Int := bsel (ile a b) b a

def isDImpl (w : Int) : Bool := w == dfxOne

/-- `w = 2⁵⁶`. -/
@[implemented_by isDImpl]
def isD (w : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun n => Nat.beq n 72057594037927936) (fun _ => false) w

/-! ## Interval operations (same values as `DIval.*`) -/

def kadd (a b : DIval) : DIval := ⟨iadd a.lo b.lo, iadd a.hi b.hi⟩
def ksub (a b : DIval) : DIval := ⟨isub a.lo b.hi, isub a.hi b.lo⟩
def kneg (a : DIval) : DIval := ⟨ineg a.hi, ineg a.lo⟩
def kpt0 : DIval := ⟨Int.ofNat 0, Int.ofNat 0⟩

def kmul (a b : DIval) : DIval :=
  let p1 := imul a.lo b.lo
  let p2 := imul a.lo b.hi
  let p3 := imul a.hi b.lo
  let p4 := imul a.hi b.hi
  ⟨shr (kmin (kmin p1 p2) (kmin p3 p4)), cshr (kmax (kmax p1 p2) (kmax p3 p4))⟩

/-- `a.mul (pt c)`. -/
def kmulPt (a : DIval) (c : Int) : DIval :=
  let p := imul a.lo c
  let q := imul a.hi c
  bsel (ile p q) ⟨shr p, cshr q⟩ ⟨shr q, cshr p⟩

/-- `a.mul (pt 2⁵⁶)`: the sorted end points. -/
def sortI (a : DIval) : DIval := bsel (ile a.lo a.hi) a ⟨a.hi, a.lo⟩

/-- `a.mul (pt w)` for a structure weight: exact for `w = 2⁵⁶`. -/
def kmulW (a : DIval) (w : Int) : DIval := bsel (isD w) (sortI a) (kmulPt a w)

def khalf (a : DIval) : DIval := ⟨shr1 a.lo, ineg (shr1 (ineg a.hi))⟩

def kabs (a : DIval) : DIval :=
  bsel (nonneg a.lo) a (bsel (ile a.hi (Int.ofNat 0)) (kneg a) ⟨Int.ofNat 0, kmax (ineg a.lo) a.hi⟩)

def kposI (a : DIval) : DIval := ⟨kmax a.lo (Int.ofNat 0), kmax a.hi (Int.ofNat 0)⟩

def kdet (u v : V2) : DIval := ksub (kmul u.1 v.2) (kmul u.2 v.1)
def kdot (u v : V2) : DIval := kadd (kmul u.1 v.1) (kmul u.2 v.2)
def kvsub (u v : V2) : V2 := (ksub u.1 v.1, ksub u.2 v.2)
def kJ (a : V2) : V2 := (kneg a.2, a.1)

def ksumImpl (l : List DIval) : DIval := l.foldl kadd kpt0

/-- Sum (left fold, as `isum`). -/
@[implemented_by ksumImpl]
def ksum (l : List DIval) : DIval :=
  List.rec (motive := fun _ => DIval → DIval) (fun acc => acc) (fun h _ ih acc => ih (kadd acc h)) l kpt0

/-! ## Vertex data from canonical arguments -/

structure VD where
  g : Nat
  b : Nat
  A : Ang
  T : Tr
  rq : V2
  x0 : V2
  mv : DIval

instance : Inhabited Ang := ⟨⟨DIval.pt 0, DIval.pt 0, 0⟩⟩
instance : Inhabited Tr := ⟨⟨(DIval.pt 0, DIval.pt 0), 0, 0, DIval.pt 0⟩⟩
instance : Inhabited VD := ⟨⟨0, 0, default, default, V2.zero, V2.zero, DIval.pt 0⟩⟩

def vdK (F : Fam) (g b : Nat) (A : Ang) (T : Tr) : VD :=
  let rq := V2.rot A.s A.c F.q[g]!
  ⟨g, b, A, T, rq, V2.add T.tc rq, (F.qn[g]!.mul (DIval.pt A.h)).add T.trad⟩

def vd0 (F : Fam) (g : Nat) : VD := ⟨g, 0, default, default, F.q[g]!, F.q[g]!, DIval.pt 0⟩

structure Env where
  F : Fam
  A1 : Ang
  A2 : Ang
  A3 : Ang
  A4 : Ang
  T1 : Tr
  T2 : Tr
  T3 : Tr
  T4 : Tr

def withVD {β : Type} (E : Env) (g : Nat) (k : VD → β) : β :=
  match E with
  | ⟨F, A1, A2, A3, A4, T1, T2, T3, T4⟩ =>
    natK g fun g' =>
      match F.body[g']! with
      | 0 => k (vd0 F g')
      | 1 => k (vdK F g' 1 A1 T1)
      | 2 => k (vdK F g' 2 A2 T2)
      | 3 => k (vdK F g' 3 A3 T3)
      | _ => k (vdK F g' 4 A4 T4)

def withVDs {β : Type} (E : Env) : List Nat → (List VD → β) → β
  | [], k => k []
  | g :: gs, k => withVD E g fun v => withVDs E gs fun vs => k (v :: vs)

def withAT {β : Type} (E : Env) (b : Nat) (k : Ang → Tr → β) : β :=
  match E with
  | ⟨_, A1, A2, A3, A4, T1, T2, T3, T4⟩ =>
    match b with
    | 1 => k A1 T1
    | 2 => k A2 T2
    | 3 => k A3 T3
    | _ => k A4 T4

/-- Rotation of a list by `s` (elements keep their terms). -/
def rotL {α : Type} (s : Nat) (l : List α) : List α := l.drop s ++ l.take s

/-- The element at `i` (cyclic), passed to the continuation. -/
def withAt {α β : Type} [Inhabited α] (l : List α) (i : Nat) (k : α → β) : β :=
  match (rotL (i % l.length) l) with
  | a :: _ => k a
  | [] => k default

/-! ## Edge contributions (leaf-independent for equal vertex data) -/

/-- `det(x, lc j r)`. -/
def detXL (x : V2) (j : Nat) (r : V2) : DIval :=
  match j with
  | 0 => kneg (sortI x.2)
  | 1 => sortI x.1
  | 2 => kdet x r
  | _ => kdet x (V2.J r)

/-- `det(lc j r, x)`. -/
def detLX (j : Nat) (r : V2) (x : V2) : DIval :=
  match j with
  | 0 => sortI x.2
  | 1 => kneg (sortI x.1)
  | 2 => kdet r x
  | _ => kdet (V2.J r) x

/-- `det(lc j r1, lc l r2)`. -/
def detLL (j : Nat) (r1 : V2) (l : Nat) (r2 : V2) : DIval :=
  match j with
  | 0 => match l with
    | 0 => kpt0
    | 1 => DIval.pt dfxOne
    | 2 => sortI r2.2
    | _ => sortI r2.1
  | 1 => match l with
    | 0 => DIval.pt (-dfxOne)
    | 1 => kpt0
    | 2 => kneg (sortI r2.1)
    | _ => sortI r2.2
  | 2 => detXL r1 l r2
  | _ => detXL (V2.J r1) l r2

structure EC where
  b1 : Nat
  b2 : Nat
  f0 : DIval
  gA : Nat → DIval
  gB : Nat → DIval
  m : Nat → Nat → DIval

def ecK (u v : VD) : EC :=
  ⟨u.b, v.b, kdet u.x0 v.x0, fun j => detLX j u.rq v.x0, fun j => detXL u.x0 j v.rq,
    fun j l => detLL j u.rq l v.rq⟩

/-- Cyclic edges of a list of vertex data. -/
def edgesV (vs : List VD) : List (VD × VD) := List.zip vs (rotL 1 vs)

/-! ## The bound -/

structure AV where
  a : Nat
  b : Nat
  j : Nat
  y0 : Int
  w : Int

def avK (A : Ang) (T : Tr) (a b j : Nat) : AV :=
  let cl := cLo A.h
  ⟨a, b, j, cond (j == 2) (cl.fdiv 2) 0,
    match j with
    | 0 => T.hx
    | 1 => T.hy
    | 2 => -(cl.fdiv 2)
    | _ => A.h⟩

structure Row where
  u : AV
  g : DIval
  ents : List (AV × DIval)
  off : DIval

structure SD where
  F0 : DIval
  rows : List Row

def gOf (ecs : List EC) (u : AV) : DIval :=
  khalf (ksum (ecs.map fun e =>
    kadd (cond (e.b2 == u.b) (e.gB u.j) kpt0) (cond (e.b1 == u.b) (e.gA u.j) kpt0)))

def mOf (ecs : List EC) (u v : AV) : DIval :=
  khalf (ksum ((ecs.filter fun e => e.b1 == u.b && e.b2 == v.b).map fun e => e.m u.j v.j))

def sdOf (ad : List AV) (vs : List VD) : SD :=
  let ecs := (edgesV vs).map fun p => ecK p.1 p.2
  let F0 := khalf (ksum (ecs.map (·.f0)))
  let present := fun (p q : Nat) => ecs.any fun e => (e.b1 == p && e.b2 == q) || (e.b1 == q && e.b2 == p)
  let rows := ad.map fun u =>
    let ents := (ad.filter fun v => v.a == u.a || present u.b v.b).map fun v =>
      (v, cond (present u.b v.b) (kadd (mOf ecs u v) (mOf ecs v u)) kpt0)
    let off := ksum ((ents.filter fun p => !(p.1.a == u.a)).map fun p => kabs (kmulPt (kmulPt p.2 u.w) p.1.w))
    ⟨u, gOf ecs u, ents, off⟩
  ⟨F0, rows⟩

def partsK (sd : SD) (β : Int) : DIval × List DIval :=
  let b2 := DIval.pt (2 * β)
  let hb := fun (u v : AV) (h : DIval) => cond (u.a == v.a && 2 ≤ u.j) (kadd h b2) h
  let g2 := fun (r : Row) => cond (r.u.j == 2) (kadd r.g b2) r.g
  let cRows := sd.rows.filter fun r => r.u.j == 2
  let lin := ksum (cRows.map fun r => kmulPt (g2 r) r.u.y0)
  let quad := ksum (cRows.flatMap fun r =>
    (r.ents.filter fun p => p.1.j == 2).map fun p => khalf (kmulPt (kmulPt (hb r.u p.1 p.2) r.u.y0) p.1.y0))
  let Fy0 := kadd (kadd sd.F0 lin) quad
  let grad := sd.rows.map fun r =>
    kadd (g2 r) (ksum ((r.ents.filter fun p => p.1.j == 2).map fun p => kmulPt (hb r.u p.1 p.2) p.1.y0))
  let pen := ksum (sd.rows.map fun r =>
    let haa := hb r.u r.u ((r.ents.find? fun p => p.1.a == r.u.a).map (·.2) |>.getD kpt0)
    kposI (ksub r.off (kmulPt (kmulPt haa r.u.w) r.u.w)))
  (ksub Fy0 (khalf pen), grad)

def addGrads : List (List DIval) → List DIval → List DIval
  | [], acc => acc
  | g :: gs, acc => addGrads gs (List.zipWith kadd acc g)

def comboK (ad : List AV) (sds : List (SD × Int)) (β : Int) : DIval :=
  let parts := sds.map fun p => (partsK p.1 β, p.2)
  let gsum := addGrads (parts.map fun pt => pt.1.2.map fun g => kmulW g pt.2) (ad.map fun _ => kpt0)
  ksub (ksum (parts.map fun pt => kmulW pt.1.1 pt.2))
    (ksum (List.zipWith (fun u g => kmulPt (kabs g) u.w) ad gsum))

def adOf (E : Env) (sts : List (St × Int)) : List AV :=
  let used := fun (b : Nat) => sts.any fun p => p.1.verts.any fun g => E.F.body[g]! == b
  ((List.range (4 * E.F.k)).filter fun a => used (a / 4 + 1)).map fun a =>
    withAT E (a / 4 + 1) fun A T => avK A T a (a / 4 + 1) (a % 4)

def leafBoundV (E : Env) (sts : List (St × Int)) (vss : List (List VD)) : Int :=
  let ad := adOf E sts
  let sds := List.zipWith (fun p vs => (sdOf ad vs, p.2)) sts vss
  betas.foldl (fun best β => max best (comboK ad sds β).lo) (-(1000 * dfxOne))

/-! ## Validity on vertex data -/

def pairMoveV (F : Fam) (u v : VD) : DIval :=
  if u.b = v.b then
    if u.b = 0 then DIval.pt 0 else (V2.norm (V2.sub F.q[v.g]! F.q[u.g]!)).mul (DIval.pt u.A.h)
  else u.mv.add v.mv

def diffV (F : Fam) (u v : VD) : V2 :=
  if u.b = v.b ∧ u.b ≠ 0 then V2.rot u.A.s u.A.c (V2.sub F.q[v.g]! F.q[u.g]!)
  else V2.sub v.x0 u.x0

def det3V (F : Fam) (a b i : VD) : DIval :=
  if a.b = b.b ∧ a.b = i.b then
    V2.det (V2.sub F.q[b.g]! F.q[a.g]!) (V2.sub F.q[i.g]! F.q[a.g]!)
  else
    let u := diffV F a b
    let v := diffV F a i
    let eab := pairMoveV F a b
    let eai := pairMoveV F a i
    let err := ((eab.mul (V2.norm v)).add (eai.mul (V2.norm u))).add (eab.mul eai)
    let d := kdet u v
    ⟨(d.sub err).lo, (d.add err).hi⟩

def fanVarV (F : Fam) (z : V2) (u v : VD) : DIval :=
  let xa := V2.sub u.x0 z
  let xb := V2.sub v.x0 z
  if u.b = v.b then
    if u.b = 0 then DIval.pt 0
    else
      let w := V2.norm (V2.sub F.q[v.g]! F.q[u.g]!)
      let tz := V2.norm (V2.sub u.T.tc z)
      w.mul ((u.T.trad.mul ((DIval.ofInt 1).add (DIval.pt u.A.h))).add (tz.mul (DIval.pt u.A.h)))
  else
    (u.mv.mul ((V2.norm xb).add v.mv)).add ((V2.norm xa).mul v.mv)

def fanDetPos (F : Fam) (z : V2) (u v : VD) : Bool :=
  pos (ksub (kdet (kvsub u.x0 z) (kvsub v.x0 z)) (fanVarV F z u v)).lo

def fanOKV (F : Fam) (vs : List VD) (zx zy : Int) : Bool :=
  let m := vs.length
  let z : V2 := (DIval.pt zx, DIval.pt zy)
  let xs := vs.map fun v => kvsub v.x0 z
  -- P d, D d: rows by offset `d` (entry `i`: positions `i` and `i + d`)
  let Pd := (List.range (m + 1)).map fun d =>
    cond (1 ≤ d && d < m) (List.zipWith (fun a b => pos (kdet a b).lo) xs (rotL d xs)) (xs.map fun _ => false)
  let Dd := (List.range (m + 1)).map fun d =>
    cond (1 ≤ d && d < m) (List.zipWith (fun a b => pos (kdot a b).lo) xs (rotL d xs)) (xs.map fun _ => false)
  decide (3 ≤ m) &&
  (List.zipWith (fun u v => fanDetPos F z u v) vs (rotL 1 vs)).all id &&
  ((List.range m).any fun s0 => decide (windCost m (fun i d => (Pd.getD d []).getD i false)
    (fun i d => (Dd.getD d []).getD i false) s0 ≤ 7))

def vfanOKV (F : Fam) (piece : List VD) (r : Nat) : Bool :=
  let l := rotL r piece
  match l with
  | a :: b :: rest =>
    (rest.all fun x => pos (det3V F a b x).lo) &&
    (List.zipWith (fun x y => pos (det3V F a x y).lo) (b :: rest) rest).all id
  | _ => true

def chordOKV (F : Fam) (maxsmall : Nat) : CT → List VD → Bool
  | .small, piece => decide (piece.length ≤ maxsmall)
  | .vfan r, piece => decide (r < piece.length) && decide (3 ≤ piece.length) && vfanOKV F piece r
  | .cut s t L R, piece =>
    let n := piece.length
    let dd := (t + n - s) % n
    decide (s < n) && decide (t < n) && decide (2 ≤ dd) && decide (dd + 2 ≤ n) &&
    withAt piece s fun ps => withAt piece t fun pt =>
    pos ((V2.norm (diffV F ps pt)).sub (pairMoveV F ps pt)).lo &&
    (((rotL s piece).take dd).drop 1 |>.all fun x => ile (det3V F ps pt x).hi 0) &&
    (((rotL t piece).take (n - dd)).drop 1 |>.all fun x => nonneg (det3V F ps pt x).lo) &&
    chordOKV F maxsmall L ((rotL s piece).take (dd + 1)) &&
    chordOKV F maxsmall R ((rotL t piece).take (n - dd + 1))

def stOKV (F : Fam) (maxsmall : Nat) (st : St) (vs : List VD) : Bool :=
  match st with
  | .small v => decide (v.length ≤ maxsmall) && v.Nodup && v.all (· < F.body.size)
  | .fan v zx zy => v.Nodup && v.all (· < F.body.size) && fanOKV F vs zx zy
  | .chord v t => v.Nodup && v.all (· < F.body.size) && chordOKV F maxsmall t vs

/-! ## The leaf test -/

def withSts {β : Type} (E : Env) : List (St × Int) → (List (List VD) → β) → β
  | [], k => k []
  | p :: ps, k => withVDs E p.1.verts fun vs => withSts E ps fun vss => k (vs :: vss)

def leafCoreK (E : Env) (maxsmall : Nat) (tauHi : Int) (r : Rec) : Bool :=
  withSts E r.sts fun vss =>
    decide (r.sts ≠ []) &&
    (List.zipWith (fun p vs => nonneg p.2 && stOKV E.F maxsmall p.1 vs) r.sts vss).all id &&
    decide ((r.sts.map (·.2)).foldl (· + ·) 0 ≤ dfxOne) &&
    decide (tauHi < leafBoundV E r.sts vss)

def leafOKK (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) : Bool :=
  arrK 12 lo.toList fun l => arrK 12 hi.toList fun h =>
    match l, h with
    | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11], [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] =>
      leafCoreK ⟨F, angK l0 h0, angK l3 h3, angK l6 h6, angK l9 h9,
          trK l1 h1 l2 h2, trK l4 h4 l5 h5, trK l7 h7 l8 h8, trK l10 h10 l11 h11⟩ maxsmall tauHi r
    | _, _ => false

end WormK3
