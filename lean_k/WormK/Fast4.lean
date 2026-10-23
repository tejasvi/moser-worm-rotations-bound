import WormK.Fast3

/-!
# Kernel-native Nat comparisons, Bool plumbing, kernel primitives in the validity checks

Same values as `WormK3` (`WormK/Fast3.lean`), on the same structures:

* Nat comparisons by `Nat.beq` / `Nat.ble` / `Nat.blt` (kernel GMP operations, one step on literals) instead of
  `==` / `decide (· ≤ ·)` through `BEq`/`Decidable` instances;
* `if`/`decide` replaced by `bsel` and Bool functions;
* the validity checks, the vertex data, the norms (square roots by structural Newton steps with a final check)
  and the sine/cosine enclosures on the interval primitives of `WormK3`;
* the bound model: edge filters and body-pair presence on canonical body numbers (shared within a structure);
* the beta loop short-circuits (`tauHi < max_β f β` as `∃ β, tauHi < f β`; `β = 0` comes first and clears `tauHi`
  on all leaves of the sampled chunks).
-/

namespace WormK4

open WormCore MoserWorm
open WormK2 (natK intK arrK Ang Tr angK trK)
open WormK3 (iadd ineg isub imul ile nonneg pos shr shr1 cshr bsel kmin kmax isD kadd ksub kneg kpt0 kmul kmulPt
  sortI kmulW khalf kabs kposI kdet kdot kvsub ksum VD Env withVD withVDs withAT rotL withAt EC ecK edgesV AV avK
  Row SD)

/-! ## Bool helpers -/

/-- `l.Nodup` for lists of naturals. -/
def nodupK : List Nat → Bool
  | [] => true
  | a :: l => l.all (fun b => !(Nat.beq a b)) && nodupK l

/-- `a < b`. -/
def ilt (a b : Int) : Bool := !(ile b a)

/-- `V2.add` on primitives. -/
def kvadd (u v : V2) : V2 := (kadd u.1 v.1, kadd u.2 v.2)

def posNatImpl (x : Int) : Nat := (max x 0).toNat

/-- `(max x 0).toNat`. -/
@[implemented_by posNatImpl]
def posNat (x : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun n => n) (fun _ => 0) x

/-- Newton steps of `Nat.sqrt.iter` with structural fuel. -/
def newtonK (n : Nat) : Nat → Nat → Nat
  | 0, g => g
  | f + 1, g =>
    let next := Nat.div (Nat.add g (Nat.div n g)) 2
    bsel (Nat.blt next g) (newtonK n f next) g

/-- `Nat.sqrt n`: Newton steps, then the defining inequalities are checked (fallback `Nat.sqrt`). -/
def isqrtK (n : Nat) : Nat :=
  let r := bsel (Nat.ble n 1) n (newtonK n 12 (Nat.shiftLeft 1 (Nat.add (Nat.div (Nat.log2 n) 2) 1)))
  bsel (Nat.ble (Nat.mul r r) n && Nat.blt n (Nat.mul (Nat.add r 1) (Nat.add r 1))) r (Nat.sqrt n)

/-- `DIval.sq` on primitives. -/
def ksq (a : DIval) : DIval :=
  let t := kabs a
  ⟨shr (imul t.lo t.lo), cshr (imul t.hi t.hi)⟩

/-- `DIval.sqrtI` on primitives. -/
def ksqrtI (a : DIval) : DIval :=
  let lo := posNat a.lo
  let hi := posNat a.hi
  let rl := isqrtK (Nat.shiftLeft lo 56)
  let rh := isqrtK (Nat.shiftLeft hi 56)
  ⟨Int.ofNat rl, bsel (Nat.beq (Nat.mul rh rh) (Nat.shiftLeft hi 56)) (Int.ofNat rh) (Int.ofNat (Nat.add rh 1))⟩

/-- `DIval.norm2` on primitives. -/
def knorm2 (x y : DIval) : DIval := ksqrtI (kadd (ksq x) (ksq y))

/-- `V2.norm` on primitives. -/
def vnormK (a : V2) : DIval := knorm2 a.1 a.2

/-- `V2.rot s c v` on primitives. -/
def krot (s c : DIval) (v : V2) : V2 := (ksub (kmul c v.1) (kmul s v.2), kadd (kmul s v.1) (kmul c v.2))

/-! ## Sine and cosine enclosures on primitives -/

def hornerK (x2 : DIval) : List Int → DIval
  | [] => kpt0
  | [c] => ⟨c, iadd c 1⟩
  | c :: c' :: rest => ksub ⟨c, iadd c 1⟩ (kmul x2 (hornerK x2 (c' :: rest)))

def sinCoreK (x : DIval) : DIval :=
  let x2 := ksq x
  let acc := hornerK x2 DIval.sinCoeffs
  let s := kmul x (ksub (DIval.pt dfxOne) (kmul x2 acc))
  ⟨isub s.lo 1, iadd s.hi 1⟩

def cosCoreK (x : DIval) : DIval :=
  let x2 := ksq x
  let acc := hornerK x2 DIval.cosCoeffs
  let c := ksub (DIval.pt dfxOne) (kmul x2 acc)
  ⟨isub c.lo 1, iadd c.hi 1⟩

/-- `⟨pi2Lo, pi2Lo + 1⟩`. -/
def pi2I : DIval := ⟨113187804032455044, 113187804032455045⟩

/-- `pi4Lo + 64`. -/
def pi4S : Int := 56593902016227586

def kpi2Residual (t k : Int) : DIval := ksub (DIval.pt t) (kmul (DIval.pt (imul k dfxOne)) pi2I)

def adjustKK (t : Int) : Nat → Int → Int
  | 0, k => k
  | fuel + 1, k =>
    let x := kpi2Residual t k
    bsel (ilt pi4S x.hi) (adjustKK t fuel (iadd k 1)) (bsel (ilt x.lo (ineg pi4S)) (adjustKK t fuel (isub k 1)) k)

/-- `clamp1` on primitives. -/
def kclamp1 (a : DIval) : DIval := ⟨kmax a.lo (-72057594037927936), kmin a.hi 72057594037927936⟩

def sincosK (t : Int) : DIval × DIval :=
  let num := iadd t DIval.pi4Lo
  let k0 := num.fdiv DIval.pi2Lo
  let k := adjustKK t 8 k0
  let x := kpi2Residual t k
  let sc := sinCoreK x
  let cc := cosCoreK x
  let r :=
    match (k % 4).toNat with
    | 0 => (sc, cc)
    | 1 => (cc, kneg sc)
    | 2 => (kneg sc, kneg cc)
    | _ => (kneg cc, sc)
  (kclamp1 r.1, kclamp1 r.2)

def sincosIvK (t : DIval) : DIval × DIval :=
  let m := t.lo + (t.hi - t.lo) / 2
  let rad := kmax (isub t.hi m) (isub m t.lo)
  let sc := sincosK m
  (kclamp1 ⟨isub sc.1.lo rad, iadd sc.1.hi rad⟩, kclamp1 ⟨isub sc.2.lo rad, iadd sc.2.hi rad⟩)

/-! ## Per-body data and vertex data on primitives -/

def angK4 (tl th : Int) : Ang :=
  let t := (iadd tl th).fdiv 2
  let hθ := kmax (isub th t) (isub t tl)
  let sc := sincosIvK ⟨toLo t, toHi t⟩
  ⟨sc.1, sc.2, toHi hθ⟩

def trK4 (xl xh yl yh : Int) : Tr :=
  let tx := (iadd xl xh).fdiv 2
  let ty := (iadd yl yh).fdiv 2
  let hx := toHi (kmax (isub xh tx) (isub tx xl))
  let hy := toHi (kmax (isub yh ty) (isub ty yl))
  ⟨(⟨toLo tx, toHi tx⟩, ⟨toLo ty, toHi ty⟩), hx, hy, knorm2 (DIval.pt hx) (DIval.pt hy)⟩

def vdK4 (F : Fam) (g b : Nat) (A : Ang) (T : Tr) : VD :=
  let rq := krot A.s A.c F.q[g]!
  ⟨g, b, A, T, rq, kvadd T.tc rq, kadd (kmulPt F.qn[g]! A.h) T.trad⟩

def withVD4 {β : Type} (E : Env) (g : Nat) (k : VD → β) : β :=
  match E with
  | ⟨F, A1, A2, A3, A4, T1, T2, T3, T4⟩ =>
    natK g fun g' =>
      match F.body[g']! with
      | 0 => k (WormK3.vd0 F g')
      | 1 => k (vdK4 F g' 1 A1 T1)
      | 2 => k (vdK4 F g' 2 A2 T2)
      | 3 => k (vdK4 F g' 3 A3 T3)
      | _ => k (vdK4 F g' 4 A4 T4)

def withVDs4 {β : Type} (E : Env) : List Nat → (List VD → β) → β
  | [], k => k []
  | g :: gs, k => withVD4 E g fun v => withVDs4 E gs fun vs => k (v :: vs)

/-! ## The bound -/

def avK4 (A : Ang) (T : Tr) (a b j : Nat) : AV :=
  let cl := cLo A.h
  ⟨a, b, j, cond (Nat.beq j 2) (cl.fdiv 2) 0,
    match j with
    | 0 => T.hx
    | 1 => T.hy
    | 2 => -(cl.fdiv 2)
    | _ => A.h⟩

def gOf4 (ecs : List EC) (u : AV) : DIval :=
  khalf (ksum (ecs.map fun e =>
    kadd (cond (Nat.beq e.b2 u.b) (e.gB u.j) kpt0) (cond (Nat.beq e.b1 u.b) (e.gA u.j) kpt0)))

/-- `mOf` with the bodies `p = u.b`, `q = v.b` passed as canonical terms (the edge filter is shared). -/
def mOf4 (ecs : List EC) (p q : Nat) (u v : AV) : DIval :=
  khalf (ksum ((ecs.filter fun e => Nat.beq e.b1 p && Nat.beq e.b2 q).map fun e => e.m u.j v.j))

/-- Presence of the body pair `(p, q)` (either orientation) among the edges. -/
def presentK (ecs : List EC) (p q : Nat) : Bool :=
  ecs.any fun e => (Nat.beq e.b1 p && Nat.beq e.b2 q) || (Nat.beq e.b1 q && Nat.beq e.b2 p)

def sdOf4 (ad : List AV) (vs : List VD) : SD :=
  let ecs := (edgesV vs).map fun p => ecK p.1 p.2
  let F0 := khalf (ksum (ecs.map (·.f0)))
  let rows := ad.map fun u => natK u.b fun ub =>
    let ents := (ad.filter fun v => Nat.beq v.a u.a || natK v.b fun vb => presentK ecs ub vb).map fun v =>
      (v, natK v.b fun vb => cond (presentK ecs ub vb) (kadd (mOf4 ecs ub vb u v) (mOf4 ecs vb ub v u)) kpt0)
    let off := ksum ((ents.filter fun p => !(Nat.beq p.1.a u.a)).map fun p =>
      kabs (kmulPt (kmulPt p.2 u.w) p.1.w))
    ⟨u, gOf4 ecs u, ents, off⟩
  ⟨F0, rows⟩

def partsK4 (sd : SD) (β : Int) : DIval × List DIval :=
  let b2 := DIval.pt (2 * β)
  let hb := fun (u v : AV) (h : DIval) => cond (Nat.beq u.a v.a && Nat.ble 2 u.j) (kadd h b2) h
  let g2 := fun (r : Row) => cond (Nat.beq r.u.j 2) (kadd r.g b2) r.g
  let cRows := sd.rows.filter fun r => Nat.beq r.u.j 2
  let lin := ksum (cRows.map fun r => kmulPt (g2 r) r.u.y0)
  let quad := ksum (cRows.flatMap fun r =>
    (r.ents.filter fun p => Nat.beq p.1.j 2).map fun p => khalf (kmulPt (kmulPt (hb r.u p.1 p.2) r.u.y0) p.1.y0))
  let Fy0 := kadd (kadd sd.F0 lin) quad
  let grad := sd.rows.map fun r =>
    kadd (g2 r) (ksum ((r.ents.filter fun p => Nat.beq p.1.j 2).map fun p => kmulPt (hb r.u p.1 p.2) p.1.y0))
  let pen := ksum (sd.rows.map fun r =>
    let haa := hb r.u r.u ((r.ents.find? fun p => Nat.beq p.1.a r.u.a).map (·.2) |>.getD kpt0)
    kposI (ksub r.off (kmulPt (kmulPt haa r.u.w) r.u.w)))
  (ksub Fy0 (khalf pen), grad)

def comboK4 (ad : List AV) (sds : List (SD × Int)) (β : Int) : DIval :=
  let parts := sds.map fun p => (partsK4 p.1 β, p.2)
  let gsum := WormK3.addGrads (parts.map fun pt => pt.1.2.map fun g => kmulW g pt.2) (ad.map fun _ => kpt0)
  ksub (ksum (parts.map fun pt => kmulW pt.1.1 pt.2))
    (ksum (List.zipWith (fun u g => kmulPt (kabs g) u.w) ad gsum))

def adOf4 (E : Env) (sts : List (St × Int)) : List AV :=
  let used := fun (b : Nat) => sts.any fun p => p.1.verts.any fun g => Nat.beq E.F.body[g]! b
  ((List.range (4 * E.F.k)).filter fun a => natK (a / 4 + 1) used).map fun a =>
    withAT E (a / 4 + 1) fun A T => avK4 A T a (a / 4 + 1) (a % 4)

/-- `-(1000 · 2⁵⁶)`. -/
def boundInit : Int := -72057594037927936000

def leafBoundV4 (E : Env) (sts : List (St × Int)) (vss : List (List VD)) : Int :=
  let ad := adOf4 E sts
  let sds := List.zipWith (fun p vs => (sdOf4 ad vs, p.2)) sts vss
  betas.foldl (fun best β => kmax best (comboK4 ad sds β).lo) boundInit

/-- `tauHi < leafBoundV4 E sts vss`, short-circuiting over the betas. -/
def boundOK4 (E : Env) (sts : List (St × Int)) (vss : List (List VD)) (tauHi : Int) : Bool :=
  let ad := adOf4 E sts
  let sds := List.zipWith (fun p vs => (sdOf4 ad vs, p.2)) sts vss
  ilt tauHi boundInit || betas.any fun β => ilt tauHi (comboK4 ad sds β).lo

/-! ## Validity on vertex data -/

def pairMoveV4 (F : Fam) (u v : VD) : DIval :=
  bsel (Nat.beq u.b v.b)
    (bsel (Nat.beq u.b 0) kpt0 (kmulPt (vnormK (kvsub F.q[v.g]! F.q[u.g]!)) u.A.h))
    (kadd u.mv v.mv)

def diffV4 (F : Fam) (u v : VD) : V2 :=
  bsel (Nat.beq u.b v.b && !(Nat.beq u.b 0)) (krot u.A.s u.A.c (kvsub F.q[v.g]! F.q[u.g]!)) (kvsub v.x0 u.x0)

def det3V4 (F : Fam) (a b i : VD) : DIval :=
  bsel (Nat.beq a.b b.b && Nat.beq a.b i.b)
    (kdet (kvsub F.q[b.g]! F.q[a.g]!) (kvsub F.q[i.g]! F.q[a.g]!))
    (let u := diffV4 F a b
     let v := diffV4 F a i
     let eab := pairMoveV4 F a b
     let eai := pairMoveV4 F a i
     let err := kadd (kadd (kmul eab (vnormK v)) (kmul eai (vnormK u))) (kmul eab eai)
     let d := kdet u v
     ⟨(ksub d err).lo, (kadd d err).hi⟩)

def fanVarV4 (F : Fam) (z : V2) (u v : VD) : DIval :=
  bsel (Nat.beq u.b v.b)
    (bsel (Nat.beq u.b 0) kpt0
      (let w := vnormK (kvsub F.q[v.g]! F.q[u.g]!)
       let tz := vnormK (kvsub u.T.tc z)
       kmul w (kadd (kmul u.T.trad (kadd (DIval.pt dfxOne) (DIval.pt u.A.h))) (kmulPt tz u.A.h))))
    (kadd (kmul u.mv (kadd (vnormK (kvsub v.x0 z)) v.mv)) (kmul (vnormK (kvsub u.x0 z)) v.mv))

def fanDetPos4 (F : Fam) (z : V2) (u v : VD) : Bool :=
  pos (ksub (kdet (kvsub u.x0 z) (kvsub v.x0 z)) (fanVarV4 F z u v)).lo

def fanOKV4 (F : Fam) (vs : List VD) (zx zy : Int) : Bool :=
  let m := vs.length
  let z : V2 := (DIval.pt zx, DIval.pt zy)
  let xs := vs.map fun v => kvsub v.x0 z
  let Pd := (List.range (m + 1)).map fun d =>
    cond (Nat.ble 1 d && Nat.blt d m) (List.zipWith (fun a b => pos (kdet a b).lo) xs (rotL d xs))
      (xs.map fun _ => false)
  let Dd := (List.range (m + 1)).map fun d =>
    cond (Nat.ble 1 d && Nat.blt d m) (List.zipWith (fun a b => pos (kdot a b).lo) xs (rotL d xs))
      (xs.map fun _ => false)
  Nat.ble 3 m &&
  (List.zipWith (fun u v => fanDetPos4 F z u v) vs (rotL 1 vs)).all id &&
  ((List.range m).any fun s0 => Nat.ble (windCost m (fun i d => (Pd.getD d []).getD i false)
    (fun i d => (Dd.getD d []).getD i false) s0) 7)

def vfanOKV4 (F : Fam) (piece : List VD) (r : Nat) : Bool :=
  let l := rotL r piece
  match l with
  | a :: b :: rest =>
    (rest.all fun x => pos (det3V4 F a b x).lo) &&
    (List.zipWith (fun x y => pos (det3V4 F a x y).lo) (b :: rest) rest).all id
  | _ => true

def chordOKV4 (F : Fam) (maxsmall : Nat) : CT → List VD → Bool
  | .small, piece => Nat.ble piece.length maxsmall
  | .vfan r, piece => Nat.blt r piece.length && Nat.ble 3 piece.length && vfanOKV4 F piece r
  | .cut s t L R, piece =>
    let n := piece.length
    let dd := (t + n - s) % n
    Nat.blt s n && Nat.blt t n && Nat.ble 2 dd && Nat.ble (dd + 2) n &&
    withAt piece s fun ps => withAt piece t fun pt =>
    pos (ksub (vnormK (diffV4 F ps pt)) (pairMoveV4 F ps pt)).lo &&
    (((rotL s piece).take dd).drop 1 |>.all fun x => ile (det3V4 F ps pt x).hi 0) &&
    (((rotL t piece).take (n - dd)).drop 1 |>.all fun x => nonneg (det3V4 F ps pt x).lo) &&
    chordOKV4 F maxsmall L ((rotL s piece).take (dd + 1)) &&
    chordOKV4 F maxsmall R ((rotL t piece).take (n - dd + 1))

def stOKV4 (F : Fam) (maxsmall : Nat) (st : St) (vs : List VD) : Bool :=
  match st with
  | .small v => Nat.ble v.length maxsmall && nodupK v && v.all (fun g => Nat.blt g F.body.size)
  | .fan v zx zy => nodupK v && v.all (fun g => Nat.blt g F.body.size) && fanOKV4 F vs zx zy
  | .chord v t => nodupK v && v.all (fun g => Nat.blt g F.body.size) && chordOKV4 F maxsmall t vs

/-! ## The leaf test -/

def withSts {β : Type} (E : Env) : List (St × Int) → (List (List VD) → β) → β
  | [], k => k []
  | p :: ps, k => withVDs4 E p.1.verts fun vs => withSts E ps fun vss => k (vs :: vss)

def leafCoreK4 (E : Env) (maxsmall : Nat) (tauHi : Int) (r : Rec) : Bool :=
  withSts E r.sts fun vss =>
    !r.sts.isEmpty &&
    (List.zipWith (fun p vs => nonneg p.2 && stOKV4 E.F maxsmall p.1 vs) r.sts vss).all id &&
    ile ((r.sts.map (·.2)).foldl iadd 0) dfxOne &&
    boundOK4 E r.sts vss tauHi

def leafOKK4 (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) : Bool :=
  arrK 12 lo.toList fun l => arrK 12 hi.toList fun h =>
    match l, h with
    | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11], [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] =>
      leafCoreK4 ⟨F, angK4 l0 h0, angK4 l3 h3, angK4 l6 h6, angK4 l9 h9,
          trK4 l1 h1 l2 h2, trK4 l4 h4 l5 h5, trK4 l7 h7 l8 h8, trK4 l10 h10 l11 h11⟩ maxsmall tauHi r
    | _, _ => false

end WormK4
