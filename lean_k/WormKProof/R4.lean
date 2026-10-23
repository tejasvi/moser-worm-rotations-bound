import WormK.Walk4
import WormKProof.R4Prims
import WormKProof.Walk

/-!
# `WormK4` = `WormK3`

`WormK4.leafOKK4 = WormK3.leafOKK` for all arguments (no hypotheses), hence with `WormK3.leafOKK_eq` the `WormK4`
leaf test is the checker's `leafOK`; the same for the refined test (`leafOKRK4`), the walk and the piece check.
-/

namespace WormK4

open WormCore MoserWorm WormK3
open WormK2 (natK intK arrK Ang Tr angK trK)

/-! ## The bound -/

theorem avK4_eq (A : Ang) (T : Tr) (a b j : Nat) : avK4 A T a b j = avK A T a b j := rfl

theorem gOf4_eq (ecs : List EC) (u : AV) : gOf4 ecs u = gOf ecs u := rfl

theorem mOf4_eq (ecs : List EC) (u v : AV) : mOf4 ecs u.b v.b u v = mOf ecs u v := rfl

theorem sdOf4_eq (ad : List AV) (vs : List VD) : sdOf4 ad vs = sdOf ad vs := by
  simp only [sdOf4, sdOf, natK_eq, mOf4_eq, gOf4_eq]
  rfl

theorem partsK4_eq (sd : SD) (β : Int) : partsK4 sd β = partsK sd β := by
  simp only [partsK4, partsK, nble_eq]
  rfl

theorem comboK4_eq (ad : List AV) (sds : List (SD × Int)) (β : Int) : comboK4 ad sds β = comboK ad sds β := by
  simp only [comboK4, comboK, partsK4_eq]

theorem adOf4_eq (E : Env) (sts : List (St × Int)) : adOf4 E sts = adOf E sts := by
  simp only [adOf4, adOf, natK_eq, avK4_eq]
  rfl

theorem boundInit_eq : boundInit = -(1000 * dfxOne) := by decide

theorem leafBoundV4_eq (E : Env) (sts : List (St × Int)) (vss : List (List VD)) :
    leafBoundV4 E sts vss = leafBoundV E sts vss := by
  simp only [leafBoundV4, leafBoundV, adOf4_eq, sdOf4_eq, comboK4_eq, kmax_eq, boundInit_eq]

theorem lt_max' (t a b : Int) : t < max a b ↔ t < a ∨ t < b := by omega

theorem lt_foldl_max (t : Int) (f : Int → Int) : ∀ (l : List Int) (init : Int),
    t < l.foldl (fun best β => max best (f β)) init ↔ t < init ∨ ∃ β ∈ l, t < f β
  | [], init => by simp
  | β :: l, init => by
    rw [List.foldl_cons, lt_foldl_max t f l, lt_max']
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem boundOK4_eq (E : Env) (sts : List (St × Int)) (vss : List (List VD)) (tauHi : Int) :
    boundOK4 E sts vss tauHi = decide (tauHi < leafBoundV E sts vss) := by
  simp only [boundOK4, leafBoundV, ilt_eq, adOf4_eq, sdOf4_eq, comboK4_eq, boundInit_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, lt_foldl_max]

/-! ## Validity -/

theorem pairMoveV4_eq (F : Fam) (u v : VD) : pairMoveV4 F u v = pairMoveV F u v := by
  simp only [pairMoveV4, pairMoveV, bsel_eq, nbeq_dec, vnormK_eq, kvsub_eq, kmulPt_eq, kadd_eq, decide_eq_true_eq]
  rfl

theorem diffV4_eq (F : Fam) (u v : VD) : diffV4 F u v = diffV F u v := by
  simp only [diffV4, diffV, bsel_eq, nbeq_dec, krot_eq, kvsub_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]

theorem det3V4_eq (F : Fam) (a b i : VD) : det3V4 F a b i = det3V F a b i := by
  simp only [det3V4, det3V, bsel_eq, nbeq_dec, kdet_eq, kvsub_eq, diffV4_eq, pairMoveV4_eq, vnormK_eq, kmul_eq,
    kadd_eq, ksub_eq, Bool.and_eq_true, decide_eq_true_eq]

theorem fanVarV4_eq (F : Fam) (z : V2) (u v : VD) : fanVarV4 F z u v = fanVarV F z u v := by
  simp only [fanVarV4, fanVarV, bsel_eq, nbeq_dec, vnormK_eq, kvsub_eq, kmul_eq, kadd_eq, kmulPt_eq, ofInt_one,
    decide_eq_true_eq]
  rfl

theorem fanDetPos4_eq (F : Fam) (z : V2) (u v : VD) : fanDetPos4 F z u v = fanDetPos F z u v := by
  simp only [fanDetPos4, fanDetPos, fanVarV4_eq]

theorem fanOKV4_eq (F : Fam) (vs : List VD) (zx zy : Int) : fanOKV4 F vs zx zy = fanOKV F vs zx zy := by
  simp only [fanOKV4, fanOKV, nble_eq, nblt_eq, fanDetPos4_eq]

theorem vfanOKV4_eq (F : Fam) (piece : List VD) (r : Nat) : vfanOKV4 F piece r = vfanOKV F piece r := by
  simp only [vfanOKV4, vfanOKV, det3V4_eq]
  rfl

theorem chordOKV4_eq (F : Fam) (maxsmall : Nat) : ∀ (t : CT) (piece : List VD),
    chordOKV4 F maxsmall t piece = chordOKV F maxsmall t piece
  | .small, piece => by simp only [chordOKV4, chordOKV, nble_eq]
  | .vfan r, piece => by simp only [chordOKV4, chordOKV, nble_eq, nblt_eq, vfanOKV4_eq]
  | .cut s t L R, piece => by
    simp only [chordOKV4, chordOKV, nble_eq, nblt_eq, det3V4_eq, diffV4_eq, pairMoveV4_eq, vnormK_eq, ksub_eq,
      chordOKV4_eq F maxsmall L, chordOKV4_eq F maxsmall R]

theorem stOKV4_eq (F : Fam) (maxsmall : Nat) (st : St) (vs : List VD) :
    stOKV4 F maxsmall st vs = stOKV F maxsmall st vs := by
  cases st <;> simp only [stOKV4, stOKV, nble_eq, nblt_eq, nodupK_eq, fanOKV4_eq, chordOKV4_eq]

/-! ## The leaf test -/

theorem leafCoreK4_eq (E : Env) (maxsmall : Nat) (tauHi : Int) (r : Rec) :
    leafCoreK4 E maxsmall tauHi r = leafCoreK E maxsmall tauHi r := by
  simp only [leafCoreK4, leafCoreK, withSts4_eq, WormK3.withSts_eq, stOKV4_eq, boundOK4_eq, ile_eq]
  have h1 : (!r.sts.isEmpty) = decide (r.sts ≠ []) := by cases r.sts <;> rfl
  have h2 : (r.sts.map (·.2)).foldl iadd 0 = (r.sts.map (·.2)).foldl (· + ·) 0 := by
    congr 1; funext a b; exact iadd_eq a b
  rw [h1, h2]

/-- **`WormK4` = `WormK3`**, for all arguments. -/
theorem leafOKK4_eq3 (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) :
    leafOKK4 F maxsmall tauHi lo hi r = WormK3.leafOKK F maxsmall tauHi lo hi r := by
  simp only [leafOKK4, WormK3.leafOKK, angK4_eq, trK4_eq, leafCoreK4_eq]
  rfl

/-- **The `WormK4` leaf test is the checker's `leafOK`** (any family with four moving bodies, 12-coordinate boxes). -/
theorem leafOKK4_eq (F : Fam) (hF : FamOK F) (lo hi : Array Int) (maxsmall : Nat) (tauHi : Int) (r : Rec)
    (hlo : lo.size = 12) (hhi : hi.size = 12) :
    leafOKK4 F maxsmall tauHi lo hi r = leafOK F maxsmall tauHi lo hi r := by
  rw [leafOKK4_eq3]
  exact WormK3.leafOKK_eq F hF lo hi maxsmall tauHi r hlo hhi

/-! ## Refinement, walk, pieces -/

theorem leafOKRK4_eq3 (F : Fam) (maxsmall : Nat) (tauHi : Int) : ∀ (d : Nat) (lo hi : Array Int) (r : Rec),
    leafOKRK4 F maxsmall tauHi d lo hi r = WormK3.leafOKRK F maxsmall tauHi d lo hi r
  | 0, lo, hi, r => by simp only [leafOKRK4, WormK3.leafOKRK, leafOKK4_eq3]
  | d + 1, lo, hi, r => by
    simp only [leafOKRK4, WormK3.leafOKRK, leafOKK4_eq3, leafOKRK4_eq3 F maxsmall tauHi d]

/-- **The `WormK4` refined leaf test is the checker's `leafOKR`** (same statement as `WormK3.leafOKRK_eq`). -/
theorem leafOKRK4_eq (F : Fam) (hF : FamOK F) (maxsmall : Nat) (tauHi : Int) (d : Nat) (lo hi : Array Int)
    (r : Rec) (hlo : lo.size = 12) (hhi : hi.size = 12) :
    leafOKRK4 F maxsmall tauHi d lo hi r = leafOKR F maxsmall tauHi d lo hi r := by
  rw [leafOKRK4_eq3]
  exact WormK3.leafOKRK_eq F hF maxsmall tauHi d lo hi r hlo hhi

theorem walkK4_eq3 (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) :
    ∀ (fuel : Nat) (cs : List Char) (st : List (Array Int × Array Int)) (recs : List Rec),
      walkK4 F maxsmall tauHi rdepth fuel cs st recs = WormK3.walkK F maxsmall tauHi rdepth fuel cs st recs
  | 0, _, _, _ => rfl
  | _ + 1, [], [], recs => rfl
  | fuel + 1, c :: cs, (lo, hi) :: st, recs => by
    simp only [walkK4, WormK3.walkK, leafOKRK4_eq3, walkK4_eq3 F maxsmall tauHi rdepth fuel]
    rfl
  | _ + 1, [], _ :: _, _ => rfl
  | _ + 1, _ :: _, [], _ => rfl

theorem pieceOK4_eq3 (box : Array Int × Array Int) (codes : List Char) (recs : List Rec) :
    pieceOK4 box codes recs = WormK3.pieceOK box codes recs := by
  simp only [pieceOK4, WormK3.pieceOK, walkK4_eq3]
  rfl

end WormK4
