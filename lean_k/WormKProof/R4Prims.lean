import WormK.Fast4
import WormKProof.Prims
import WormKProof.CPS

/-!
# The `WormK4` primitives compute the `WormK3` and core operations

Nat comparisons (`Nat.beq`, `Nat.ble`, `Nat.blt`), `nodupK`, `ilt`, the square root `isqrtK = Nat.sqrt`, the interval
square, square root and norm, rotations, the sine/cosine enclosures, the per-body data `angK4 = angK`,
`trK4 = trK`, the vertex data `vdK4 = vdK` and the continuation-passing helpers.
-/

namespace WormK4

open WormCore MoserWorm WormK3
open WormK2 (natK intK arrK Ang Tr angK trK)

/-! ## Comparisons -/

theorem nbeq_eq (a b : Nat) : Nat.beq a b = (a == b) := rfl

theorem nbeq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr; simp only [Nat.beq_eq, decide_eq_true_eq]

theorem nble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr; simp only [Nat.ble_eq, decide_eq_true_eq]

theorem nblt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr; simp only [Nat.blt_eq, decide_eq_true_eq]

theorem ilt_eq (a b : Int) : ilt a b = decide (a < b) := by
  simp only [ilt, ile_eq]
  by_cases h : a < b
  · simp [h, Int.not_le.mpr h]
  · simp [h, Int.not_lt.mp h]

theorem nodupK_eq (l : List Nat) : nodupK l = decide l.Nodup := by
  induction l with
  | nil => simp [nodupK]
  | cons a l ih =>
    simp only [nodupK, ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.nodup_cons]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hm => ?_, h2⟩
      have := h1 a hm
      simp [nbeq_dec] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun b hb => ?_, h2⟩
      rw [nbeq_dec]
      simp only [decide_eq_false_iff_not]
      rintro rfl
      exact h1 hb

/-! ## Square roots and norms -/

theorem kvadd_eq (u v : V2) : kvadd u v = V2.add u v := by
  simp only [kvadd, V2.add, kadd_eq]

theorem posNat_eq (x : Int) : posNat x = (max x 0).toNat := by
  rcases x with n | n
  · show n = (max (Int.ofNat n) 0).toNat
    rw [Int.max_eq_left (by simp)]
    rfl
  · show 0 = (max (Int.negSucc n) 0).toNat
    rw [Int.max_eq_right (Int.le_of_lt (Int.negSucc_lt_zero n))]
    rfl

theorem sqrt_unique (n r : Nat) (h1 : r * r ≤ n) (h2 : n < (r + 1) * (r + 1)) : r = Nat.sqrt n := by
  have a1 := Nat.sqrt_le n
  have a2 := Nat.lt_succ_sqrt n
  rcases Nat.lt_trichotomy r (Nat.sqrt n) with h | h | h
  · have : (r + 1) * (r + 1) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h h
    omega
  · exact h
  · have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ r * r := Nat.mul_le_mul h h
    simp only [Nat.succ_eq_add_one] at a2
    omega

theorem isqrtK_eq (n : Nat) : isqrtK n = Nat.sqrt n := by
  simp only [isqrtK]
  generalize bsel (Nat.ble n 1) n _ = r
  rw [bsel_eq]
  split
  · next h =>
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    exact sqrt_unique n r h.1 h.2
  · rfl

theorem ksq_eq (a : DIval) : ksq a = DIval.sq a := by
  simp only [ksq, DIval.sq, kabs_eq, shr_eq, cshr_eq, imul_eq]

theorem hi2_eq (rh x : Nat) :
    bsel (Nat.beq (Nat.mul rh rh) x) (Int.ofNat rh) (Int.ofNat (Nat.add rh 1)) =
      (if rh * rh = x then (rh : Int) else (rh : Int) + 1) := by
  rw [bsel_eq, nbeq_dec]
  by_cases h : rh * rh = x
  · have h' : Nat.mul rh rh = x := h
    simp only [h', h, decide_true, if_true]
    rfl
  · have h' : ¬ Nat.mul rh rh = x := h
    simp only [h', h, decide_false, if_false, Bool.false_eq_true]
    show Int.ofNat (rh + 1) = (rh : Int) + 1
    simp

theorem ksqrtI_eq (a : DIval) : ksqrtI a = DIval.sqrtI a := by
  have e1 : ∀ x : Nat, Nat.shiftLeft x 56 = x <<< dfxS := fun _ => rfl
  simp only [ksqrtI, DIval.sqrtI, DIval.isqrt, posNat_eq, isqrtK_eq, e1, hi2_eq]
  rfl

theorem knorm2_eq (x y : DIval) : knorm2 x y = DIval.norm2 x y := by
  simp only [knorm2, DIval.norm2, ksq_eq, kadd_eq, ksqrtI_eq]

theorem vnormK_eq (a : V2) : vnormK a = V2.norm a := by
  simp only [vnormK, V2.norm, knorm2_eq]

theorem krot_eq (s c : DIval) (v : V2) : krot s c v = V2.rot s c v := by
  simp only [krot, V2.rot, kmul_eq, ksub_eq, kadd_eq]

/-! ## Sine and cosine -/

theorem hornerK_eq (x2 : DIval) : ∀ l : List Int, hornerK x2 l = DIval.hornerAlt x2 l
  | [] => rfl
  | [c] => by simp only [hornerK, DIval.hornerAlt, iadd_eq]
  | c :: c' :: rest => by
    simp only [hornerK, DIval.hornerAlt, hornerK_eq x2 (c' :: rest), ksub_eq, kmul_eq, iadd_eq]

theorem ofInt_one : DIval.ofInt 1 = DIval.pt dfxOne := by
  simp only [DIval.ofInt, Int.one_mul]

theorem sinCoreK_eq (x : DIval) : sinCoreK x = DIval.sinCore x := by
  simp only [sinCoreK, DIval.sinCore, ksq_eq, hornerK_eq, kmul_eq, ksub_eq, isub_eq, iadd_eq, ofInt_one]

theorem cosCoreK_eq (x : DIval) : cosCoreK x = DIval.cosCore x := by
  simp only [cosCoreK, DIval.cosCore, ksq_eq, hornerK_eq, kmul_eq, ksub_eq, isub_eq, iadd_eq, ofInt_one]

theorem pi2I_eq : pi2I = ⟨DIval.pi2Lo, DIval.pi2Lo + 1⟩ := by decide

theorem pi4S_eq : pi4S = DIval.pi4Lo + 64 := by decide

theorem kpi2Residual_eq (t k : Int) : kpi2Residual t k = DIval.kpi2Residual t k := by
  simp only [kpi2Residual, DIval.kpi2Residual, ksub_eq, kmul_eq, imul_eq, DIval.ofInt, pi2I_eq]

theorem adjustKK_eq (t : Int) : ∀ (fuel : Nat) (k : Int), adjustKK t fuel k = DIval.adjustK t fuel k
  | 0, _ => rfl
  | fuel + 1, k => by
    simp only [adjustKK, DIval.adjustK, kpi2Residual_eq, bsel_eq, ilt_eq, ineg_eq, iadd_eq, isub_eq,
      adjustKK_eq t fuel, pi4S_eq, decide_eq_true_eq, gt_iff_lt]

theorem kclamp1_eq (a : DIval) : kclamp1 a = DIval.clamp1 a := by
  simp only [kclamp1, DIval.clamp1, kmax_eq, kmin_eq]

theorem sincosK_eq (t : Int) : sincosK t = DIval.sincos t := by
  simp only [sincosK, DIval.sincos, adjustKK_eq, kpi2Residual_eq, sinCoreK_eq, cosCoreK_eq, kneg_eq, kclamp1_eq,
    iadd_eq]
  rfl

theorem sincosIvK_eq (t : DIval) : sincosIvK t = DIval.sincosIv t := by
  simp only [sincosIvK, DIval.sincosIv, sincosK_eq, kmax_eq, isub_eq, iadd_eq, kclamp1_eq]

/-! ## Per-body data, vertex data -/

theorem angK4_eq (tl th : Int) : angK4 tl th = angK tl th := by
  simp only [angK4, angK, sincosIvK_eq, kmax_eq, isub_eq, iadd_eq]

theorem trK4_eq (xl xh yl yh : Int) : trK4 xl xh yl yh = trK xl xh yl yh := by
  simp only [trK4, trK, knorm2_eq, kmax_eq, isub_eq, iadd_eq]

theorem vdK4_eq (F : Fam) (g b : Nat) (A : Ang) (T : Tr) : vdK4 F g b A T = vdK F g b A T := by
  simp only [vdK4, vdK, krot_eq, kvadd_eq, kmulPt_eq, kadd_eq]

theorem withVD4_eq {β : Type} (E : Env) (g : Nat) (k : VD → β) : withVD4 E g k = withVD E g k := by
  obtain ⟨F, A1, A2, A3, A4, T1, T2, T3, T4⟩ := E
  simp only [withVD4, withVD, natK_eq]
  generalize F.body[g]! = b
  rcases b with _ | _ | _ | _ | b <;> simp only [vdK4_eq]

theorem withVDs4_eq {β : Type} (E : Env) (l : List Nat) (k : List VD → β) : withVDs4 E l k = withVDs E l k := by
  induction l generalizing k with
  | nil => rfl
  | cons g gs ih => simp only [withVDs4, withVDs, withVD4_eq, ih]

theorem withSts4_eq {β : Type} (E : Env) (sts : List (St × Int)) (k : List (List VD) → β) :
    WormK4.withSts E sts k = WormK3.withSts E sts k := by
  induction sts generalizing k with
  | nil => rfl
  | cons p ps ih => simp only [WormK4.withSts, WormK3.withSts, withVDs4_eq, ih]

end WormK4
