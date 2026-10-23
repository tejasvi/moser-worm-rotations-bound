import WormKProof.Isum

/-!
# Determinants with the unit columns

`detXL x j r = det(x, lc j r)`, `detLX j r x = det(lc j r, x)`, `detLL j r₁ l r₂ = det(lc j r₁, lc l r₂)` where
`lc 0 = (1, 0)`, `lc 1 = (0, 1)`, `lc 2 = r`, `lc j = J r` (`j ≥ 3`), as for `lcol`.
-/

namespace WormK3

open MoserWorm WormCore

/-- The columns of `lcol`, from the rotated body point. -/
def lc (j : Nat) (r : V2) : V2 :=
  match j with
  | 0 => (DIval.ofInt 1, DIval.pt 0)
  | 1 => (DIval.pt 0, DIval.ofInt 1)
  | 2 => r
  | _ => V2.J r

theorem lcol_eq (C : Ctx) (g j : Nat) : lcol C g j = lc j C.RQ[g]! := by
  rcases j with _ | _ | _ | j <;> rfl

theorem mul_comm' (a b : DIval) : a.mul b = b.mul a := by
  simp only [DIval.mul]
  have h1 : a.lo * b.lo = b.lo * a.lo := Int.mul_comm _ _
  have h2 : a.lo * b.hi = b.hi * a.lo := Int.mul_comm _ _
  have h3 : a.hi * b.lo = b.lo * a.hi := Int.mul_comm _ _
  have h4 : a.hi * b.hi = b.hi * a.hi := Int.mul_comm _ _
  rw [h1, h2, h3, h4]
  generalize b.lo * a.lo = p1
  generalize b.hi * a.lo = p2
  generalize b.lo * a.hi = p3
  generalize b.hi * a.hi = p4
  congr 1
  · congr 1; simp only [Int.min_def]; (repeat' split) <;> omega
  · congr 2; simp only [Int.max_def]; (repeat' split) <;> omega

theorem ofInt1 : DIval.ofInt 1 = DIval.pt dfxOne := rfl

theorem mulD (a : DIval) : a.mul (DIval.ofInt 1) = sortI a := (sortI_eq a).symm
theorem Dmul (a : DIval) : (DIval.ofInt 1).mul a = sortI a := by rw [mul_comm', mulD]

theorem kdet_eq (u v : V2) : kdet u v = V2.det u v := by
  simp only [kdet, V2.det, ksub_eq, kmul_eq]

theorem pt0_sub (a : DIval) : (DIval.pt 0).sub a = kneg a := by
  simp only [DIval.sub, DIval.pt, kneg, ineg_eq]; congr 1 <;> omega

theorem kneg_sortI_neg (r : DIval) : kneg (sortI r.neg) = sortI r := by
  simp only [kneg, sortI, DIval.neg, bsel_eq, ile_eq, ineg_eq]
  by_cases h : r.lo ≤ r.hi
  · have h' : -r.hi ≤ -r.lo := by omega
    simp [h, h']
  · have h' : ¬ -r.hi ≤ -r.lo := by omega
    simp [h, h']

theorem detXL_eq (x : V2) (j : Nat) (r : V2) : detXL x j r = V2.det x (lc j r) := by
  rcases j with _ | _ | _ | j
  · simp only [detXL, lc, V2.det, mul_pt0, mulD, pt0_sub]
  · simp only [detXL, lc, V2.det, mul_pt0, mulD, sub_pt0]
  · simp only [detXL, lc, kdet_eq]
  · simp only [detXL, lc, kdet_eq]

theorem detLX_eq (j : Nat) (r : V2) (x : V2) : detLX j r x = V2.det (lc j r) x := by
  rcases j with _ | _ | _ | j
  · simp only [detLX, lc, V2.det, pt0_mul, Dmul, sub_pt0]
  · simp only [detLX, lc, V2.det, pt0_mul, Dmul, pt0_sub]
  · simp only [detLX, lc, kdet_eq]
  · simp only [detLX, lc, kdet_eq]

theorem detLL_eq (j : Nat) (r1 : V2) (l : Nat) (r2 : V2) : detLL j r1 l r2 = V2.det (lc j r1) (lc l r2) := by
  rcases j with _ | _ | _ | j
  · rcases l with _ | _ | _ | l
    · simp only [detLL, lc]; decide
    · simp only [detLL, lc]; decide
    · simp only [detLL, lc, V2.det, pt0_mul, Dmul, sub_pt0]
    · simp only [detLL, lc, V2.det, V2.J, pt0_mul, Dmul, sub_pt0]
  · rcases l with _ | _ | _ | l
    · simp only [detLL, lc]; decide
    · simp only [detLL, lc]; decide
    · simp only [detLL, lc, V2.det, pt0_mul, Dmul, pt0_sub]
    · simp only [detLL, lc, V2.det, V2.J, pt0_mul, Dmul, pt0_sub, kneg_sortI_neg]
  · simp only [detLL, lc, detXL_eq]
  · simp only [detLL, lc, detXL_eq]

end WormK3
