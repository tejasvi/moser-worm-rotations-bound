import WormK.Fast3

/-!
# The kernel-form primitives compute the core operations

`iadd = (· + ·)`, `ineg = (- ·)`, `imul = (· * ·)`, `ile a b = decide (a ≤ b)`, `shr x = x.fdiv 2⁵⁶`, and the interval
operations `kadd`, `ksub`, `kmul`, `kmulPt`, `sortI`, `kmulW`, `khalf`, `kabs`, `kposI`, `ksum` agree with
`DIval.add`, `DIval.sub`, `DIval.mul`, `DIval.mul · (pt c)`, `DIval.half`, `DIval.abs`, `DIval.pos`, `isum`.
-/

namespace WormK3

open MoserWorm WormCore

theorem isnn_eq (m n : Nat) : isnn m n = Int.subNatNat m n := by
  show Nat.rec (motive := fun _ => Int) (Int.ofNat (m - n)) (fun k _ => Int.negSucc k) (n - m) = Int.subNatNat m n
  unfold Int.subNatNat
  cases h : n - m with
  | zero => rfl
  | succ k => rfl

theorem iadd_eq (a b : Int) : iadd a b = a + b := by
  cases a <;> cases b <;> simp only [iadd, isnn_eq] <;> rfl

theorem nneg_eq (n : Nat) : nneg n = -(n : Int) := by
  cases n <;> rfl

theorem ineg_eq (a : Int) : ineg a = -a := by
  cases a with
  | ofNat n => simp only [ineg, nneg_eq]; rfl
  | negSucc n => rfl

theorem isub_eq (a b : Int) : isub a b = a - b := by
  simp only [isub, iadd_eq, ineg_eq, Int.sub_eq_add_neg]

theorem imul_eq (a b : Int) : imul a b = a * b := by
  cases a <;> cases b <;> simp only [imul, nneg_eq] <;> rfl

theorem ile_eq (a b : Int) : ile a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> simp only [ile, Nat.ble_eq, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast,
    Bool.false_eq_true, false_iff, true_iff] <;> omega

theorem nonneg_eq (a : Int) : nonneg a = decide (0 ≤ a) := by
  cases a <;> simp [nonneg, Int.negSucc_eq] <;> omega

theorem isD_eq (w : Int) : isD w = decide (w = dfxOne) := by
  apply Bool.eq_iff_iff.mpr
  cases w <;> simp only [isD, Nat.beq_eq, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast, dfxOne,
    Bool.false_eq_true, false_iff] <;> omega

theorem bsel_eq {α : Type} (c : Bool) (t e : α) : bsel c t e = if c then t else e := by
  cases c <;> rfl

theorem shr_eq (x : Int) : shr x = x.fdiv dfxOne := by
  have h1 : shr x = x >>> 56 := by cases x <;> rfl
  rw [h1, Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  rfl

theorem shr1_eq (x : Int) : shr1 x = x.fdiv 2 := by
  have h1 : shr1 x = x >>> 1 := by cases x <;> rfl
  rw [h1, Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  rfl

theorem cshr_eq (x : Int) : cshr x = -((-x).fdiv dfxOne) := by
  simp only [cshr, ineg_eq, shr_eq]

theorem kmin_eq (a b : Int) : kmin a b = min a b := by
  simp only [kmin, bsel_eq, ile_eq, Int.min_def]; split <;> simp_all <;> omega

theorem kmax_eq (a b : Int) : kmax a b = max a b := by
  simp only [kmax, bsel_eq, ile_eq, Int.max_def]; split <;> simp_all <;> omega

theorem kadd_eq (a b : DIval) : kadd a b = a.add b := by
  simp only [kadd, DIval.add, iadd_eq]

theorem ksub_eq (a b : DIval) : ksub a b = a.sub b := by
  simp only [ksub, DIval.sub, isub_eq]

theorem kneg_eq (a : DIval) : kneg a = a.neg := by
  simp only [kneg, DIval.neg, ineg_eq]

theorem kpt0_eq : kpt0 = DIval.pt 0 := rfl

theorem kmul_eq (a b : DIval) : kmul a b = a.mul b := by
  simp only [kmul, DIval.mul, imul_eq, kmin_eq, kmax_eq, shr_eq, cshr_eq]

theorem kmulPt_eq (a : DIval) (c : Int) : kmulPt a c = a.mul (DIval.pt c) := by
  simp only [kmulPt, DIval.mul, DIval.pt, imul_eq, bsel_eq, ile_eq, shr_eq, cshr_eq]
  by_cases h : a.lo * c ≤ a.hi * c
  · simp [h, Int.min_def, Int.max_def]
  · simp [h, Int.min_def, Int.max_def]

theorem sortI_eq (a : DIval) : sortI a = a.mul (DIval.pt dfxOne) := by
  simp only [sortI, DIval.mul, DIval.pt, bsel_eq, ile_eq]
  have hD : (0 : Int) < dfxOne := by decide
  have e1 : (a.lo * dfxOne).fdiv dfxOne = a.lo := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]; exact Int.mul_ediv_cancel _ (by decide)
  have e2 : (a.hi * dfxOne).fdiv dfxOne = a.hi := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]; exact Int.mul_ediv_cancel _ (by decide)
  have e3 : -((-(a.lo * dfxOne)).fdiv dfxOne) = a.lo := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), ← Int.neg_mul, Int.mul_ediv_cancel _ (by decide), Int.neg_neg]
  have e4 : -((-(a.hi * dfxOne)).fdiv dfxOne) = a.hi := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), ← Int.neg_mul, Int.mul_ediv_cancel _ (by decide), Int.neg_neg]
  by_cases h : a.lo ≤ a.hi
  · have hm : a.lo * dfxOne ≤ a.hi * dfxOne := Int.mul_le_mul_of_nonneg_right h (by decide)
    simp [h, Int.min_def, Int.max_def, hm, e1, e2, e3, e4]
  · have hm : ¬ a.lo * dfxOne ≤ a.hi * dfxOne := fun h' => h (Int.le_of_mul_le_mul_right h' hD)
    simp [h, Int.min_def, Int.max_def, hm, e1, e2, e3, e4]

theorem kmulW_eq (a : DIval) (w : Int) : kmulW a w = a.mul (DIval.pt w) := by
  simp only [kmulW, bsel_eq, isD_eq]
  split
  · next h => simp only [decide_eq_true_eq] at h; subst h; exact sortI_eq a
  · exact kmulPt_eq a w

theorem khalf_eq (a : DIval) : khalf a = a.half := by
  simp only [khalf, DIval.half, DIval.fshr, DIval.cshr, shr1_eq, ineg_eq]
  rfl

theorem kabs_eq (a : DIval) : kabs a = a.abs := by
  simp only [kabs, DIval.abs, bsel_eq, nonneg_eq, ile_eq, kneg_eq, kmax_eq, ineg_eq]
  by_cases h1 : 0 ≤ a.lo
  · simp [h1]
  · by_cases h2 : a.hi ≤ 0 <;> simp [h1, h2]

theorem kposI_eq (a : DIval) : kposI a = a.pos := by
  simp only [kposI, DIval.pos, kmax_eq]; rfl

theorem ksum_eq (l : List DIval) : ksum l = isum l := by
  unfold ksum isum
  suffices H : ∀ acc, List.rec (motive := fun _ => DIval → DIval) (fun acc => acc)
      (fun h _ ih acc => ih (kadd acc h)) l acc = l.foldl DIval.add acc from H _
  induction l with
  | nil => intro acc; rfl
  | cons h t ih => intro acc; simp only [List.foldl_cons, ← kadd_eq]; exact ih _

end WormK3
