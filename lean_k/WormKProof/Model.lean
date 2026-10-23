import WormKProof.Ctx
import WormKProof.Det

/-!
# The quadratic model: edges, `F₀`, `g`, `M`

The cyclic edges of the vertex data are the images of `cycPairs`; the sums over the edge contributions `ecK` give the
entries of `model` (`F₀`, `g_k`, `M_kl`), the zero terms of the dense model being dropped.
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (Ang Tr angK trK)

theorem rotL1_getElem {α : Type} (l : List α) (j : Nat) (hj : j < l.length) :
    (rotL 1 l)[j]'(by simp [rotL]; omega) = l[(j + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  simp only [rotL]
  by_cases h : j + 1 < l.length
  · rw [List.getElem_append_left (by simp; omega)]
    simp [Nat.mod_eq_of_lt h]
  · have hj' : j + 1 = l.length := by omega
    rw [List.getElem_append_right (by simp; omega)]
    have : (j + 1) % l.length = 0 := by rw [hj', Nat.mod_self]
    simp only [List.getElem_take, this]
    congr 1; simp; omega

theorem edgesV_map (l : List Nat) (f : Nat → VD) :
    edgesV (l.map f) = (cycPairs l).map fun p => (f p.1, f p.2) := by
  apply List.ext_getElem
  · simp only [edgesV, cycPairs, rotL, List.length_zip, List.length_map, List.length_append, List.length_drop,
      List.length_take, List.length_range]; omega
  · intro j h1 h2
    simp only [edgesV, List.getElem_zip, List.getElem_map, cycPairs, List.getElem_range, at']
    have hj : j < l.length := by simpa [cycPairs] using h2
    have hn : 0 < l.length := by omega
    rw [rotL1_getElem _ j (by simpa using hj)]
    simp only [List.length_map, List.getElem_map, List.getD_eq_getElem?_getD, Nat.mod_eq_of_lt hj,
      List.getElem?_eq_getElem hj, Option.getD_some,
      List.getElem?_eq_getElem (Nat.mod_lt _ hn)]

theorem mem_cycPairs (l : List Nat) (p : Nat × Nat) (hp : p ∈ cycPairs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  simp only [cycPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hn : 0 < l.length := by omega
  simp only [at', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hn), Option.getD_some]
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

/-- The active variable data of variable `a`. -/
def avOfK (E : Env) (a : Nat) : AV := avK (angOf E (a / 4 + 1)) (trOf E (a / 4 + 1)) a (a / 4 + 1) (a % 4)

section
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int) (l : List Nat) (hl : ∀ g ∈ l, g < F.body.size)

/-- The edge contributions of the structure `l`. -/
def ecsOf : List EC := (edgesV (l.map (vdOf (envOf F lo hi)))).map fun p => ecK p.1 p.2

theorem ecsOf_eq : ecsOf F lo hi l =
    (cycPairs l).map fun p => ecK (vdOf (envOf F lo hi) p.1) (vdOf (envOf F lo hi) p.2) := by
  simp [ecsOf, edgesV_map]

include hF hl in
theorem F0_eq : khalf (ksum ((ecsOf F lo hi l).map (·.f0))) = (model (mkCtx F lo hi) l).1 := by
  rw [ecsOf_eq, List.map_map, ksum_eq, khalf_eq]
  simp only [model]
  congr 1
  apply isum_congr
  intro p hp
  obtain ⟨h1, h2⟩ := mem_cycPairs l p hp
  obtain ⟨-, -, hx1, -⟩ := vdOf_ctx F hF lo hi p.1 (hl _ h1)
  obtain ⟨-, -, hx2, -⟩ := vdOf_ctx F hF lo hi p.2 (hl _ h2)
  simp only [Function.comp, ecK, kdet_eq, hx1, hx2]

theorem cond_kpt0 (c : Bool) (x : DIval) : cond c x kpt0 = if c then x else DIval.pt 0 := by
  cases c <;> rfl

include hF in
theorem gTerm_eq (x y a : Nat) (hx : x < F.body.size) (hy : y < F.body.size) :
    kadd (cond ((vdOf (envOf F lo hi) y).b == a / 4 + 1) (detXL (vdOf (envOf F lo hi) x).x0 (a % 4) (vdOf (envOf F lo hi) y).rq) kpt0)
      (cond ((vdOf (envOf F lo hi) x).b == a / 4 + 1) (detLX (a % 4) (vdOf (envOf F lo hi) x).rq (vdOf (envOf F lo hi) y).x0) kpt0) =
    gTerm (mkCtx F lo hi) x y a := by
  obtain ⟨bx, rqx, x0x, -⟩ := vdOf_ctx F hF lo hi x hx
  obtain ⟨by', rqy, x0y, -⟩ := vdOf_ctx F hF lo hi y hy
  simp only [gTerm, kadd_eq, cond_kpt0, bx, by', rqx, rqy, x0x, x0y, detXL_eq, detLX_eq, lcol_eq]
  have e1 : ((F.body[y]! == a / 4 + 1) = true) ↔ ((mkCtx F lo hi).F.body[y]! ≠ 0 ∧ a / 4 = (mkCtx F lo hi).F.body[y]! - 1) := by
    show _ ↔ (F.body[y]! ≠ 0 ∧ a / 4 = F.body[y]! - 1)
    simp only [beq_iff_eq]; omega
  have e2 : ((F.body[x]! == a / 4 + 1) = true) ↔ ((mkCtx F lo hi).F.body[x]! ≠ 0 ∧ a / 4 = (mkCtx F lo hi).F.body[x]! - 1) := by
    show _ ↔ (F.body[x]! ≠ 0 ∧ a / 4 = F.body[x]! - 1)
    simp only [beq_iff_eq]; omega
  simp only [e1, e2]

include hF hl in
theorem g_eq (a : Nat) (ha : a < 16) :
    gOf (ecsOf F lo hi l) (avOfK (envOf F lo hi) a) = (model (mkCtx F lo hi) l).2.1[a]! := by
  have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
  simp only [model, hk]
  rw [range_map_get _ _ _ ha, gOf, ecsOf_eq, List.map_map, ksum_eq, khalf_eq]
  congr 1
  apply isum_congr
  intro p hp
  obtain ⟨h1, h2⟩ := mem_cycPairs l p hp
  simp only [Function.comp, ecK, avOfK, avK]
  exact gTerm_eq F hF lo hi p.1 p.2 a (hl _ h1) (hl _ h2)

include hF in
theorem MTerm_eq (x y a b : Nat) (hx : x < F.body.size) (hy : y < F.body.size) :
    MTerm (mkCtx F lo hi) x y a b =
      if ((vdOf (envOf F lo hi) x).b == a / 4 + 1 && (vdOf (envOf F lo hi) y).b == b / 4 + 1) = true then
        detLL (a % 4) (vdOf (envOf F lo hi) x).rq (b % 4) (vdOf (envOf F lo hi) y).rq
      else DIval.pt 0 := by
  obtain ⟨bx, rqx, -, -⟩ := vdOf_ctx F hF lo hi x hx
  obtain ⟨by', rqy, -, -⟩ := vdOf_ctx F hF lo hi y hy
  simp only [MTerm, bx, by', rqx, rqy, detLL_eq, lcol_eq]
  have e : ((F.body[x]! == a / 4 + 1 && F.body[y]! == b / 4 + 1) = true) ↔
      ((mkCtx F lo hi).F.body[x]! ≠ 0 ∧ (mkCtx F lo hi).F.body[y]! ≠ 0 ∧ a / 4 = (mkCtx F lo hi).F.body[x]! - 1 ∧
        b / 4 = (mkCtx F lo hi).F.body[y]! - 1) := by
    show _ ↔ (F.body[x]! ≠ 0 ∧ F.body[y]! ≠ 0 ∧ a / 4 = F.body[x]! - 1 ∧ b / 4 = F.body[y]! - 1)
    simp only [Bool.and_eq_true, beq_iff_eq]; omega
  simp only [e]

include hF hl in
theorem M_eq (a b : Nat) (ha : a < 16) (hb : b < 16) :
    mOf (ecsOf F lo hi l) (avOfK (envOf F lo hi) a) (avOfK (envOf F lo hi) b) =
      (model (mkCtx F lo hi) l).2.2[a * 16 + b]! := by
  have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
  have hi' : a * 16 + b < 16 * 16 := by omega
  have hd : (a * 16 + b) / 16 = a := by omega
  have hm : (a * 16 + b) % 16 = b := by omega
  simp only [model, hk]
  rw [range_map_get _ _ _ hi', hd, hm, mOf, ecsOf_eq, List.filter_map, List.map_map, ksum_eq, khalf_eq]
  congr 1
  rw [← isum_filter (cycPairs l)
    (fun p => (fun e : EC => e.b1 == (avOfK (envOf F lo hi) a).b && e.b2 == (avOfK (envOf F lo hi) b).b)
      (ecK (vdOf (envOf F lo hi) p.1) (vdOf (envOf F lo hi) p.2)))
    (fun p => MTerm (mkCtx F lo hi) p.1 p.2 a b)]
  · apply isum_congr
    intro p hp
    have hp' := (List.mem_filter.mp hp)
    obtain ⟨h1, h2⟩ := mem_cycPairs l p hp'.1
    rw [MTerm_eq F hF lo hi p.1 p.2 a b (hl _ h1) (hl _ h2)]
    simp only [Function.comp, ecK, avOfK, avK] at hp' ⊢
    simp only [hp'.2, ite_true]
  · intro p hp hq
    obtain ⟨h1, h2⟩ := mem_cycPairs l p hp
    rw [MTerm_eq F hF lo hi p.1 p.2 a b (hl _ h1) (hl _ h2)]
    simp only [ecK, avOfK, avK] at hq ⊢
    simp only [hq, Bool.false_eq_true, ite_false]

end

end WormK3
