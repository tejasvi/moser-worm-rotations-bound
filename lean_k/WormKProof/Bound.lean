import WormKProof.Model

/-!
# The bound: `leafBoundV = leafBound`
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (Ang Tr angK trK)

section
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int)

include hF in
theorem y0_eq (a : Nat) (ha : a < 16) :
    ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (y0At (mkCtx F lo hi)))[a]! = (avOfK (envOf F lo hi) a).y0 := by
  have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
  rw [hk, range_map_get _ _ _ ha]
  have hb0 : a / 4 + 1 ≠ 0 := by omega
  have hb4 : a / 4 + 1 ≤ 4 := by omega
  obtain ⟨-, -, hh⟩ := angOf_bd F hF lo hi _ hb0 hb4
  simp only [y0At, avOfK, avK, hh]
  by_cases h2 : a % 4 = 2 <;> simp [h2]

include hF in
theorem w_eq (a : Nat) (ha : a < 16) :
    ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (wAt (mkCtx F lo hi)))[a]! = (avOfK (envOf F lo hi) a).w := by
  have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
  rw [hk, range_map_get _ _ _ ha]
  have hb0 : a / 4 + 1 ≠ 0 := by omega
  have hb4 : a / 4 + 1 ≤ 4 := by omega
  obtain ⟨-, -, hh⟩ := angOf_bd F hF lo hi _ hb0 hb4
  obtain ⟨-, -, hx, hy⟩ := trOf_bd F hF lo hi _ hb0 hb4
  simp only [wAt, avOfK, avK, hh, hx, hy]
  have : a % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases h : a % 4 with _ | _ | _ | _ | j <;> simp_all <;> omega

theorem adOf_eq (sts : List (St × Int)) :
    adOf (envOf F lo hi) sts =
      ((List.range (4 * (mkCtx F lo hi).F.k)).filter fun a => bodyUsed (mkCtx F lo hi) sts (a / 4 + 1)).map
        (avOfK (envOf F lo hi)) := by
  simp only [adOf, withAT_eq, bodyUsed]
  rfl

end

/-! ## `partsK` against `boundParts`, with function arguments -/

/-- `boundParts` with the arrays replaced by functions. -/
def bpF (act : List Nat) (F0 : DIval) (gf : Nat → DIval) (Hb : Nat → Nat → DIval) (y0f wf : Nat → Int) (β : Int) :
    DIval × (Nat → DIval) :=
  let H := fun a b => if a = b ∧ a % 4 ≥ 2 then (Hb a b).add (DIval.pt (2 * β)) else Hb a b
  let g2 := fun a => if a % 4 = 2 then (gf a).add (DIval.pt (2 * β)) else gf a
  let Fy0 := (F0.add (isum (act.map fun a => (g2 a).mul (DIval.pt (y0f a))))).add
    (isum (act.flatMap fun a => act.map fun b => (((H a b).mul (DIval.pt (y0f a))).mul (DIval.pt (y0f b))).half))
  let grad := fun a => (g2 a).add (isum (act.map fun b => (H a b).mul (DIval.pt (y0f b))))
  let pen := isum (act.map fun a =>
    ((isum ((act.filter (· ≠ a)).map fun b => (((H a b).mul (DIval.pt (wf a))).mul (DIval.pt (wf b))).abs)).sub
      (((H a a).mul (DIval.pt (wf a))).mul (DIval.pt (wf a)))).pos)
  (Fy0.sub pen.half, grad)

theorem boundParts_eq (act : List Nat) (F0 : DIval) (g M : Array DIval) (y0 w : Array Int) (β : Int) :
    boundParts 16 act F0 g M y0 w β =
      bpF act F0 (fun a => g[a]!) (fun a b => M[a * 16 + b]!.add M[b * 16 + a]!) (fun a => y0[a]!) (fun a => w[a]!) β :=
  rfl

/-- The abstract active-variable record. -/
def avA (y0f wf : Nat → Int) (a : Nat) : AV := ⟨a, a / 4 + 1, a % 4, y0f a, wf a⟩

/-- The abstract rows. -/
def rowA (act : List Nat) (gf : Nat → DIval) (Hb : Nat → Nat → DIval) (pr : Nat → Nat → Bool) (y0f wf : Nat → Int)
    (a : Nat) : Row :=
  let ents := (act.filter fun b => b == a || pr a b).map fun b => (avA y0f wf b, Hb a b)
  ⟨avA y0f wf a, gf a, ents,
    ksum ((ents.filter fun p => !(p.1.a == a)).map fun p => kabs (kmulPt (kmulPt p.2 (wf a)) p.1.w))⟩

theorem cond_eq_ite {α : Type} (c : Bool) (x y : α) : cond c x y = if c = true then x else y := by
  cases c <;> rfl

theorem find_diag (y0f wf : Nat → Int) (Hb : Nat → Nat → DIval) (a : Nat) (L : List Nat) (ha : a ∈ L) :
    (L.map fun b => (avA y0f wf b, Hb a b)).find? (fun p => p.1.a == a) = some (avA y0f wf a, Hb a a) := by
  induction L with
  | nil => simp at ha
  | cons b bs ih =>
    by_cases hb : b = a
    · subst hb; simp [avA]
    · have ha' : a ∈ bs := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hb
        · exact h
      simp only [List.map_cons, List.find?_cons]
      have : ((avA y0f wf b).a == a) = false := by simp [avA, hb]
      simp only [this, ih ha']

section abs
variable (act : List Nat) (gf : Nat → DIval) (Hb : Nat → Nat → DIval) (pr : Nat → Nat → Bool) (y0f wf : Nat → Int)
  (β : Int)

theorem rowA_u (a : Nat) : (rowA act gf Hb pr y0f wf a).u = avA y0f wf a := rfl
theorem rowA_g (a : Nat) : (rowA act gf Hb pr y0f wf a).g = gf a := rfl
theorem rowA_ents (a : Nat) : (rowA act gf Hb pr y0f wf a).ents =
    (act.filter fun b => b == a || pr a b).map fun b => (avA y0f wf b, Hb a b) := rfl

theorem g2K_eq (a : Nat) :
    (bif (rowA act gf Hb pr y0f wf a).u.j == 2 then kadd (rowA act gf Hb pr y0f wf a).g (DIval.pt (2 * β))
      else (rowA act gf Hb pr y0f wf a).g) = (if a % 4 = 2 then (gf a).add (DIval.pt (2 * β)) else gf a) := by
  simp only [rowA_u, rowA_g, avA, cond_eq_ite, kadd_eq, beq_iff_eq]

theorem hbK_eq (a b : Nat) :
    (bif (avA y0f wf a).a == (avA y0f wf b).a && decide (2 ≤ (avA y0f wf a).j) then kadd (Hb a b) (DIval.pt (2 * β))
      else Hb a b) = (if a = b ∧ a % 4 ≥ 2 then (Hb a b).add (DIval.pt (2 * β)) else Hb a b) := by
  simp only [avA, cond_eq_ite, kadd_eq, Bool.and_eq_true, beq_iff_eq]
  congr 1; simp only [eq_iff_iff, and_congr_right_iff]; intro _; exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

theorem lin_eq (hy : ∀ a, a % 4 ≠ 2 → y0f a = 0) :
    ksum (List.map (fun r => kmulPt (bif r.u.j == 2 then kadd r.g (DIval.pt (2 * β)) else r.g) r.u.y0)
      (List.filter (fun r => r.u.j == 2) (act.map (rowA act gf Hb pr y0f wf)))) =
    isum (act.map fun a => (if a % 4 = 2 then (gf a).add (DIval.pt (2 * β)) else gf a).mul (DIval.pt (y0f a))) := by
  rw [List.filter_map, List.map_map, ksum_eq,
    ← isum_filter act (fun a => a % 4 == 2) _ (fun a _ h => by
      simp only [beq_eq_false_iff_ne, ne_eq] at h; rw [hy a h, mul_pt0])]
  have hf : ((fun r : Row => r.u.j == 2) ∘ rowA act gf Hb pr y0f wf) = fun a => a % 4 == 2 := by
    funext a; simp [rowA_u, avA]
  rw [hf]
  apply isum_congr
  intro a _
  simp only [Function.comp, kmulPt_eq, rowA_u, rowA_g, avA, cond_eq_ite, kadd_eq, beq_iff_eq]

theorem hbK_eq' (a b : Nat) (h : DIval) :
    (bif (avA y0f wf a).a == (avA y0f wf b).a && decide (2 ≤ (avA y0f wf a).j) then kadd h (DIval.pt (2 * β))
      else h) = (if a = b ∧ a % 4 ≥ 2 then h.add (DIval.pt (2 * β)) else h) := by
  simp only [avA, cond_eq_ite, kadd_eq, Bool.and_eq_true, beq_iff_eq]
  congr 1; simp only [eq_iff_iff, and_congr_right_iff]; intro _; exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

theorem hb_red (a b : Nat) (h : DIval) :
    (bif a == b && decide (2 ≤ a % 4) then kadd h (DIval.pt (2 * β)) else h) =
      (if a = b ∧ a % 4 ≥ 2 then h.add (DIval.pt (2 * β)) else h) := by
  simp only [cond_eq_ite, kadd_eq, Bool.and_eq_true, beq_iff_eq]
  congr 1; simp only [eq_iff_iff, and_congr_right_iff]; intro _; exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

theorem isum_flatMap' {α : Type} (l : List α) (m : α → List DIval) :
    isum (l.flatMap m) = isum (l.map fun a => isum (m a)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, isum_append, ih, List.map_cons, isum_cons]

/-- Dropping the absent and the non-`C` columns of a row. -/
theorem filter_ents (a : Nat) (f : Nat → DIval)
    (hf0 : ∀ b ∈ act, b ≠ a → pr a b = false → f b = DIval.pt 0) (hf2 : ∀ b ∈ act, b % 4 ≠ 2 → f b = DIval.pt 0) :
    isum (((act.filter fun b => b == a || pr a b).filter fun b => b % 4 == 2).map f) = isum (act.map f) := by
  rw [List.filter_filter]
  apply isum_filter
  intro b hb h
  simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact hf2 b hb h
  · exact hf0 b hb h1 h2

theorem ents_j (a : Nat) :
    ((act.filter fun b => b == a || pr a b).map fun b => (avA y0f wf b, Hb a b)).filter (fun p => p.1.j == 2) =
      (((act.filter fun b => b == a || pr a b).filter fun b => b % 4 == 2).map fun b => (avA y0f wf b, Hb a b)) := by
  rw [List.filter_map]; rfl

theorem quad_eq (hz : ∀ a ∈ act, ∀ b ∈ act, a ≠ b → pr a b = false → Hb a b = DIval.pt 0)
    (hy : ∀ a, a % 4 ≠ 2 → y0f a = 0) :
    ksum (List.flatMap (fun r => List.map (fun p => khalf (kmulPt (kmulPt
        (bif r.u.a == p.fst.a && decide (2 ≤ r.u.j) then kadd p.snd (DIval.pt (2 * β)) else p.snd) r.u.y0) p.fst.y0))
        (List.filter (fun p => p.fst.j == 2) r.ents))
      (List.filter (fun r => r.u.j == 2) (act.map (rowA act gf Hb pr y0f wf)))) =
    isum (act.flatMap fun a => act.map fun b =>
      (((if a = b ∧ a % 4 ≥ 2 then (Hb a b).add (DIval.pt (2 * β)) else Hb a b).mul (DIval.pt (y0f a))).mul
        (DIval.pt (y0f b))).half) := by
  rw [ksum_eq, isum_flatMap', isum_flatMap', List.filter_map, List.map_map]
  have hf : ((fun r : Row => r.u.j == 2) ∘ rowA act gf Hb pr y0f wf) = fun a => a % 4 == 2 := by
    funext a; simp [rowA_u, avA]
  rw [hf, ← isum_filter act (fun a => a % 4 == 2) _ (fun a _ h => by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      apply isum_zero; intro b _; rw [hy a h, mul_pt0, pt0_mul, half_pt0])]
  apply isum_congr
  intro a ha
  have ha' := (List.mem_filter.mp ha).1
  simp only [Function.comp, rowA_ents, rowA_u, ents_j, List.map_map]
  rw [← filter_ents act pr a _ (fun b _ hba hpr => by
      rw [hz a ha' b ‹_› (Ne.symm hba) hpr]
      have : ¬ (a = b ∧ a % 4 ≥ 2) := fun h => hba h.1.symm
      simp only [this, ite_false, pt0_mul, half_pt0])
    (fun b _ hb2 => by rw [hy b hb2, mul_pt0, half_pt0])]
  apply isum_congr
  intro b _
  simp only [Function.comp, khalf_eq, kmulPt_eq, avA]
  congr 3
  by_cases h1 : a = b <;> by_cases h2 : 2 ≤ a % 4 <;> simp [h1, h2, cond_eq_ite, kadd_eq]

theorem grad_eq (hz : ∀ a ∈ act, ∀ b ∈ act, a ≠ b → pr a b = false → Hb a b = DIval.pt 0)
    (hy : ∀ a, a % 4 ≠ 2 → y0f a = 0) :
    List.map (fun r => kadd (bif r.u.j == 2 then kadd r.g (DIval.pt (2 * β)) else r.g)
        (ksum (List.map (fun p => kmulPt (bif r.u.a == p.fst.a && decide (2 ≤ r.u.j) then kadd p.snd
          (DIval.pt (2 * β)) else p.snd) p.fst.y0) (List.filter (fun p => p.fst.j == 2) r.ents))))
      (act.map (rowA act gf Hb pr y0f wf)) =
    act.map fun a => (if a % 4 = 2 then (gf a).add (DIval.pt (2 * β)) else gf a).add
      (isum (act.map fun b => (if a = b ∧ a % 4 ≥ 2 then (Hb a b).add (DIval.pt (2 * β)) else Hb a b).mul
        (DIval.pt (y0f b)))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp, kadd_eq, rowA_ents, rowA_u, ents_j, List.map_map, ksum_eq]
  congr 1
  · simp only [avA, rowA_g, cond_eq_ite, beq_iff_eq]
  rw [← filter_ents act pr a _ (fun b _ hba hpr => by
      rw [hz a ha b ‹_› (Ne.symm hba) hpr]
      have : ¬ (a = b ∧ a % 4 ≥ 2) := fun h => hba h.1.symm
      simp only [this, ite_false, pt0_mul])
    (fun b _ hb2 => by rw [hy b hb2, mul_pt0])]
  apply isum_congr
  intro b _
  simp only [Function.comp, kmulPt_eq, avA]
  congr 1
  by_cases h1 : a = b <;> by_cases h2 : 2 ≤ a % 4 <;> simp [h1, h2, cond_eq_ite, kadd_eq]

theorem isum_filter_ite {α : Type} (l : List α) (p : α → Bool) (f : α → DIval) :
    isum ((l.filter p).map f) = isum (l.map fun x => if p x = true then f x else DIval.pt 0) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hp : p x = true
    · simp only [List.filter_cons_of_pos hp, List.map_cons, isum_cons, ih, hp, ite_true]
    · rw [List.filter_cons_of_neg hp, ih, List.map_cons, isum_cons]
      simp only [hp, Bool.false_eq_true, ite_false, pt0_add]

theorem pen_eq (hz : ∀ a ∈ act, ∀ b ∈ act, a ≠ b → pr a b = false → Hb a b = DIval.pt 0) :
    ksum (List.map (fun r => kposI (ksub r.off (kmulPt (kmulPt
        (bif r.u.a == r.u.a && decide (2 ≤ r.u.j) then
          kadd ((Option.map (fun x => x.snd) (List.find? (fun p => p.fst.a == r.u.a) r.ents)).getD kpt0) (DIval.pt (2 * β))
        else (Option.map (fun x => x.snd) (List.find? (fun p => p.fst.a == r.u.a) r.ents)).getD kpt0)
        r.u.w) r.u.w))) (act.map (rowA act gf Hb pr y0f wf))) =
    isum (act.map fun a =>
      ((isum ((act.filter (· ≠ a)).map fun b =>
          (((if a = b ∧ a % 4 ≥ 2 then (Hb a b).add (DIval.pt (2 * β)) else Hb a b).mul (DIval.pt (wf a))).mul
            (DIval.pt (wf b))).abs)).sub
        (((if a = a ∧ a % 4 ≥ 2 then (Hb a a).add (DIval.pt (2 * β)) else Hb a a).mul (DIval.pt (wf a))).mul
          (DIval.pt (wf a)))).pos) := by
  rw [List.map_map, ksum_eq]
  apply isum_congr
  intro a ha
  have hmem : a ∈ act.filter fun b => b == a || pr a b := List.mem_filter.mpr ⟨ha, by simp⟩
  have hfd : (((act.filter fun b => b == a || pr a b).map fun b => (avA y0f wf b, Hb a b)).find?
      (fun p => p.1.a == (avA y0f wf a).a)) = some (avA y0f wf a, Hb a a) := find_diag y0f wf Hb a _ hmem
  simp only [Function.comp, rowA_u, rowA_ents]
  rw [hfd]
  simp only [Option.map_some, Option.getD_some, kposI_eq, ksub_eq, kmulPt_eq]
  congr 2
  · -- the off-diagonal Gershgorin sum
    show ksum _ = _
    rw [ksum_eq, List.filter_map, List.map_map, isum_filter_ite, isum_filter_ite]
    conv => rhs; rw [isum_filter_ite]
    apply isum_congr
    intro b hb
    simp only [Function.comp, avA]
    by_cases hba : b = a
    · subst hba; simp
    · have hab : a ≠ b := fun h => hba h.symm
      have hn : ¬ (a = b ∧ a % 4 ≥ 2) := fun h => hab h.1
      by_cases hp : pr a b = true
      · simp [hba, hp, hn, kabs_eq, kmulPt_eq]
      · have hz' := hz a ha b hb hab (by simpa using hp)
        simp [hba, hp, hn, hz', pt0_mul, abs_pt0]
  · congr 2
    simp only [avA]
    by_cases h2 : 2 ≤ a % 4 <;> simp [h2, cond_eq_ite, kadd_eq]

end abs

theorem partsK_abs (act : List Nat) (F0 : DIval) (gf : Nat → DIval) (Hb : Nat → Nat → DIval) (pr : Nat → Nat → Bool)
    (y0f wf : Nat → Int) (β : Int)
    (hz : ∀ a ∈ act, ∀ b ∈ act, a ≠ b → pr a b = false → Hb a b = DIval.pt 0)
    (hy : ∀ a, a % 4 ≠ 2 → y0f a = 0) :
    partsK ⟨F0, act.map (rowA act gf Hb pr y0f wf)⟩ β =
      ((bpF act F0 gf Hb y0f wf β).1, act.map (bpF act F0 gf Hb y0f wf β).2) := by
  simp only [partsK, bpF]
  rw [lin_eq (hy := hy), quad_eq (hz := hz) (hy := hy), pen_eq (hz := hz), grad_eq (hz := hz) (hy := hy)]
  simp only [ksub_eq, kadd_eq, khalf_eq]

/-! ## `sdOf` is the abstract row structure -/

section conc
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int) (l : List Nat) (hl : ∀ g ∈ l, g < F.body.size)

/-- Presence of an edge between bodies `p` and `q` (either orientation). -/
def presOf (p q : Nat) : Bool :=
  (ecsOf F lo hi l).any fun e => (e.b1 == p && e.b2 == q) || (e.b1 == q && e.b2 == p)

theorem mOf_absent (u v : AV) (h : presOf F lo hi l u.b v.b = false) :
    mOf (ecsOf F lo hi l) u v = DIval.pt 0 ∧ mOf (ecsOf F lo hi l) v u = DIval.pt 0 := by
  simp only [presOf, List.any_eq_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and] at h
  have e1 : (ecsOf F lo hi l).filter (fun e => e.b1 == u.b && e.b2 == v.b) = [] := by
    rw [List.filter_eq_nil_iff]; intro e he; simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    exact (h e he).1
  have e2 : (ecsOf F lo hi l).filter (fun e => e.b1 == v.b && e.b2 == u.b) = [] := by
    rw [List.filter_eq_nil_iff]; intro e he; simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    exact (h e he).2
  simp only [mOf, e1, e2, List.map_nil]
  exact ⟨by decide, by decide⟩

def y0fOf (a : Nat) : Int := ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (y0At (mkCtx F lo hi)))[a]!
def wfOf (a : Nat) : Int := ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (wAt (mkCtx F lo hi)))[a]!

include hF in
theorem avOfK_eq (a : Nat) (ha : a < 16) : avOfK (envOf F lo hi) a = avA (y0fOf F lo hi) (wfOf F lo hi) a := by
  simp only [avA, y0fOf, wfOf, y0_eq F hF lo hi a ha, w_eq F hF lo hi a ha]
  rfl

/-- The row data of the structure `l`. -/
def gfOf (a : Nat) : DIval := (model (mkCtx F lo hi) l).2.1[a]!
def HbOf (a b : Nat) : DIval := (model (mkCtx F lo hi) l).2.2[a * 16 + b]!.add (model (mkCtx F lo hi) l).2.2[b * 16 + a]!
def prOf (a b : Nat) : Bool := presOf F lo hi l (a / 4 + 1) (b / 4 + 1)

include hF hl in
theorem HbOf_eq (a b : Nat) (ha : a < 16) (hb : b < 16) :
    cond (presOf F lo hi l (avA (y0fOf F lo hi) (wfOf F lo hi) a).b (avA (y0fOf F lo hi) (wfOf F lo hi) b).b)
      (kadd (mOf (ecsOf F lo hi l) (avA (y0fOf F lo hi) (wfOf F lo hi) a) (avA (y0fOf F lo hi) (wfOf F lo hi) b))
        (mOf (ecsOf F lo hi l) (avA (y0fOf F lo hi) (wfOf F lo hi) b) (avA (y0fOf F lo hi) (wfOf F lo hi) a))) kpt0 =
      HbOf F lo hi l a b := by
  rw [← avOfK_eq F hF lo hi a ha, ← avOfK_eq F hF lo hi b hb]
  have m1 := M_eq F hF lo hi l hl a b ha hb
  have m2 := M_eq F hF lo hi l hl b a hb ha
  simp only [HbOf]
  rw [← m1, ← m2]
  cases hp : presOf F lo hi l (avOfK (envOf F lo hi) a).b (avOfK (envOf F lo hi) b).b
  · obtain ⟨z1, z2⟩ := mOf_absent F lo hi l _ _ hp
    rw [z1, z2]; rfl
  · simp only [cond_true, kadd_eq]

include hF hl in
theorem sdOf_eq (act : List Nat) (hact : ∀ a ∈ act, a < 16) :
    sdOf (act.map (avOfK (envOf F lo hi))) (l.map (vdOf (envOf F lo hi))) =
      ⟨(model (mkCtx F lo hi) l).1,
        act.map (rowA act (gfOf F lo hi l) (HbOf F lo hi l) (prOf F lo hi l) (y0fOf F lo hi) (wfOf F lo hi))⟩ := by
  have hmap : act.map (avOfK (envOf F lo hi)) = act.map (avA (y0fOf F lo hi) (wfOf F lo hi)) :=
    List.map_congr_left fun a ha => avOfK_eq F hF lo hi a (hact a ha)
  rw [hmap]
  simp only [sdOf]
  congr 1
  · exact F0_eq F hF lo hi l hl
  · rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have ha16 := hact a ha
    have hents : ((act.map (avA (y0fOf F lo hi) (wfOf F lo hi))).filter fun v =>
          v.a == (avA (y0fOf F lo hi) (wfOf F lo hi) a).a ||
            presOf F lo hi l (avA (y0fOf F lo hi) (wfOf F lo hi) a).b v.b).map (fun v =>
          (v, cond (presOf F lo hi l (avA (y0fOf F lo hi) (wfOf F lo hi) a).b v.b)
            (kadd (mOf (ecsOf F lo hi l) (avA (y0fOf F lo hi) (wfOf F lo hi) a) v)
              (mOf (ecsOf F lo hi l) v (avA (y0fOf F lo hi) (wfOf F lo hi) a))) kpt0)) =
        (act.filter fun b => b == a || prOf F lo hi l a b).map fun b => (avA (y0fOf F lo hi) (wfOf F lo hi) b, HbOf F lo hi l a b) := by
      rw [List.filter_map, List.map_map]
      apply List.map_congr_left
      intro b hb
      have hb16 := hact b (List.mem_filter.mp hb).1
      simp only [Function.comp]
      congr 1
      exact HbOf_eq F hF lo hi l hl a b ha16 hb16
    simp only [Function.comp, rowA]
    simp only [ecsOf, presOf] at hents
    rw [hents]
    have hg : gOf ((edgesV (l.map (vdOf (envOf F lo hi)))).map fun p => ecK p.1 p.2) (avA (y0fOf F lo hi) (wfOf F lo hi) a) =
        gfOf F lo hi l a := by
      rw [← avOfK_eq F hF lo hi a ha16]; exact g_eq F hF lo hi l hl a ha16
    rw [hg]
    rfl

include hF hl in
theorem partsK_sdOf (act : List Nat) (hact : ∀ a ∈ act, a < 16) (β : Int) :
    partsK (sdOf (act.map (avOfK (envOf F lo hi))) (l.map (vdOf (envOf F lo hi)))) β =
      ((boundParts 16 act (model (mkCtx F lo hi) l).1 (model (mkCtx F lo hi) l).2.1 (model (mkCtx F lo hi) l).2.2
          ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (y0At (mkCtx F lo hi)))
          ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (wAt (mkCtx F lo hi))) β).1,
        act.map (boundParts 16 act (model (mkCtx F lo hi) l).1 (model (mkCtx F lo hi) l).2.1 (model (mkCtx F lo hi) l).2.2
          ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (y0At (mkCtx F lo hi)))
          ((List.range (4 * (mkCtx F lo hi).F.k)).toArray.map (wAt (mkCtx F lo hi))) β).2) := by
  rw [sdOf_eq F hF lo hi l hl act hact, boundParts_eq]
  apply partsK_abs
  · intro a ha b hb _ hp
    have m1 := M_eq F hF lo hi l hl a b (hact a ha) (hact b hb)
    have m2 := M_eq F hF lo hi l hl b a (hact b hb) (hact a ha)
    obtain ⟨z1, z2⟩ := mOf_absent F lo hi l (avOfK (envOf F lo hi) a) (avOfK (envOf F lo hi) b) hp
    simp only [HbOf]
    rw [← m1, ← m2, z1, z2]; rfl
  · intro a h2
    simp only [y0fOf]
    by_cases ha : a < 16
    · have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
      rw [hk, range_map_get _ _ _ ha]; simp [y0At, h2]
    · have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
      rw [hk]; simp [ha]

end conc

/-! ## `comboK` and `leafBoundV` -/

theorem zipWith_map_same {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map fun a => f (g a) (h a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem addGrads_gen (act : List Nat) (Gs : List ((Nat → DIval) × Int)) (f : Nat → DIval) :
    addGrads (Gs.map fun Gw => act.map fun a => kmulW (Gw.1 a) Gw.2) (act.map f) =
      act.map fun a => (Gs.map fun Gw => (Gw.1 a).mul (DIval.pt Gw.2)).foldl DIval.add (f a) := by
  induction Gs generalizing f with
  | nil => rfl
  | cons Gw rest ih =>
    simp only [List.map_cons, addGrads]
    rw [zipWith_map_same, ih]
    simp only [List.foldl_cons, kadd_eq, kmulW_eq]

theorem zipWith_map_right {α β γ : Type} (f : α → β → γ) (g : α → β) (l : List α) :
    List.zipWith f l (l.map g) = l.map fun a => f a (g a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem isum_eq_foldl (l : List DIval) : isum l = l.foldl DIval.add kpt0 := rfl

section final
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int) (sts : List (St × Int))
  (hsts : ∀ p ∈ sts, ∀ g ∈ p.1.verts, g < F.body.size)

include hF hsts in
theorem leafBoundV_eq :
    leafBoundV (envOf F lo hi) sts (sts.map fun p => p.1.verts.map (vdOf (envOf F lo hi))) =
      leafBound (mkCtx F lo hi) sts := by
  have hk : 4 * (mkCtx F lo hi).F.k = 16 := by show 4 * F.k = 16; rw [hF.k4]
  simp only [leafBoundV, leafBound]
  rw [adOf_eq]
  have hact : ∀ a ∈ (List.range (4 * (mkCtx F lo hi).F.k)).filter (fun a => bodyUsed (mkCtx F lo hi) sts (a / 4 + 1)),
      a < 16 := by
    intro a ha; rw [← hk]; exact List.mem_range.mp (List.mem_filter.mp ha).1
  generalize (List.range (4 * (mkCtx F lo hi).F.k)).filter (fun a => bodyUsed (mkCtx F lo hi) sts (a / 4 + 1)) = act
    at hact ⊢
  simp only [hk]
  congr 1
  funext best β
  congr 2
  have hp : ∀ p ∈ sts, partsK (sdOf (act.map (avOfK (envOf F lo hi))) (p.1.verts.map (vdOf (envOf F lo hi)))) β =
      ((boundParts 16 act (model (mkCtx F lo hi) p.1.verts).1 (model (mkCtx F lo hi) p.1.verts).2.1
          (model (mkCtx F lo hi) p.1.verts).2.2
          ((List.range 16).toArray.map (y0At (mkCtx F lo hi))) ((List.range 16).toArray.map (wAt (mkCtx F lo hi))) β).1,
        act.map (boundParts 16 act (model (mkCtx F lo hi) p.1.verts).1
          (model (mkCtx F lo hi) p.1.verts).2.1 (model (mkCtx F lo hi) p.1.verts).2.2
          ((List.range 16).toArray.map (y0At (mkCtx F lo hi))) ((List.range 16).toArray.map (wAt (mkCtx F lo hi))) β).2) := by
    intro p hp
    have h := partsK_sdOf F hF lo hi p.1.verts (hsts p hp) act hact β
    rw [hk] at h
    exact h
  have hw : ∀ a ∈ act, (avOfK (envOf F lo hi) a).w = ((List.range 16).toArray.map (wAt (mkCtx F lo hi)))[a]! := by
    intro a ha
    have h := w_eq F hF lo hi a (hact a ha)
    rw [hk] at h
    exact h.symm
  simp only [comboK, comboVal, zipWith_map_right, List.map_map, ksub_eq]
  congr 1
  · rw [ksum_eq]
    apply isum_congr
    intro p hpm
    simp only [Function.comp, hp p hpm, kmulW_eq]
  · have hG : List.map ((fun pt => List.map (fun g => kmulW g pt.2) pt.1.2) ∘ (fun p => (partsK p.1 β, p.2)) ∘
        fun a => (sdOf (act.map (avOfK (envOf F lo hi))) (a.1.verts.map (vdOf (envOf F lo hi))), a.2)) sts =
        (sts.map fun p => ((boundParts 16 act (model (mkCtx F lo hi) p.1.verts).1 (model (mkCtx F lo hi) p.1.verts).2.1
          (model (mkCtx F lo hi) p.1.verts).2.2
          ((List.range 16).toArray.map (y0At (mkCtx F lo hi))) ((List.range 16).toArray.map (wAt (mkCtx F lo hi))) β).2,
            p.2)).map fun Gw => act.map fun a => kmulW (Gw.1 a) Gw.2 := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p hpm
      simp only [Function.comp, hp p hpm, List.map_map]
      rfl
    have h0 : List.map ((fun _ => kpt0) ∘ avOfK (envOf F lo hi)) act = act.map fun _ => kpt0 := rfl
    rw [hG, h0, addGrads_gen, zipWith_map_same, ksum_eq]
    apply isum_congr
    intro a ha
    simp only [kmulPt_eq, kabs_eq, hw a ha, ← isum_eq_foldl, List.map_map]
    rfl

end final

end WormK3
