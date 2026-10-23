import WormSound.FinalAt
import WormKC.Pack

/-!
# K composition: data-free box covers

`Cov B`: every point of the box `B` lies in a box that passes `leafOK` and lies in the root box. This is the per-box
fact that the assembly of the worm bound uses; it does not mention any certificate data, so modules can export it
while keeping their data private.
-/

noncomputable section

namespace WormCore.SoundK

open MeasureTheory Worm WormCore WormCore.Sound
open MoserWorm hiding cross shoelace

/-- Every point of `B` lies in a box that passes `leafOK` and lies in the root box. -/
def Cov (B : Array Int × Array Int) : Prop :=
  ∀ x : Fin 12 → ℝ, InBox B.1 B.2 x → ∃ lo hi : Array Int, ∃ r : Rec,
    leafOK famW maxsmallW tauHiW lo hi r = true ∧ InBox lo hi x ∧ BoxSub lo hi rootW.lo rootW.hi

/-- Covers of the two halves give a cover of the box. -/
theorem cov_halves {B l u : Array Int × Array Int} {k : ℕ} (h : halves B.1 B.2 k = some (l, u))
    (hl : Cov l) (hu : Cov u) : Cov B := by
  intro x hx
  rcases halves_cover h hx with h1 | h2
  · exact hl x h1
  · exact hu x h2

/-- A leaf box in the root box that passes `leafOK` covers itself. -/
theorem cov_of_leafOK {lo hi : Array Int} {r : Rec} (hroot : BoxSub lo hi rootW.lo rootW.hi)
    (h : leafOK famW maxsmallW tauHiW lo hi r = true) : Cov (lo, hi) :=
  fun _ hx => ⟨lo, hi, r, h, hx, hroot⟩

/-- A checked subtree (in the root box) covers its box. -/
theorem cov_of_unitOK {B : Array Int × Array Int} (hb : B.1.size = 12 ∧ B.2.size = 12)
    (hroot : BoxSub B.1 B.2 rootW.lo rootW.hi) (codes : String) (recs : List Rec)
    (h : unitOK famW maxsmallW tauHiW rdepthW B codes recs = true) : Cov B := by
  intro x hx
  obtain ⟨lo, hi, r, -, hleaf, hxl, hsub⟩ := unitOK_cover famW maxsmallW tauHiW rdepthW B hb codes recs h x hx
  exact ⟨lo, hi, r, hleaf, hxl, BoxSub.trans hsub hroot⟩

/-- A checked subtree walk over a character list (in the root box) covers its box. -/
theorem cov_of_unitWalk {B : Array Int × Array Int} (hb : B.1.size = 12 ∧ B.2.size = 12)
    (hroot : BoxSub B.1 B.2 rootW.lo rootW.hi) (cs : List Char) (recs : List Rec)
    (h : unitWalk famW maxsmallW tauHiW rdepthW (cs.length + 1) cs [B] recs = some []) : Cov B := by
  apply cov_of_unitOK hb hroot (String.ofList cs) recs
  unfold unitOK
  rw [String.length_ofList, String.toList_ofList, h]

/-- A walk with any leaf test equal to `leafOKR` (the kernel form, once proved equal) covers its box. -/
theorem cov_of_walkG (leafT : Nat → Array Int → Array Int → Rec → Bool)
    (hT : leafT = leafOKR famW maxsmallW tauHiW) {B : Array Int × Array Int}
    (hb : B.1.size = 12 ∧ B.2.size = 12) (hroot : BoxSub B.1 B.2 rootW.lo rootW.hi) (cs : List Char)
    (recs : List Rec) (h : K.walkDone (K.walkG leafT rdepthW (cs.length + 1) cs [B] recs) = true) : Cov B := by
  subst hT
  apply cov_of_unitWalk hb hroot cs recs
  rw [← K.walkG_leafOKR]
  exact K.eq_of_walkDone h

/-- The top tree: if every piece box it lists is covered, every box on its stack is covered. -/
theorem cov_of_topWalk : ∀ (fuel : Nat) (cs : List Char) (st acc out : List (Array Int × Array Int)),
    K.topWalk fuel cs st acc = some out → (∀ b ∈ out, Cov b) → ∀ b ∈ st, Cov b := by
  intro fuel
  induction fuel with
  | zero => intro cs st acc out h; simp [K.topWalk] at h
  | succ n ih =>
    intro cs st acc out h hout
    match cs, st, h with
    | [], [], _ => intro b hb; simp at hb
    | c :: cs, (lo, hi) :: st, h =>
      simp only [K.topWalk] at h
      by_cases hc : c = 'P'
      · simp only [hc, ↓reduceIte] at h
        have hrest := ih cs st ((lo, hi) :: acc) out h hout
        have hacc : ∀ b ∈ (lo, hi) :: acc, b ∈ out := K.topWalk_acc_sub n cs st ((lo, hi) :: acc) out h
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hout _ (hacc _ (List.mem_cons_self))
        · exact hrest b hb'
      · simp only [hc, ↓reduceIte] at h
        cases hk : codeDim c with
        | none => simp [hk] at h
        | some k =>
          simp only [hk] at h
          cases hh : halves lo hi k with
          | none => simp [hh] at h
          | some p =>
            obtain ⟨l, u⟩ := p
            simp only [hh] at h
            have hrest := ih cs (l :: u :: st) acc out h hout
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact cov_halves (B := (lo, hi)) hh (hrest l (by simp)) (hrest u (by simp))
            · exact hrest b (by simp [hb'])

theorem boxSub_of_boxSubB {lo hi lo' hi' : Array Int} (h : K.boxSubB lo hi lo' hi' = true) : BoxSub lo hi lo' hi' := by
  intro i hi12
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi12)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- A checked piece covers its (decoded) box. -/
theorem cov_of_pieceOKK (leafT : Nat → Array Int → Array Int → Rec → Bool)
    (hT : leafT = leafOKR famW maxsmallW tauHiW) (tab : K.BTree Nat) (nb nc cnt ni : Nat)
    (h : K.pieceOKK leafT tab nb nc cnt ni = true) : Cov (K.decodeBox nb) := by
  simp only [K.pieceOKK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, hsub⟩, hw⟩ := h
  exact cov_of_walkG leafT hT ⟨h1, h2⟩ (boxSub_of_boxSubB hsub) _ _ hw

/-- A checked top tree whose piece boxes are covered covers the unit box. -/
theorem cov_of_topOKK (B : Array Int × Array Int) (nt : Nat) (out : List (Array Int × Array Int))
    (h : K.topOKK B nt out = true) (hout : ∀ b ∈ out, Cov b) : Cov B := by
  simp only [K.topOKK, decide_eq_true_eq] at h
  exact cov_of_topWalk _ _ _ _ _ h hout B (List.mem_singleton_self B)

/-- **Assembly from unit covers.** -/
theorem worm_lower_at_of_covers (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ (tauHiW : ℝ) / 2 ^ dfxS)
    (hroot : ∀ x, InDtauOf τ x → InBox rootW.lo rootW.hi x) (skelOf : ℕ → String)
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcov : ∀ p < rootW.nparts, ∀ boxes, unitBoxes rootW p (skelOf p) = some boxes →
      ∀ u < boxes.size, Cov boxes[u]!)
    (K : Set ℂ) (hK : IsConvexCoverM K) : ENNReal.ofReal τ ≤ volume K := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨K', hK'c, hvol, x, hxD, hplace⟩ := w1_domain_of τ hτ0 K hK hlt
  have hxR := hroot x hxD
  obtain ⟨p, hp, k, hk, hxcell⟩ := cells_cover rootW rootExact_rootW rootShape_rootW x hxR
  have hsome : (unitBoxes rootW p (skelOf p)).isSome = true := by
    have := List.all_eq_true.mp hskel p (List.mem_range.mpr hp)
    simpa using this
  obtain ⟨boxes, hboxes⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, hcov'⟩ := unitBoxes_cover rootW rootExact_rootW rootShape_rootW p (skelOf p) boxes hboxes
  obtain ⟨u, hu, hxu⟩ := hcov' k hk x hxcell
  obtain ⟨lo, hi, r, hleaf, hxleaf, hsubroot⟩ := hcov p hp boxes hboxes u hu x hxu
  have hlt' := leafOK_sound famArcs famGid arcsOK_famArcs rfl famGid_bodies maxsmallW (by decide) tauHiW
    (by decide) lo hi (angleRange_of_sub hsubroot) r hleaf x hxleaf K' hK'c hplace
  have hτ' : ENNReal.ofReal τ ≤ ENNReal.ofReal ((tauHiW : ℝ) / 2 ^ dfxS) := ENNReal.ofReal_le_ofReal hτ
  rw [hvol] at hlt'
  exact absurd (lt_of_le_of_lt hτ' hlt') (not_lt.mpr hlt.le)

/-- **Assembly from unit covers** for a general `τ`, in the form of the statement. -/
theorem wormLowerAt_of_covers (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ (tauHiW : ℝ) / 2 ^ dfxS)
    (hroot : ∀ x, InDtauOf τ x → InBox rootW.lo rootW.hi x) (skelOf : ℕ → String)
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcov : ∀ p < rootW.nparts, ∀ boxes, unitBoxes rootW p (skelOf p) = some boxes →
      ∀ u < boxes.size, Cov boxes[u]!) :
    WormLowerAt τ :=
  fun K hK => worm_lower_at_of_covers τ hτ0 hτ hroot skelOf hskel hcov K hK

/-- The per-part facts used by `wormLowerAt_of_covers`: the skeleton walk succeeds and every unit box is covered. -/
def PartOK (skelOf : ℕ → String) (p : ℕ) : Prop :=
  (unitBoxes rootW p (skelOf p)).isSome = true ∧
    ∀ boxes, unitBoxes rootW p (skelOf p) = some boxes → ∀ u < boxes.size, Cov boxes[u]!

theorem partOK_of (skelOf : ℕ → String) (p : ℕ) (cs : List Char) (hs : skelOf p = String.ofList cs)
    (ub : List (Array Int × Array Int)) (hb : K.unitBoxesL rootW p cs = some ub.toArray)
    (hcov : ∀ b ∈ ub, Cov b) : PartOK skelOf p := by
  rw [PartOK, hs, K.unitBoxes_ofList, hb]
  refine ⟨rfl, ?_⟩
  intro boxes h u hu
  cases h
  rw [List.size_toArray] at hu
  have : ub.toArray[u]! = ub[u] := by
    rw [getElem!_pos ub.toArray u (by simpa using hu)]
    simp
  rw [this]
  exact hcov _ (List.getElem_mem hu)

/-- All parts give the bound. -/
theorem wormLowerAt_of_parts (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ (tauHiW : ℝ) / 2 ^ dfxS)
    (hroot : ∀ x, InDtauOf τ x → InBox rootW.lo rootW.hi x) (skelOf : ℕ → String)
    (h : ∀ p < rootW.nparts, PartOK skelOf p) : WormLowerAt τ := by
  apply wormLowerAt_of_covers τ hτ0 hτ hroot skelOf
  · rw [List.all_eq_true]
    intro p hp
    exact (h p (List.mem_range.mp hp)).1
  · intro p hp boxes hb
    exact (h p hp).2 boxes hb

/-- Blocks of `m` consecutive indices: used to assemble the 16,384 part facts with few references per
declaration (linking cost grows quadratically with the references in one declaration). -/
theorem forall_lt_of_blocks {P : ℕ → Prop} (n m : ℕ) (h : ∀ j < n, ∀ i < m, P (m * j + i)) :
    ∀ p < m * n, P p := by
  intro p hp
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  have hj : p / m < n := by
    rw [Nat.div_lt_iff_lt_mul hm]
    rwa [Nat.mul_comm] at hp
  have := h (p / m) hj (p % m) (Nat.mod_lt _ hm)
  rwa [Nat.div_add_mod] at this

end WormCore.SoundK
