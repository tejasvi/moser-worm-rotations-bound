import WormKC.Cov
import WormKProof.R4

/-!
# The production leaf test in the K layout

The kernel-form leaf test `WormK4.leafOKRK4 famW maxsmallW tauHiW` agrees with `leafOKR` on boxes
with 12 coordinates (`WormK4.leafOKRK4_eq`, `WormK3.famOK_famW`). Walks keep that size, so a piece checked with it is
covered (`cov_of_pieceOKK_K`).
-/

noncomputable section

namespace WormCore.SoundK

open WormCore WormCore.Sound

/-- The walk with the kernel-form leaf test is `unitWalk` on stacks of 12-coordinate boxes. -/
theorem walkG_leafOKRK (rdepth : Nat) (fuel : Nat) :
    ∀ (cs : List Char) (st : List (Array Int × Array Int)) (recs : List Rec),
      (∀ b ∈ st, b.1.size = 12 ∧ b.2.size = 12) →
      K.walkG (WormK4.leafOKRK4 famW maxsmallW tauHiW) rdepth fuel cs st recs =
        unitWalk famW maxsmallW tauHiW rdepth fuel cs st recs := by
  induction fuel with
  | zero => intro cs st recs _; rfl
  | succ n ih =>
    intro cs st recs hst
    match cs, st with
    | [], [] => rfl
    | [], _ :: _ => rfl
    | _ :: _, [] => rfl
    | c :: cs, (lo, hi) :: st =>
      have hb := hst (lo, hi) (List.mem_cons_self)
      have hrest : ∀ b ∈ st, b.1.size = 12 ∧ b.2.size = 12 := fun b h => hst b (List.mem_cons_of_mem _ h)
      simp only [K.walkG, unitWalk]
      by_cases hc : c = 'L' ∨ c = 'K'
      · simp only [hc, ↓reduceIte]
        cases recs with
        | nil => rfl
        | cons r rs =>
          simp only
          rw [WormK4.leafOKRK4_eq famW WormK3.famOK_famW maxsmallW tauHiW rdepth lo hi r hb.1 hb.2]
          cases leafOKR famW maxsmallW tauHiW rdepth lo hi r <;> simp [ih cs st rs hrest]
      · simp only [hc, ↓reduceIte]
        cases hk : codeDim c with
        | none => rfl
        | some k =>
          simp only
          cases hh : halves lo hi k with
          | none => rfl
          | some p =>
            obtain ⟨l, u⟩ := p
            simp only
            apply ih
            have hs := WormK3.halves_size lo hi k l u hh hb.1 hb.2
            intro b hbm
            rcases List.mem_cons.mp hbm with rfl | hbm
            · exact hs.1
            rcases List.mem_cons.mp hbm with rfl | hbm
            · exact hs.2
            · exact hrest b hbm

/-- A piece checked with the kernel-form leaf test covers its (decoded) box. -/
theorem cov_of_pieceOKK_K (tab : K.BTree Nat) (nb nc cnt ni : Nat)
    (h : K.pieceOKK (WormK4.leafOKRK4 famW maxsmallW tauHiW) tab nb nc cnt ni = true) : Cov (K.decodeBox nb) := by
  simp only [K.pieceOKK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, hsub⟩, hw⟩ := h
  apply cov_of_unitWalk ⟨h1, h2⟩ (boxSub_of_boxSubB hsub) _ _
  rw [← walkG_leafOKRK rdepthW _ _ _ _ (by simp [h1, h2])]
  exact K.eq_of_walkDone hw

end WormCore.SoundK
