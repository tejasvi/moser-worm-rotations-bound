import WormKProof.Leaf
import WormK.Walk3

/-!
# The String-free walk equals `unitWalk`

`pieceOK box cs recs = unitOK famW maxsmallW tauHiW rdepthW box (String.ofList cs) recs` for boxes with `12`
coordinates, so `unitOK_cover` applies to every checked piece.
-/

namespace WormK3

open MoserWorm WormCore

theorem famOK_famW : FamOK famW where
  k4 := by decide
  body_le := by
    intro g
    by_cases hg : g < famW.body.size
    · have hall : ∀ i < famW.body.size, famW.body[i]! ≤ 4 := by decide
      exact hall g hg
    · simp [Array.getElem!_eq_getD, Array.getD, hg]

theorem size_set! (a : Array Int) (i : Nat) (v : Int) : (a.set! i v).size = a.size := by
  simp [Array.set!]

section
variable (F : Fam) (hF : FamOK F) (maxsmall : Nat) (tauHi : Int)

include hF in
theorem leafOKRK_eq (d : Nat) : ∀ (lo hi : Array Int) (r : Rec), lo.size = 12 → hi.size = 12 →
    leafOKRK F maxsmall tauHi d lo hi r = leafOKR F maxsmall tauHi d lo hi r := by
  induction d with
  | zero => intro lo hi r hlo hhi; simp only [leafOKRK, leafOKR, leafOKK_eq F hF lo hi maxsmall tauHi r hlo hhi]
  | succ d ih =>
    intro lo hi r hlo hhi
    simp only [leafOKRK, leafOKR, leafOKK_eq F hF lo hi maxsmall tauHi r hlo hhi]
    rw [ih lo _ r hlo (by rw [size_set!]; exact hhi), ih _ hi r (by rw [size_set!]; exact hlo) hhi]

theorem halves_size (lo hi : Array Int) (k : Nat) (l u : Array Int × Array Int)
    (h : halves lo hi k = some (l, u)) (hlo : lo.size = 12) (hhi : hi.size = 12) :
    (l.1.size = 12 ∧ l.2.size = 12) ∧ (u.1.size = 12 ∧ u.2.size = 12) := by
  simp only [halves] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [size_set!, hlo, hhi]
  · simp at h

include hF in
theorem walkK_eq (rdepth : Nat) (fuel : Nat) : ∀ (cs : List Char) (st : List (Array Int × Array Int)) (recs : List Rec),
    (∀ b ∈ st, b.1.size = 12 ∧ b.2.size = 12) →
    walkK F maxsmall tauHi rdepth fuel cs st recs = unitWalk F maxsmall tauHi rdepth fuel cs st recs := by
  induction fuel with
  | zero => intro cs st recs _; rfl
  | succ fuel ih =>
    intro cs st recs hst
    match cs, st with
    | [], [] => rfl
    | [], _ :: _ => rfl
    | _ :: _, [] => rfl
    | c :: cs, (lo, hi) :: st =>
      have hb := hst (lo, hi) List.mem_cons_self
      have hst' : ∀ b ∈ st, b.1.size = 12 ∧ b.2.size = 12 := fun b hb' => hst b (List.mem_cons_of_mem _ hb')
      simp only [walkK, unitWalk]
      by_cases hc : c = 'L' ∨ c = 'K'
      · simp only [hc, ite_true]
        cases recs with
        | nil => rfl
        | cons r rs =>
          simp only []
          rw [leafOKRK_eq F hF maxsmall tauHi rdepth lo hi r hb.1 hb.2]
          by_cases hl : leafOKR F maxsmall tauHi rdepth lo hi r = true
          · simp only [hl, ite_true]; exact ih _ _ _ hst'
          · simp only [hl, Bool.false_eq_true, ite_false]
      · simp only [hc, ite_false]
        cases hk : codeDim c with
        | none => rfl
        | some k =>
          simp only []
          cases hh : halves lo hi k with
          | none => rfl
          | some p =>
            obtain ⟨l, u⟩ := p
            have hs := halves_size lo hi _ l u hh hb.1 hb.2
            simp only []
            apply ih
            intro b hb'
            simp only [List.mem_cons] at hb'
            rcases hb' with rfl | rfl | hb'
            · exact hs.1
            · exact hs.2
            · exact hst' b hb'

end

theorem pieceOK_eq (box : Array Int × Array Int) (hb : box.1.size = 12 ∧ box.2.size = 12) (cs : List Char) (recs : List Rec) :
    pieceOK box cs recs = unitOK famW maxsmallW tauHiW rdepthW box (String.ofList cs) recs := by
  simp only [pieceOK, unitOK, String.toList_ofList, String.length_ofList]
  rw [walkK_eq famW famOK_famW maxsmallW tauHiW rdepthW _ cs [box] recs (by
    intro b hb'; simp only [List.mem_singleton] at hb'; subst hb'; exact hb)]
  rfl

end WormK3
