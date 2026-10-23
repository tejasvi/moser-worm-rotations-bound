import WormKProof.Valid

/-!
# The kernel-form leaf test equals `leafOK`

`leafOKK_eq : leafOKK F maxsmall tauHi lo hi r = leafOK F maxsmall tauHi lo hi r` for a family with four moving
bodies and body indices at most `4`, and boxes with `12` coordinates; `leafOKRK_eq` for the local refinement.
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (Ang Tr angK trK)

section
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int)

include hF in
theorem stOKV_eq (maxsmall : Nat) (st : St) :
    stOKV F maxsmall st (st.verts.map (vdOf (envOf F lo hi))) = stOK (mkCtx F lo hi) maxsmall st := by
  have hCF : (mkCtx F lo hi).F = F := rfl
  cases st with
  | small v => simp only [stOKV, stOK, hCF]
  | fan v zx zy =>
    simp only [stOKV, stOK, St.verts, hCF]
    by_cases hv : (v.all fun x => decide (x < F.body.size)) = true
    · have hv' : ∀ g ∈ v, g < F.body.size := by simpa using hv
      rw [fanOKV_eq F hF lo hi v hv' zx zy]
    · simp only [Bool.not_eq_true] at hv
      simp [hv]
  | chord v t =>
    simp only [stOKV, stOK, St.verts, hCF]
    by_cases hv : (v.all fun x => decide (x < F.body.size)) = true
    · have hv' : ∀ g ∈ v, g < F.body.size := by simpa using hv
      rw [chordOKV_eq F hF lo hi maxsmall t v hv']
    · simp only [Bool.not_eq_true] at hv
      simp [hv]

theorem stOK_verts (C : Ctx) (maxsmall : Nat) (st : St) (h : stOK C maxsmall st = true) :
    ∀ g ∈ st.verts, g < C.F.body.size := by
  cases st with
  | small v => simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.2
  | fan v zx zy => simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.1.2
  | chord v t => simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.1.2

include hF in
theorem leafCoreK_eq (maxsmall : Nat) (tauHi : Int) (r : Rec) :
    leafCoreK (envOf F lo hi) maxsmall tauHi r = leafOK F maxsmall tauHi lo hi r := by
  have hCF : (mkCtx F lo hi).F = F := rfl
  simp only [leafCoreK, withSts_eq, leafOK, zipWith_map_right, List.all_map]
  have hval : r.sts.all (id ∘ fun a => nonneg a.snd &&
      stOKV (envOf F lo hi).F maxsmall a.fst (List.map (vdOf (envOf F lo hi)) a.fst.verts)) =
      r.sts.all fun x => decide (0 ≤ x.snd) && stOK (mkCtx F lo hi) maxsmall x.fst := by
    apply all_congr_mem
    intro p _
    show (nonneg p.2 && stOKV F maxsmall p.1 (p.1.verts.map (vdOf (envOf F lo hi)))) = _
    rw [nonneg_eq, stOKV_eq F hF lo hi maxsmall p.1]
  rw [hval]
  by_cases hV : (r.sts.all fun x => decide (0 ≤ x.snd) && stOK (mkCtx F lo hi) maxsmall x.fst) = true
  · have hsts : ∀ p ∈ r.sts, ∀ g ∈ p.1.verts, g < F.body.size := by
      intro p hp g hg
      have := (List.all_eq_true.mp hV) p hp
      simp only [Bool.and_eq_true] at this
      exact stOK_verts (mkCtx F lo hi) maxsmall p.1 this.2 g hg
    rw [leafBoundV_eq F hF lo hi r.sts hsts]
  · simp only [Bool.not_eq_true] at hV
    simp [hV]

include hF in
theorem leafOKK_eq (maxsmall : Nat) (tauHi : Int) (r : Rec) (hlo : lo.size = 12) (hhi : hi.size = 12) :
    leafOKK F maxsmall tauHi lo hi r = leafOK F maxsmall tauHi lo hi r := by
  rw [leafOKK_eq_core F maxsmall tauHi lo hi r hlo hhi, leafCoreK_eq F hF lo hi maxsmall tauHi r]

end

end WormK3
