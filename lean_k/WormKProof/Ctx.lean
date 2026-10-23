import WormKProof.CPS

/-!
# The kernel-form context agrees with `mkCtx`

`envOf F lo hi` is the environment that `leafOKK` builds from the box; its vertex data `vdOf` agree with the arrays
`RQ`, `X0`, `MV` of `mkCtx F lo hi`, and its per-body data with `bd`.
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (natK intK arrK Ang Tr angK trK)

def envOf (F : Fam) (lo hi : Array Int) : Env :=
  ⟨F, angK lo[0]! hi[0]!, angK lo[3]! hi[3]!, angK lo[6]! hi[6]!, angK lo[9]! hi[9]!,
    trK lo[1]! hi[1]! lo[2]! hi[2]!, trK lo[4]! hi[4]! lo[5]! hi[5]!,
    trK lo[7]! hi[7]! lo[8]! hi[8]!, trK lo[10]! hi[10]! lo[11]! hi[11]!⟩

theorem list12 (l : List Int) (h : l.length = 12) :
    l = [l[0]!, l[1]!, l[2]!, l[3]!, l[4]!, l[5]!, l[6]!, l[7]!, l[8]!, l[9]!, l[10]!, l[11]!] := by
  match l, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

theorem leafOKK_eq_core (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec)
    (hlo : lo.size = 12) (hhi : hi.size = 12) :
    leafOKK F maxsmall tauHi lo hi r = leafCoreK (envOf F lo hi) maxsmall tauHi r := by
  have h1 : lo.toList.take 12 = lo.toList := List.take_of_length_le (by simp [hlo])
  have h2 : hi.toList.take 12 = hi.toList := List.take_of_length_le (by simp [hhi])
  have e1 := list12 lo.toList (by simp [hlo])
  have e2 := list12 hi.toList (by simp [hhi])
  simp only [leafOKK, arrK_eq, h1, h2]
  rw [e1, e2]
  simp only [envOf, Array.getElem!_toList]

/-! ## Per-body and per-vertex data -/

theorem bd_eq (F : Fam) (lo hi : Array Int) (b : Nat) (hb0 : b ≠ 0) (hbk : b ≤ F.k) :
    (mkCtx F lo hi).bd[b]! = bodyData lo hi b := by
  simp [mkCtx, hb0, Nat.lt_succ_of_le hbk]

theorem angOf_eq (F : Fam) (lo hi : Array Int) (b : Nat) (hb1 : 1 ≤ b) (hb4 : b ≤ 4) :
    angOf (envOf F lo hi) b = angK lo[3 * (b - 1)]! hi[3 * (b - 1)]! := by
  rcases b with _ | _ | _ | _ | _ | b <;> first | omega | rfl

theorem trOf_eq (F : Fam) (lo hi : Array Int) (b : Nat) (hb1 : 1 ≤ b) (hb4 : b ≤ 4) :
    trOf (envOf F lo hi) b = trK lo[3 * (b - 1) + 1]! hi[3 * (b - 1) + 1]! lo[3 * (b - 1) + 2]! hi[3 * (b - 1) + 2]! := by
  rcases b with _ | _ | _ | _ | _ | b <;> first | omega | rfl

/-- The family assumptions used: four moving bodies, every body index at most `4`. -/
structure FamOK (F : Fam) : Prop where
  k4 : F.k = 4
  body_le : ∀ g : Nat, F.body[g]! ≤ 4

theorem vdOf_eq (F : Fam) (hF : FamOK F) (lo hi : Array Int) (g : Nat) :
    vdOf (envOf F lo hi) g =
      if F.body[g]! = 0 then vd0 F g
      else vdK F g F.body[g]! (angOf (envOf F lo hi) F.body[g]!) (trOf (envOf F lo hi) F.body[g]!) := by
  have h4 := hF.body_le g
  simp only [vdOf, envOf, angOf, trOf]
  generalize F.body[g]! = b at h4 ⊢
  rcases b with _ | _ | _ | _ | _ | b <;> first | omega | rfl

theorem vdOf_b (F : Fam) (hF : FamOK F) (lo hi : Array Int) (g : Nat) : (vdOf (envOf F lo hi) g).b = F.body[g]! := by
  rw [vdOf_eq F hF]; split <;> simp_all [vd0, vdK]

theorem range_map_get {α : Type} [Inhabited α] (n g : Nat) (f : Nat → α) (h : g < n) :
    ((List.range n).toArray.map f)[g]! = f g := by
  simp [h]

theorem bdK_eq (F : Fam) (hF : FamOK F) (lo hi : Array Int) (b : Nat) (hb0 : b ≠ 0) (hb4 : b ≤ 4) :
    (mkCtx F lo hi).bd[b]! = bodyData lo hi b := bd_eq F lo hi b hb0 (hF.k4 ▸ hb4)

theorem RQ_eq (F : Fam) (lo hi : Array Int) (g : Nat) (hg : g < F.body.size) :
    (mkCtx F lo hi).RQ[g]! = if F.body[g]! = 0 then F.q[g]! else
      V2.rot (mkCtx F lo hi).bd[F.body[g]!]!.s (mkCtx F lo hi).bd[F.body[g]!]!.c F.q[g]! := by
  show ((List.range F.body.size).toArray.map _)[g]! = _
  rw [range_map_get _ _ _ hg]
  rfl

theorem X0_eq (F : Fam) (lo hi : Array Int) (g : Nat) (hg : g < F.body.size) :
    (mkCtx F lo hi).X0[g]! = if F.body[g]! = 0 then F.q[g]! else
      V2.add (mkCtx F lo hi).bd[F.body[g]!]!.tc (mkCtx F lo hi).RQ[g]! := by
  show ((List.range F.body.size).toArray.map _)[g]! = _
  rw [range_map_get _ _ _ hg]
  rfl

theorem MV_eq (F : Fam) (lo hi : Array Int) (g : Nat) (hg : g < F.body.size) :
    (mkCtx F lo hi).MV[g]! = if F.body[g]! = 0 then DIval.pt 0 else
      (F.qn[g]!.mul (DIval.pt (mkCtx F lo hi).bd[F.body[g]!]!.h)).add (mkCtx F lo hi).bd[F.body[g]!]!.trad := by
  show ((List.range F.body.size).toArray.map _)[g]! = _
  rw [range_map_get _ _ _ hg]
  rfl

theorem angOf_bd (F : Fam) (hF : FamOK F) (lo hi : Array Int) (b : Nat) (hb0 : b ≠ 0) (hb4 : b ≤ 4) :
    (angOf (envOf F lo hi) b).s = (mkCtx F lo hi).bd[b]!.s ∧ (angOf (envOf F lo hi) b).c = (mkCtx F lo hi).bd[b]!.c ∧
      (angOf (envOf F lo hi) b).h = (mkCtx F lo hi).bd[b]!.h := by
  rw [bdK_eq F hF lo hi b hb0 hb4, angOf_eq F lo hi b (Nat.one_le_iff_ne_zero.mpr hb0) hb4]
  exact ⟨rfl, rfl, rfl⟩

theorem trOf_bd (F : Fam) (hF : FamOK F) (lo hi : Array Int) (b : Nat) (hb0 : b ≠ 0) (hb4 : b ≤ 4) :
    (trOf (envOf F lo hi) b).tc = (mkCtx F lo hi).bd[b]!.tc ∧ (trOf (envOf F lo hi) b).trad = (mkCtx F lo hi).bd[b]!.trad ∧
      (trOf (envOf F lo hi) b).hx = (mkCtx F lo hi).bd[b]!.hx ∧ (trOf (envOf F lo hi) b).hy = (mkCtx F lo hi).bd[b]!.hy := by
  rw [bdK_eq F hF lo hi b hb0 hb4, trOf_eq F lo hi b (Nat.one_le_iff_ne_zero.mpr hb0) hb4]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Vertex data agree with the arrays of `mkCtx`. -/
theorem vdOf_ctx (F : Fam) (hF : FamOK F) (lo hi : Array Int) (g : Nat) (hg : g < F.body.size) :
    let v := vdOf (envOf F lo hi) g
    let C := mkCtx F lo hi
    v.b = F.body[g]! ∧ v.rq = C.RQ[g]! ∧ v.x0 = C.X0[g]! ∧ v.mv = C.MV[g]! := by
  intro v C
  have h4 := hF.body_le g
  refine ⟨vdOf_b F hF lo hi g, ?_⟩
  simp only [v, C, RQ_eq F lo hi g hg, X0_eq F lo hi g hg, MV_eq F lo hi g hg, vdOf_eq F hF]
  by_cases h0 : F.body[g]! = 0
  · simp [h0, vd0]
  · obtain ⟨hs, hc, hh⟩ := angOf_bd F hF lo hi _ h0 h4
    obtain ⟨htc, htr, -, -⟩ := trOf_bd F hF lo hi _ h0 h4
    simp [h0, vdK, hs, hc, hh, htc, htr]

end WormK3
