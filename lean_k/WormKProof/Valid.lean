import WormKProof.Bound

/-!
# Validity: `stOKV = stOK`
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (Ang Tr angK trK)

theorem rotL_length {α : Type} (s : Nat) (l : List α) : (rotL s l).length = l.length := by
  simp only [rotL, List.length_append, List.length_drop, List.length_take]; omega

theorem rotL_getElem {α : Type} (s : Nat) (l : List α) (hs : s < l.length) (j : Nat) (hj : j < l.length) :
    (rotL s l)[j]'(by rw [rotL_length]; exact hj) = l[(s + j) % l.length]'(Nat.mod_lt _ (by omega)) := by
  simp only [rotL]
  by_cases h : j < l.length - s
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_drop]
    congr 1; rw [Nat.mod_eq_of_lt (by omega)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_take, List.length_drop]
    congr 1
    have : (s + j) % l.length = s + j - l.length := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [this]; omega

section vd
variable (F : Fam) (hF : FamOK F) (lo hi : Array Int)

theorem vdOf_g (g : Nat) : (vdOf (envOf F lo hi) g).g = g := by
  simp only [vdOf]; split <;> rfl

include hF in
/-- Per-body data of a moving vertex. -/
theorem vdOf_body (g : Nat) (h0 : F.body[g]! ≠ 0) :
    (vdOf (envOf F lo hi) g).A.s = (mkCtx F lo hi).bd[F.body[g]!]!.s ∧
    (vdOf (envOf F lo hi) g).A.c = (mkCtx F lo hi).bd[F.body[g]!]!.c ∧
    (vdOf (envOf F lo hi) g).A.h = (mkCtx F lo hi).bd[F.body[g]!]!.h ∧
    (vdOf (envOf F lo hi) g).T.tc = (mkCtx F lo hi).bd[F.body[g]!]!.tc ∧
    (vdOf (envOf F lo hi) g).T.trad = (mkCtx F lo hi).bd[F.body[g]!]!.trad := by
  have h4 := hF.body_le g
  rw [vdOf_eq F hF]
  simp only [h0, ite_false, vdK]
  obtain ⟨hs, hc, hh⟩ := angOf_bd F hF lo hi _ h0 h4
  obtain ⟨htc, htr, -, -⟩ := trOf_bd F hF lo hi _ h0 h4
  exact ⟨hs, hc, hh, htc, htr⟩

theorem pos_eq (x : Int) : pos x = decide (0 < x) := by
  simp only [pos, ile_eq]; by_cases h : x ≤ 0 <;> simp [h] <;> omega

theorem kvsub_eq (u v : V2) : kvsub u v = V2.sub u v := by
  simp only [kvsub, V2.sub, ksub_eq]

include hF in
theorem fanVarV_eq (z : V2) (a b : Nat) (ha : a < F.body.size) (hb : b < F.body.size) :
    fanVarV F z (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) = fanVar (mkCtx F lo hi) z a b := by
  obtain ⟨ba, -, xa, ma⟩ := vdOf_ctx F hF lo hi a ha
  obtain ⟨bb, -, xb, mb⟩ := vdOf_ctx F hF lo hi b hb
  have hCF : (mkCtx F lo hi).F = F := rfl
  simp only [fanVarV, fanVar, ba, bb, xa, xb, ma, mb, vdOf_g, hCF]
  by_cases he : F.body[a]! = F.body[b]!
  · simp only [he, ite_true]
    by_cases h0 : F.body[b]! = 0
    · simp only [h0, ite_true]
    · have hA := vdOf_body F hF lo hi a (he ▸ h0)
      rw [he] at hA
      simp only [h0, ite_false, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2]
  · simp only [he, ite_false]

include hF in
theorem fanDetPos_eq (z : V2) (a b : Nat) (ha : a < F.body.size) (hb : b < F.body.size) :
    fanDetPos F z (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) = decide (0 < fanDetLo (mkCtx F lo hi) z a b) := by
  obtain ⟨-, -, xa, -⟩ := vdOf_ctx F hF lo hi a ha
  obtain ⟨-, -, xb, -⟩ := vdOf_ctx F hF lo hi b hb
  simp only [fanDetPos, fanDetLo, pos_eq, ksub_eq, kdet_eq, kvsub_eq, xa, xb, fanVarV_eq F hF lo hi z a b ha hb]
  rfl

theorem getD_range_map {α : Type} [Inhabited α] (n i : Nat) (f : Nat → α) (dflt : α) (h : i < n) :
    ((List.range n).map f).getD i dflt = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {α : Type} (l : List α) (i : Nat) (dflt : α) (h : l.length ≤ i) : l.getD i dflt = dflt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem arr_get_ge {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]! = default := by
  simp [Array.getElem!_eq_getD, Array.getD, Nat.not_lt.mpr h]

theorem zipWith_getD {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) (i : Nat) (dflt : γ)
    (h1 : i < l1.length) (h2 : i < l2.length) :
    (List.zipWith f l1 l2).getD i dflt = f l1[i] l2[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]

theorem range_arr_size {α : Type} (n : Nat) (f : Nat → α) : ((List.range n).toArray.map f).size = n := by
  simp

theorem range_list_getD {α : Type} (n i : Nat) (f : Nat → List α) (h : n ≤ i) :
    ((List.range n).map f).getD i [] = [] := getD_ge _ _ _ (by simp; omega)

/-- A sign table of `fanOK` (rows `i < m`, offsets `d ≤ m`) against the offset-major table of `fanOKV`. -/
theorem table_eq (m : Nat) (xs : List V2) (hxs : xs.length = m) (X : Nat → V2) (hX : ∀ i (h : i < m), xs[i] = X i)
    (test : V2 → V2 → Bool) (i d : Nat) :
    ((((List.range m).toArray.map fun i => (List.range (m + 1)).toArray.map fun d =>
        (decide (1 ≤ d) && decide (d < m) && test (X i) (X ((i + d) % m))))[i]!)[d]!) =
    (((List.range (m + 1)).map fun d => cond (decide (1 ≤ d) && decide (d < m))
        (List.zipWith test xs (rotL d xs)) (xs.map fun _ => false)).getD d []).getD i false := by
  -- the length of every row of the offset-major table
  have hlen : ∀ d', (cond (decide (1 ≤ d') && decide (d' < m)) (List.zipWith test xs (rotL d' xs))
      (xs.map fun _ => false)).length = m := by
    intro d'; cases (decide (1 ≤ d') && decide (d' < m)) <;> simp [rotL_length, hxs]
  by_cases hi : i < m
  · have hrow := range_map_get m i (fun i => (List.range (m + 1)).toArray.map fun d =>
        (decide (1 ≤ d) && decide (d < m) && test (X i) (X ((i + d) % m)))) hi
    rw [hrow]
    by_cases hd : d < m + 1
    · have hcell := range_map_get (m + 1) d (fun d =>
        (decide (1 ≤ d) && decide (d < m) && test (X i) (X ((i + d) % m)))) hd
      rw [hcell, getD_range_map _ _ _ _ hd]
      by_cases hc : (decide (1 ≤ d) && decide (d < m)) = true
      · simp only [hc, Bool.cond_true, Bool.true_and]
        have hd' : d < m := by simp at hc; omega
        rw [zipWith_getD _ _ _ _ _ (by omega) (by rw [rotL_length]; omega)]
        rw [rotL_getElem _ _ (by omega) _ (by omega)]
        have e1 := hX i hi
        have e2 := hX ((d + i) % xs.length) (by rw [hxs]; exact Nat.mod_lt _ (by omega))
        rw [e1, e2, hxs, Nat.add_comm d i]
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.cond_false, Bool.false_and]
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, hi, hxs]
    · have hcell := arr_get_ge ((List.range (m + 1)).toArray.map fun d =>
        (decide (1 ≤ d) && decide (d < m) && test (X i) (X ((i + d) % m)))) d (by rw [range_arr_size]; omega)
      rw [hcell, range_list_getD _ _ _ (by omega)]
      rfl
  · have hrow := arr_get_ge ((List.range m).toArray.map fun i => (List.range (m + 1)).toArray.map fun d =>
        (decide (1 ≤ d) && decide (d < m) && test (X i) (X ((i + d) % m)))) i (by rw [range_arr_size]; omega)
    rw [hrow]
    by_cases hd : d < m + 1
    · rw [getD_range_map _ _ _ _ hd, getD_ge _ _ _ (by rw [hlen]; omega)]
      rfl
    · rw [range_list_getD _ _ _ (by omega)]
      rfl

include hF in
theorem fanOKV_eq (v : List Nat) (hv : ∀ g ∈ v, g < F.body.size) (zx zy : Int) :
    fanOKV F (v.map (vdOf (envOf F lo hi))) zx zy = fanOK (mkCtx F lo hi) v zx zy := by
  simp only [fanOKV, fanOK, List.length_map]
  have hva : ∀ j (h : j < v.length), v.toArray[j]! = v[j] := by
    intro j h; simp [h]
  have hxs : ∀ i (h : i < v.length),
      ((v.map (vdOf (envOf F lo hi))).map fun w => kvsub w.x0 (DIval.pt zx, DIval.pt zy))[i]'(by simpa using h) =
        V2.sub (mkCtx F lo hi).X0[v.toArray[i]!]! (DIval.pt zx, DIval.pt zy) := by
    intro i h
    simp only [List.getElem_map, kvsub_eq, hva i h]
    rw [(vdOf_ctx F hF lo hi v[i] (hv _ (List.getElem_mem h))).2.2.1]
  have hlen : ((v.map (vdOf (envOf F lo hi))).map fun w => kvsub w.x0 (DIval.pt zx, DIval.pt zy)).length = v.length := by
    simp
  congr 1
  · congr 1
    -- the consecutive determinants on the whole box
    have hz : List.zipWith (fun u w => fanDetPos F (DIval.pt zx, DIval.pt zy) u w) (v.map (vdOf (envOf F lo hi)))
        (rotL 1 (v.map (vdOf (envOf F lo hi)))) = (List.range v.length).map fun j =>
          decide (0 < fanDetLo (mkCtx F lo hi) (DIval.pt zx, DIval.pt zy) v.toArray[j]! v.toArray[(j + 1) % v.length]!) := by
      apply List.ext_getElem
      · simp [rotL_length]
      · intro j h1 h2
        have hj : j < v.length := by simpa using h2
        simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
        rw [rotL1_getElem _ j (by simpa using hj)]
        simp only [List.getElem_map, List.length_map]
        have hj1 : (j + 1) % v.length < v.length := Nat.mod_lt _ (by omega)
        rw [hva j hj, hva _ hj1]
        exact fanDetPos_eq F hF lo hi _ v[j] v[(j + 1) % v.length] (hv _ (List.getElem_mem hj))
          (hv _ (List.getElem_mem hj1))
    rw [hz, List.all_map]
    rfl
  · congr 1
    funext s0
    congr 2
    congr 1
    · funext i d
      have htest : (fun a b : V2 => pos (kdet a b).lo) = fun x y => decide (0 < (V2.det x y).lo) := by
        funext a b; simp only [pos_eq, kdet_eq]
      rw [htest]
      exact (table_eq v.length _ hlen (fun i => V2.sub (mkCtx F lo hi).X0[v.toArray[i]!]! (DIval.pt zx, DIval.pt zy))
        hxs (fun x y => decide (0 < (V2.det x y).lo)) i d).symm
    · funext i d
      have htest : (fun a b : V2 => pos (kdot a b).lo) = fun x y => decide (0 < ((x.1.mul y.1).add (x.2.mul y.2)).lo) := by
        funext a b; simp only [pos_eq, kdot, kadd_eq, kmul_eq]
      rw [htest]
      exact (table_eq v.length _ hlen (fun i => V2.sub (mkCtx F lo hi).X0[v.toArray[i]!]! (DIval.pt zx, DIval.pt zy))
        hxs (fun x y => decide (0 < ((x.1.mul y.1).add (x.2.mul y.2)).lo)) i d).symm

include hF in
theorem pairMoveV_eq (a b : Nat) (ha : a < F.body.size) (hb : b < F.body.size) :
    pairMoveV F (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) = pairMove (mkCtx F lo hi) a b := by
  obtain ⟨ba, -, -, ma⟩ := vdOf_ctx F hF lo hi a ha
  obtain ⟨bb, -, -, mb⟩ := vdOf_ctx F hF lo hi b hb
  have hCF : (mkCtx F lo hi).F = F := rfl
  simp only [pairMoveV, pairMove, ba, bb, ma, mb, vdOf_g, hCF]
  by_cases he : F.body[a]! = F.body[b]!
  · simp only [he, ite_true]
    by_cases h0 : F.body[b]! = 0
    · simp only [h0, ite_true]
    · have hA := vdOf_body F hF lo hi a (he ▸ h0)
      rw [he] at hA
      simp only [h0, ite_false, hA.2.2.1]
  · simp only [he, ite_false]

include hF in
theorem diffV_eq (a b : Nat) (ha : a < F.body.size) (hb : b < F.body.size) :
    diffV F (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) = diff (mkCtx F lo hi) a b := by
  obtain ⟨ba, -, xa, -⟩ := vdOf_ctx F hF lo hi a ha
  obtain ⟨bb, -, xb, -⟩ := vdOf_ctx F hF lo hi b hb
  have hCF : (mkCtx F lo hi).F = F := rfl
  simp only [diffV, diff, ba, bb, xa, xb, vdOf_g, hCF]
  by_cases h : F.body[a]! = F.body[b]! ∧ F.body[a]! ≠ 0
  · have hA := vdOf_body F hF lo hi a h.2
    simp only [h, and_self, ite_true, hA.1, hA.2.1]
  · simp only [h, ite_false]

include hF in
theorem det3V_eq (a b i : Nat) (ha : a < F.body.size) (hb : b < F.body.size) (hi' : i < F.body.size) :
    det3V F (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) (vdOf (envOf F lo hi) i) = det3 (mkCtx F lo hi) a b i := by
  obtain ⟨ba, -, -, -⟩ := vdOf_ctx F hF lo hi a ha
  obtain ⟨bb, -, -, -⟩ := vdOf_ctx F hF lo hi b hb
  obtain ⟨bi, -, -, -⟩ := vdOf_ctx F hF lo hi i hi'
  have hCF : (mkCtx F lo hi).F = F := rfl
  simp only [det3V, det3, ba, bb, bi, vdOf_g, hCF, diffV_eq F hF lo hi a b ha hb, diffV_eq F hF lo hi a i ha hi',
    pairMoveV_eq F hF lo hi a b ha hb, pairMoveV_eq F hF lo hi a i ha hi', kdet_eq]

theorem rotL_map {α β : Type} (f : α → β) (s : Nat) (l : List α) : rotL s (l.map f) = (rotL s l).map f := by
  simp [rotL, List.map_drop, List.map_take]

theorem at'_eq (l : List Nat) (j : Nat) (h : 0 < l.length) : at' l j = l[j % l.length]'(Nat.mod_lt _ h) := by
  simp [at', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ h)]

theorem all_range_skip0 (d : Nat) (f : Nat → Bool) :
    (List.range d).all (fun k => decide (k = 0) || f k) = ((List.range d).drop 1).all f := by
  cases d with
  | zero => rfl
  | succ n =>
    rw [List.range_succ_eq_map]
    simp only [List.all_cons, List.drop_succ_cons, List.drop_zero, List.all_map, decide_true, Bool.true_or,
      Bool.true_and]
    apply congrArg
    funext k
    simp

theorem all_range_getD (xs : List Nat) (h : Nat → Bool) (d : Nat) :
    (List.range xs.length).all (fun j => h (xs.getD j d)) = xs.all h := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.all_cons, List.getD_cons_zero, List.all_map]
    congr 1

theorem all_range_pairs (xs : List Nat) (h : Nat → Nat → Bool) (d : Nat) :
    (List.range xs.length).all (fun j => decide (xs.length ≤ j + 1) || h (xs.getD j d) (xs.getD (j + 1) d)) =
      (List.zipWith h xs xs.tail).all id := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    cases ys with
    | nil => simp
    | cons z zs =>
      simp only [List.all_cons, List.getD_cons_zero, List.getD_cons_succ, List.all_map, List.tail_cons,
        List.zipWith_cons_cons, id]
      congr 1

theorem all_range_congr (n : Nat) (f g : Nat → Bool) (h : ∀ j < n, f j = g j) :
    (List.range n).all f = (List.range n).all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H j hj => h j hj ▸ H j hj, fun H j hj => (h j hj).symm ▸ H j hj⟩

theorem all_range_add2 (n : Nat) (f : Nat → Bool) :
    (List.range (n + 2)).all f = (f 0 && (f 1 && (List.range n).all fun j => f (j + 2))) := by
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp only [List.all_cons, List.map_cons, List.map_map, List.all_map, Function.comp_def, Nat.succ_eq_add_one]

/-- The `vfan` validity on the rotated list, by cases on its first two vertices. -/
theorem vfan_core (C : Ctx) (x0 x1 : Nat) (xs : List Nat) (g : Nat → Nat → Nat → Bool)
    (hg : ∀ a b c, g a b c = decide (0 < det3Lo C a b c)) :
    let l := x0 :: x1 :: xs
    (((List.range l.length).all fun i => decide (i < 2) || decide (0 < det3Lo C (at' l 0) (at' l 1) (at' l i))) &&
      ((List.range l.length).all fun i => decide (i < 2) || decide (l.length ≤ i + 1) ||
        decide (0 < det3Lo C (at' l 0) (at' l i) (at' l (i + 1))))) =
    ((xs.all fun x => g x0 x1 x) && (List.zipWith (fun x y => g x0 x y) (x1 :: xs) xs).all id) := by
  intro l
  have hl : l.length = xs.length + 2 := by simp [l]
  have h0 : at' l 0 = x0 := by simp [l, at']
  have h1 : at' l 1 = x1 := by simp [l, at', Nat.mod_eq_of_lt (show 1 < xs.length + 2 by omega)]
  have hj : ∀ j < xs.length, at' l (j + 2) = xs.getD j 0 := by
    intro j hj
    simp only [l, at', List.length_cons, Nat.mod_eq_of_lt (show j + 2 < xs.length + 1 + 1 by omega), List.getD_cons_succ]
  rw [hl, all_range_add2, all_range_add2]
  have p1 : ((List.range xs.length).all fun j => decide (j + 2 < 2) ||
      decide (0 < det3Lo C (at' l 0) (at' l 1) (at' l (j + 2)))) = xs.all fun x => g x0 x1 x := by
    rw [← all_range_getD xs (fun x => g x0 x1 x) 0]
    apply all_range_congr
    intro j hjn
    have hn : ¬ (j + 2 < 2) := by omega
    rw [h0, h1, hj j hjn, hg]; simp [hn]
  have p2 : ((List.range xs.length).all fun j => decide (j + 2 < 2) || decide (xs.length + 2 ≤ j + 2 + 1) ||
      decide (0 < det3Lo C (at' l 0) (at' l (j + 2)) (at' l (j + 2 + 1)))) =
      (List.zipWith (fun x y => g x0 x y) xs xs.tail).all id := by
    rw [← all_range_pairs xs (fun x y => g x0 x y) 0]
    apply all_range_congr
    intro j hjn
    have hn : ¬ (j + 2 < 2) := by omega
    by_cases hlast : xs.length ≤ j + 1
    · have : xs.length + 2 ≤ j + 2 + 1 := by omega
      simp [hlast, this]
    · have hj1 := hj (j + 1) (by omega)
      rw [h0, hj j hjn, show j + 2 + 1 = (j + 1) + 2 by omega, hj1, hg]
      have : ¬ (xs.length + 2 ≤ j + 1 + 2) := by omega
      simp [hlast, this, hn]
  simp only [show decide ((0 : Nat) < 2) = true from rfl, show decide ((1 : Nat) < 2) = true from rfl, Bool.true_or,
    Bool.true_and]
  rw [p1, p2]
  cases xs with
  | nil => simp
  | cons y ys =>
    simp only [List.zipWith_cons_cons, List.all_cons, List.tail_cons, id]
    cases hx : g x0 x1 y <;> simp [hx]

theorem zipWith_congr_mem {α β γ : Type} (f g : α → β → γ) (l1 : List α) (l2 : List β)
    (h : ∀ a ∈ l1, ∀ b ∈ l2, f a b = g a b) : List.zipWith f l1 l2 = List.zipWith g l1 l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      simp only [List.zipWith_cons_cons]
      rw [h x List.mem_cons_self y List.mem_cons_self,
        ih ys (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]

theorem zipWith_map2 {α β γ δ ε : Type} (f : γ → δ → ε) (g : α → γ) (h : β → δ) (l1 : List α) (l2 : List β) :
    List.zipWith f (l1.map g) (l2.map h) = List.zipWith (fun a b => f (g a) (h b)) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons x xs ih => cases l2 with
    | nil => rfl
    | cons y ys => simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem all_congr_mem {α : Type} (f g : α → Bool) (l : List α) (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun H a ha => h a ha ▸ H a ha, fun H a ha => (h a ha).symm ▸ H a ha⟩

theorem mem_rotL {α : Type} (s : Nat) (l : List α) (x : α) (h : x ∈ rotL s l) : x ∈ l := by
  simp only [rotL, List.mem_append] at h
  rcases h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

include hF in
theorem vfanOKV_eq (piece : List Nat) (hp : ∀ g ∈ piece, g < F.body.size) (r : Nat) :
    vfanOKV F (piece.map (vdOf (envOf F lo hi))) r = vfanOK (mkCtx F lo hi) piece r := by
  have hlen : (rotL r piece).length = piece.length := rotL_length r piece
  have hvalid : ∀ g ∈ rotL r piece, g < F.body.size := fun g hg => hp g (mem_rotL r piece g hg)
  simp only [vfanOKV, vfanOK, rotL_map]
  have hrot : List.drop r piece ++ List.take r piece = rotL r piece := rfl
  rw [hrot]
  show (match (rotL r piece).map (vdOf (envOf F lo hi)) with
    | a :: b :: rest => (rest.all fun x => pos (det3V F a b x).lo) &&
        (List.zipWith (fun x y => pos (det3V F a x y).lo) (b :: rest) rest).all id
    | _ => true) = _
  rw [← hlen]
  generalize hL : rotL r piece = L at hvalid ⊢
  match L, hvalid with
  | [], _ => rfl
  | [x0], _ => rfl
  | x0 :: x1 :: xs, hv =>
    have hg : ∀ a ∈ x0 :: x1 :: xs, ∀ b ∈ x0 :: x1 :: xs, ∀ c ∈ x0 :: x1 :: xs,
        pos (det3V F (vdOf (envOf F lo hi) a) (vdOf (envOf F lo hi) b) (vdOf (envOf F lo hi) c)).lo =
          decide (0 < det3Lo (mkCtx F lo hi) a b c) := by
      intro a ha b hb c hc
      rw [pos_eq, det3V_eq F hF lo hi a b c (hv a ha) (hv b hb) (hv c hc)]; rfl
    rw [vfan_core (mkCtx F lo hi) x0 x1 xs (fun a b c => decide (0 < det3Lo (mkCtx F lo hi) a b c)) (fun _ _ _ => rfl)]
    simp only [List.map_cons, List.all_map, List.zipWith_map, Function.comp_def]
    congr 1
    · apply all_congr_mem
      intro x hx
      exact hg x0 List.mem_cons_self x1 (List.mem_cons_of_mem _ List.mem_cons_self) x
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
    · have e : (vdOf (envOf F lo hi) x1 :: List.map (vdOf (envOf F lo hi)) xs) =
          (x1 :: xs).map (vdOf (envOf F lo hi)) := rfl
      rw [e, zipWith_map2]
      rw [zipWith_congr_mem _ (fun a b => decide (0 < det3Lo (mkCtx F lo hi) x0 a b)) (x1 :: xs) xs]
      intro a ha b hb
      exact hg x0 List.mem_cons_self a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))

theorem take_rotL_at (l : List Nat) (s k : Nat) (hs : s < l.length) (hk : k ≤ l.length) :
    (rotL s l).take k = (List.range k).map fun j => at' l (s + j) := by
  apply List.ext_getElem
  · simp [rotL_length]; omega
  · intro j h1 h2
    have hj : j < k := by simpa using h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [rotL_getElem _ _ hs _ (by omega), at'_eq _ _ (by omega)]

theorem withAt_eq {α β : Type} [Inhabited α] (l : List α) (i : Nat) (k : α → β) (h : i < l.length) :
    withAt l i k = k l[i] := by
  simp only [withAt, Nat.mod_eq_of_lt h, rotL]
  rw [List.drop_eq_getElem_cons h]
  rfl

theorem at'_mem (l : List Nat) (j : Nat) (h : 0 < l.length) : at' l j ∈ l := by
  rw [at'_eq _ _ h]; exact List.getElem_mem _

theorem and_false_left (a b : Bool) (h : a = false) : (a && b) = false := by simp [h]

include hF in
theorem chordOKV_eq (maxsmall : Nat) (t : CT) : ∀ piece : List Nat, (∀ g ∈ piece, g < F.body.size) →
    chordOKV F maxsmall t (piece.map (vdOf (envOf F lo hi))) = chordOK (mkCtx F lo hi) maxsmall t piece := by
  induction t with
  | small => intro piece _; simp [chordOKV, chordOK]
  | vfan r => intro piece hp; simp only [chordOKV, chordOK, List.length_map, vfanOKV_eq F hF lo hi piece hp r]
  | cut s t L R ihL ihR =>
    intro piece hp
    simp only [chordOKV, chordOK, List.length_map]
    by_cases hD : (decide (s < piece.length) && decide (t < piece.length) &&
        decide (2 ≤ (t + piece.length - s) % piece.length) &&
        decide ((t + piece.length - s) % piece.length + 2 ≤ piece.length)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
      obtain ⟨⟨⟨hs, ht⟩, hd2⟩, hdn⟩ := hD
      have hD' : (decide (s < piece.length) && decide (t < piece.length) &&
          decide (2 ≤ (t + piece.length - s) % piece.length) &&
          decide ((t + piece.length - s) % piece.length + 2 ≤ piece.length)) = true := by simp [hs, ht, hd2, hdn]
      simp only [hD', Bool.true_and]
      rw [withAt_eq _ _ _ (by simpa using hs), withAt_eq _ _ _ (by simpa using ht)]
      simp only [List.getElem_map]
      have hps : at' piece s = piece[s] := by simp [at', Nat.mod_eq_of_lt hs, hs]
      have hpt : at' piece t = piece[t] := by simp [at', Nat.mod_eq_of_lt ht, ht]
      rw [hps, hpt]
      have vs := hp _ (List.getElem_mem hs)
      have vt := hp _ (List.getElem_mem ht)
      set_option maxRecDepth 2000 in
      congr 1
      congr 1
      congr 1
      congr 1
      · rw [pos_eq, diffV_eq F hF lo hi _ _ vs vt, pairMoveV_eq F hF lo hi _ _ vs vt]
      · rw [rotL_map, ← List.map_take, ← List.map_drop, List.all_map,
          take_rotL_at piece s _ hs (by omega), ← List.map_drop, List.all_map, all_range_skip0]
        apply all_congr_mem
        intro k _
        have hv := hp _ (at'_mem piece (s + k) (by omega))
        simp only [Function.comp_def]
        rw [ile_eq, det3V_eq F hF lo hi _ _ _ vs vt hv]; rfl
      · rw [rotL_map, ← List.map_take, ← List.map_drop, List.all_map,
          take_rotL_at piece t _ ht (by omega), ← List.map_drop, List.all_map, all_range_skip0]
        apply all_congr_mem
        intro k _
        have hv := hp _ (at'_mem piece (t + k) (by omega))
        simp only [Function.comp_def]
        rw [nonneg_eq, det3V_eq F hF lo hi _ _ _ vs vt hv]; rfl
      · rw [rotL_map, ← List.map_take, take_rotL_at piece s _ hs (by omega)]
        exact ihL _ (fun g hg => by
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
          exact hp _ (at'_mem piece (s + k) (by omega)))
      · rw [rotL_map, ← List.map_take, take_rotL_at piece t _ ht (by omega)]
        exact ihR _ (fun g hg => by
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
          exact hp _ (at'_mem piece (t + k) (by omega)))
    · simp only [Bool.not_eq_true] at hD
      simp [hD]

end vd

end WormK3
