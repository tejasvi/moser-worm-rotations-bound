import WormKProof.Prims

/-!
# Sums of intervals

`isum` adds end points exactly, so it is the pair of end-point sums; terms equal to `pt 0` can be dropped, the order
of a double sum can be changed, and the products with the point `0` vanish.
-/

namespace WormK3

open MoserWorm WormCore

theorem foldl_add_eq (l : List DIval) (acc : DIval) :
    l.foldl DIval.add acc = ⟨acc.lo + (l.map (·.lo)).sum, acc.hi + (l.map (·.hi)).sum⟩ := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, DIval.add, List.map_cons, List.sum_cons]; congr 1 <;> omega

theorem isum_eq (l : List DIval) : isum l = ⟨(l.map (·.lo)).sum, (l.map (·.hi)).sum⟩ := by
  simp [isum, foldl_add_eq, DIval.pt]

theorem DIval.ext' {a b : DIval} (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) : a = b := by
  cases a; cases b; simp_all

theorem isum_nil : isum [] = DIval.pt 0 := rfl

theorem isum_cons (x : DIval) (l : List DIval) : isum (x :: l) = x.add (isum l) := by
  simp only [isum_eq, List.map_cons, List.sum_cons, DIval.add]

theorem isum_append (l m : List DIval) : isum (l ++ m) = (isum l).add (isum m) := by
  simp only [isum_eq, List.map_append, List.sum_append, DIval.add]

theorem mul_pt0 (a : DIval) : a.mul (DIval.pt 0) = DIval.pt 0 := by
  simp [DIval.mul, DIval.pt]

theorem pt0_mul (a : DIval) : (DIval.pt 0).mul a = DIval.pt 0 := by
  simp [DIval.mul, DIval.pt]

theorem half_pt0 : (DIval.pt 0).half = DIval.pt 0 := by decide

theorem add_pt0 (a : DIval) : a.add (DIval.pt 0) = a := by simp [DIval.add, DIval.pt]
theorem pt0_add (a : DIval) : (DIval.pt 0).add a = a := by simp [DIval.add, DIval.pt]
theorem sub_pt0 (a : DIval) : a.sub (DIval.pt 0) = a := by simp [DIval.sub, DIval.pt]
theorem abs_pt0 : (DIval.pt 0).abs = DIval.pt 0 := by decide

/-- Dropping terms equal to `pt 0`. -/
theorem isum_filter {α : Type} (l : List α) (p : α → Bool) (f : α → DIval)
    (h : ∀ x ∈ l, p x = false → f x = DIval.pt 0) : isum ((l.filter p).map f) = isum (l.map f) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · simp only [List.filter_cons, hp, ite_true, List.map_cons, isum_cons, ih']
    · have hx := h x (List.mem_cons_self) (by simpa using hp)
      rw [List.filter_cons_of_neg hp, List.map_cons, isum_cons, hx, pt0_add, ih']

theorem isum_congr {α : Type} (l : List α) (f g : α → DIval) (h : ∀ x ∈ l, f x = g x) :
    isum (l.map f) = isum (l.map g) := by
  rw [List.map_congr_left h]

theorem isum_flatMap {α β : Type} (l : List α) (m : α → List β) (f : β → DIval) :
    isum ((l.flatMap m).map f) = isum (l.map fun a => isum ((m a).map f)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, isum_append, ih, List.map_cons, isum_cons]

theorem isum_zero {α : Type} (l : List α) (f : α → DIval) (h : ∀ x ∈ l, f x = DIval.pt 0) :
    isum (l.map f) = DIval.pt 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, isum_cons, h x List.mem_cons_self, pt0_add]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

end WormK3
