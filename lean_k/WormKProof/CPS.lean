import WormK.Fast3

/-!
# The continuation-passing helpers are the identity on values

`natK n k = k n`, `intK x k = k x`, `arrK n l k = k (l.take n)`, and the vertex-data continuations pass the vertex data
`vdOf E g` of the vertex `g`.
-/

namespace WormK3

open MoserWorm WormCore
open WormK2 (natK intK arrK Ang Tr)

theorem natK_eq {β : Type} (n : Nat) (k : Nat → β) : natK n k = k n := by
  cases n <;> rfl

theorem intK_eq {β : Type} (x : Int) (k : Int → β) : intK x k = k x := by
  cases x <;> simp [intK, natK_eq]

theorem arrK_eq {β : Type} (n : Nat) (l : List Int) (k : List Int → β) : arrK n l k = k (l.take n) := by
  induction n generalizing l k with
  | zero => cases l <;> rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x xs => simp only [arrK, intK_eq, ih, List.take_succ_cons]

/-- The vertex data of `g` in the environment `E`. -/
def vdOf (E : Env) (g : Nat) : VD :=
  match E.F.body[g]! with
  | 0 => vd0 E.F g
  | 1 => vdK E.F g 1 E.A1 E.T1
  | 2 => vdK E.F g 2 E.A2 E.T2
  | 3 => vdK E.F g 3 E.A3 E.T3
  | _ => vdK E.F g 4 E.A4 E.T4

theorem withVD_eq {β : Type} (E : Env) (g : Nat) (k : VD → β) : withVD E g k = k (vdOf E g) := by
  obtain ⟨F, A1, A2, A3, A4, T1, T2, T3, T4⟩ := E
  simp only [withVD, natK_eq, vdOf]
  generalize F.body[g]! = b
  rcases b with _ | _ | _ | _ | b <;> rfl

theorem withVDs_eq {β : Type} (E : Env) (l : List Nat) (k : List VD → β) :
    withVDs E l k = k (l.map (vdOf E)) := by
  induction l generalizing k with
  | nil => rfl
  | cons g gs ih => simp only [withVDs, withVD_eq, ih, List.map_cons]

theorem withSts_eq {β : Type} (E : Env) (sts : List (St × Int)) (k : List (List VD) → β) :
    withSts E sts k = k (sts.map fun p => p.1.verts.map (vdOf E)) := by
  induction sts generalizing k with
  | nil => rfl
  | cons p ps ih => simp only [withSts, withVDs_eq, ih, List.map_cons]

/-- The angle and translation data of body `b ≥ 1`. -/
def angOf (E : Env) (b : Nat) : Ang :=
  match b with
  | 1 => E.A1
  | 2 => E.A2
  | 3 => E.A3
  | _ => E.A4

def trOf (E : Env) (b : Nat) : Tr :=
  match b with
  | 1 => E.T1
  | 2 => E.T2
  | 3 => E.T3
  | _ => E.T4

theorem withAT_eq {β : Type} (E : Env) (b : Nat) (k : Ang → Tr → β) : withAT E b k = k (angOf E b) (trOf E b) := by
  obtain ⟨F, A1, A2, A3, A4, T1, T2, T3, T4⟩ := E
  rcases b with _ | _ | _ | _ | b <;> rfl

end WormK3
