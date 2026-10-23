import WormCore.Family

/-!
# K walker (core Lean only)

`walkG leafT`: the checker's `unitWalk`, with the leaf test as a parameter. The kernel-only proof runs it with the
kernel-form leaf test (`leafOKRK`); `walkG_leafOKR` says that with `leafOKR` it is `unitWalk`, so the cover lemmas of the native
chain apply once the leaf tests are proved equal.
-/

namespace WormCore.K

open WormCore

/-- The unit walk with leaf test `leafT` (called with the refinement depth). -/
def walkG (leafT : Nat → Array Int → Array Int → Rec → Bool) (rdepth : Nat) :
    Nat → List Char → List (Array Int × Array Int) → List Rec → Option (List Rec)
  | 0, _, _, _ => none
  | _ + 1, [], [], recs => some recs
  | fuel + 1, c :: cs, (lo, hi) :: st, recs =>
    if c = 'L' ∨ c = 'K' then
      match recs with
      | r :: rs => if leafT rdepth lo hi r then walkG leafT rdepth fuel cs st rs else none
      | [] => none
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => walkG leafT rdepth fuel cs (l :: u :: st) recs
        | none => none
      | none => none
  | _, _, _, _ => none

/-- With `leafOKR` the walk is `unitWalk`. -/
theorem walkG_leafOKR (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) :
    ∀ fuel cs st recs, walkG (leafOKR F maxsmall tauHi) rdepth fuel cs st recs =
      unitWalk F maxsmall tauHi rdepth fuel cs st recs := by
  intro fuel
  induction fuel with
  | zero => intro cs st recs; rfl
  | succ n ih =>
    intro cs st recs
    match cs, st with
    | [], [] => rfl
    | [], _ :: _ => rfl
    | _ :: _, [] => rfl
    | c :: cs, (lo, hi) :: st =>
      simp only [walkG, unitWalk]
      by_cases hc : c = 'L' ∨ c = 'K'
      · simp only [hc, ↓reduceIte]
        cases recs with
        | nil => rfl
        | cons r rs =>
          simp only
          cases leafOKR F maxsmall tauHi rdepth lo hi r <;> simp [ih]
      · simp only [hc, ↓reduceIte]
        cases codeDim c with
        | none => rfl
        | some k =>
          simp only
          cases halves lo hi k with
          | none => rfl
          | some p =>
            obtain ⟨l, u⟩ := p
            exact ih _ _ _

/-- The top tree of a unit above its pieces: split codes as in `unitWalk`, and `'P'` for the root of a piece.
Returns the piece boxes in walk order (reversed onto `acc`), or `none` on malformed data. -/
def topWalk : Nat → List Char → List (Array Int × Array Int) → List (Array Int × Array Int) →
    Option (List (Array Int × Array Int))
  | 0, _, _, _ => none
  | _ + 1, [], [], acc => some acc
  | fuel + 1, c :: cs, (lo, hi) :: st, acc =>
    if c = 'P' then topWalk fuel cs st ((lo, hi) :: acc)
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => topWalk fuel cs (l :: u :: st) acc
        | none => none
      | none => none
  | _, _, _, _ => none

/-- The accumulator only grows: every box in `acc` is in the result. -/
theorem topWalk_acc_sub : ∀ (fuel : Nat) (cs : List Char) (st acc out : List (Array Int × Array Int)),
    topWalk fuel cs st acc = some out → ∀ b ∈ acc, b ∈ out := by
  intro fuel
  induction fuel with
  | zero => intro cs st acc out h; simp [topWalk] at h
  | succ n ih =>
    intro cs st acc out h b hb
    match cs, st, h with
    | [], [], h => simp [topWalk] at h; exact h ▸ hb
    | c :: cs, (lo, hi) :: st, h =>
      simp only [topWalk] at h
      by_cases hc : c = 'P'
      · simp only [hc, ↓reduceIte] at h
        exact ih cs st ((lo, hi) :: acc) out h b (List.mem_cons_of_mem _ hb)
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
            exact ih cs (l :: u :: st) acc out h b hb

/-- A walk that used up all its records. -/
def walkDone : Option (List Rec) → Bool
  | some [] => true
  | _ => false

theorem eq_of_walkDone {o : Option (List Rec)} (h : walkDone o = true) : o = some [] := by
  match o, h with
  | some [], _ => rfl

end WormCore.K
