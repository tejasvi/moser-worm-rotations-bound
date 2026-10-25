import WormSound.AssemblyAt
import WormSound.RootAt

/-!
# The instance `τ = 2414/10000` of the assembly, given the certificate facts

`wormLowerAt_2414_of_certificate`: the statement `WormLowerAt (2414/10000)` from the three certificate facts of
`cert_w2414a`
(supplied by `native_decide` in the proof with compiled code, which is not part of this directory).
-/

noncomputable section

namespace WormCore.Sound

open MoserWorm hiding cross shoelace

/-- The checker's `τ` (`tauHiW · 2⁻⁵⁶`) is at least `2414/10000`. -/
lemma tau_2414_le : (2414 / 10000 : ℝ) ≤ (tauHiW : ℝ) / 2 ^ dfxS := by
  norm_num [tauHiW, dfxS]

theorem wormLowerAt_2414_of_certificate (skelOf : ℕ → String) (unitLists : List (List (ℕ × ℕ)))
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcover : allUnitsOf skelOf = unitLists.flatten)
    (hchunks : ∀ L ∈ unitLists, ∃ txt, chunkCheck famW rootW maxsmallW tauHiW rdepthW skelOf txt = some L) :
    Worm.WormLowerAt (2414 / 10000) :=
  wormLowerAt_of_certificate (2414 / 10000) (by norm_num) tau_2414_le root_box_at skelOf unitLists hskel hcover
    hchunks

end WormCore.Sound
