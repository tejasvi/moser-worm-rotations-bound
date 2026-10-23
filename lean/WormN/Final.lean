import WormN.All
import WormSound.FinalAt

/-!
# The lower bound `0.2414` for Moser's worm problem with rotations and translations only (native track)

The certificate facts `WormN.skel_ok`, `WormN.cover` and `WormN.chunks_ok` of `cert_w2414a` (checked by
`native_decide` in the modules `WormN.*`) give `WormLowerAt (2414/10000)` through `wormLowerAt_2414_of_certificate`.
-/

namespace Worm

/-- **Theorem.** Every convex set that contains a rotated and translated copy of every unit arc has area at
least `0.2414`. -/
theorem worm_lower_2414 : WormLowerAt (2414 / 10000) :=
  WormCore.Sound.wormLowerAt_2414_of_certificate WormN.skelOf WormN.unitLists WormN.skel_ok WormN.cover
    WormN.chunks_ok

/-- **Theorem**, for the least area. -/
theorem optimalAreaM_lower_2414 : OptimalAreaLowerAt (2414 / 10000) :=
  WormCore.Sound.optimalAreaLowerAt_of worm_lower_2414

end Worm
