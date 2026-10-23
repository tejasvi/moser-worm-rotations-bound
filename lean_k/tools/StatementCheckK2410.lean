import WormKD.Final
import Worm13a.StatementAt

open Lean Elab Command Term

/-! Check of the kernel-only worm bound at τ = 0.2410. The two finals must have exactly the types
`Worm.WormLowerAt (2410 / 10000)` and `Worm.OptimalAreaLowerAt (2410 / 10000)` of the statement file
`Worm13a/StatementAt.lean`, elaborated here (`Expr ==`), and depend only on the three standard axioms. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let ty (n : Name) : Expr := (env.find? n).get!.type
  let (a, b) ← liftTermElabM do
    let a ← elabTerm (← `(Worm.WormLowerAt (2410 / 10000))) none
    let b ← elabTerm (← `(Worm.OptimalAreaLowerAt (2410 / 10000))) none
    synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars a, ← instantiateMVars b)
  logInfo m!"WormKD.worm_lower_K has type Worm.WormLowerAt (2410 / 10000) (Expr ==): {ty ``WormKD.worm_lower_K == a}"
  logInfo m!"WormKD.optimalAreaM_lower_K has type Worm.OptimalAreaLowerAt (2410 / 10000) (Expr ==): {ty ``WormKD.optimalAreaM_lower_K == b}"
  logInfo m!"no metavariables in the elaborated statements: {!a.hasMVar && !b.hasMVar}"

example : Worm.WormLowerAt (2410 / 10000) := WormKD.worm_lower_K
example : Worm.OptimalAreaLowerAt (2410 / 10000) := WormKD.optimalAreaM_lower_K

#print Worm.WormLowerAt
#print Worm.OptimalAreaLowerAt
#print axioms WormKD.worm_lower_K
#print axioms WormKD.optimalAreaM_lower_K
