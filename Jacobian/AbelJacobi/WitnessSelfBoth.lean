import Jacobian.AbelJacobi.Defs

/-!
# Both diagonal witness values are zero

`witnessAbelJacobi P P v = witnessAbelJacobi Q Q v` for any two
points `P` and `Q`, since both diagonal witnesses vanish.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- All diagonal witness values agree (they are all zero). -/
theorem witnessAbelJacobi_self_both
    (P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P P v =
      witnessAbelJacobi Q Q v := by
  rw [witnessAbelJacobi_self, witnessAbelJacobi_self]

end JacobianChallenge.AbelJacobi
