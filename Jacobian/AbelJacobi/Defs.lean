import Jacobian.AnalyticJacobian.NontrivialWitness

/-!
# Abel-Jacobi map (witness skeleton)

Queue F seeding. Defines a base-point-relative *witness* map:

```text
witnessAbelJacobi (basePoint : X) (P : X) (v : E) : AnalyticJacobianGroup E X
  := evalJacobianClass P v - evalJacobianClass basePoint v
```

This is **not** the full path-integral Abel-Jacobi map (which would
require multi-chart path integration plus Stokes — both deferred).
But it has the same *signature shape* and the right base-point
behaviour: at `P = basePoint`, the witness is zero. Useful as a
type-correct stand-in until the real construction lands.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Base-point-relative witness map into the analytic Jacobian
quotient. *Not* the full Abel-Jacobi map (deferred), but a
type-correct skeleton that vanishes at the base point. -/
noncomputable def witnessAbelJacobi
    (basePoint P : X) (v : E) : AnalyticJacobianGroup E X :=
  evalJacobianClass P v - evalJacobianClass basePoint v

/-- The witness map vanishes at the base point. -/
@[simp] theorem witnessAbelJacobi_self
    (basePoint : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint basePoint v = 0 := by
  unfold witnessAbelJacobi
  exact sub_self _

/-- The witness map is antisymmetric in the two endpoints. -/
theorem witnessAbelJacobi_swap
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      -witnessAbelJacobi (E := E) (X := X) P basePoint v := by
  unfold witnessAbelJacobi
  rw [neg_sub]

/-- The witness map of a point with itself collapses. -/
theorem witnessAbelJacobi_diag (basePoint : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint basePoint v = 0 :=
  witnessAbelJacobi_self basePoint v

end JacobianChallenge.AbelJacobi
