import Jacobian.AnalyticJacobian.EvalJacobianClass

/-!
# `evalJacobianClass`-self subtraction is zero

Trivial sanity lemma: subtracting an `evalJacobianClass` from
itself in `AnalyticJacobianGroup` gives `0`.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `evalJacobianClass P v - evalJacobianClass P v = 0`. -/
theorem evalJacobianClass_self_sub_self
    (P : X) (v : E) :
    evalJacobianClass (E := E) (X := X) P v -
      evalJacobianClass P v = 0 :=
  sub_self _

end JacobianChallenge.AnalyticJacobian
