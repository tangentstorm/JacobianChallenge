import Jacobian.Periods.ChartedFormLinearMap

/-!
# Scalar-multiplication simp for `chartedFormLinearMap`

Mirrors `ChartedFormPullbackLinearMapSmul.lean` at the corrected layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormLinearMap` distributes over scalar multiplication. -/
@[simp] theorem chartedFormLinearMap_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) :
    chartedFormLinearMap c (k • ω) =
      k • chartedFormLinearMap c ω :=
  (chartedFormLinearMap c).map_smul k ω

end JacobianChallenge.Periods
