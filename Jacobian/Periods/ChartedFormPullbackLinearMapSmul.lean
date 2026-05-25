import Jacobian.Periods.ChartedFormPullbackLinearMap

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
`chartedFormPullbackLinearMap` distributes over scalar
multiplication.
-/
@[simp] theorem chartedFormPullbackLinearMap_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) :
    chartedFormPullbackLinearMap c (k • ω) =
      k • chartedFormPullbackLinearMap c ω :=
  (chartedFormPullbackLinearMap c).map_smul k ω

end JacobianChallenge.Periods
