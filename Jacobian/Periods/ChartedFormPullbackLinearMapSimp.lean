import Jacobian.Periods.ChartedFormPullbackLinearMap

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormPullbackLinearMap` of the zero form is zero. -/
@[simp] theorem chartedFormPullbackLinearMap_zero
    (c : OpenPartialHomeomorph X E) :
    chartedFormPullbackLinearMap c (0 : HolomorphicOneForm E X) = 0 :=
  LinearMap.map_zero (chartedFormPullbackLinearMap c)

/-- `chartedFormPullbackLinearMap` distributes over negation. -/
@[simp] theorem chartedFormPullbackLinearMap_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormPullbackLinearMap c (-ω) = -chartedFormPullbackLinearMap c ω :=
  LinearMap.map_neg (chartedFormPullbackLinearMap c) ω

/-- `chartedFormPullbackLinearMap` distributes over addition. -/
@[simp] theorem chartedFormPullbackLinearMap_add
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormPullbackLinearMap c (ω + η) =
      chartedFormPullbackLinearMap c ω + chartedFormPullbackLinearMap c η :=
  LinearMap.map_add (chartedFormPullbackLinearMap c) ω η

/-- `chartedFormPullbackLinearMap` distributes over subtraction. -/
@[simp] theorem chartedFormPullbackLinearMap_sub
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormPullbackLinearMap c (ω - η) =
      chartedFormPullbackLinearMap c ω - chartedFormPullbackLinearMap c η :=
  LinearMap.map_sub (chartedFormPullbackLinearMap c) ω η

end JacobianChallenge.Periods
