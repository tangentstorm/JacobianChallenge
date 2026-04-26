import Jacobian.Periods.ChartedFormLinearMap

/-!
# Simp lemmas for `chartedFormLinearMap`

Mirrors `ChartedFormPullbackLinearMapSimp.lean` at the corrected
layer. Named `@[simp]` lemmas exposing `LinearMap`-derived linearity
of `chartedFormLinearMap` (zero, neg, add, sub).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormLinearMap` of the zero form is zero. -/
@[simp] theorem chartedFormLinearMap_zero
    (c : OpenPartialHomeomorph X E) :
    chartedFormLinearMap c (0 : HolomorphicOneForm E X) = 0 :=
  LinearMap.map_zero (chartedFormLinearMap c)

/-- `chartedFormLinearMap` distributes over negation. -/
@[simp] theorem chartedFormLinearMap_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormLinearMap c (-ω) = -chartedFormLinearMap c ω :=
  LinearMap.map_neg (chartedFormLinearMap c) ω

/-- `chartedFormLinearMap` distributes over addition. -/
@[simp] theorem chartedFormLinearMap_add
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormLinearMap c (ω + η) =
      chartedFormLinearMap c ω + chartedFormLinearMap c η :=
  LinearMap.map_add (chartedFormLinearMap c) ω η

/-- `chartedFormLinearMap` distributes over subtraction. -/
@[simp] theorem chartedFormLinearMap_sub
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormLinearMap c (ω - η) =
      chartedFormLinearMap c ω - chartedFormLinearMap c η :=
  LinearMap.map_sub (chartedFormLinearMap c) ω η

end JacobianChallenge.Periods
