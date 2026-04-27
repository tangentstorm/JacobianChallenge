import Jacobian.HolomorphicForms.EvalLinearMapApi

/-!
# Negation simps for `evalLinearMap`

Double-negation cancellation and reversed-orientation negation
analogues to `ToFunNeg`, but at the bundled `evalLinearMap` level.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Double-negation cancellation on the form slot. -/
theorem evalLinearMap_neg_neg_form
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (- -η) = evalLinearMap x v η := by
  rw [neg_neg]

/-- Double-negation cancellation on the result. -/
theorem evalLinearMap_neg_neg_result
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    -(-evalLinearMap x v η) = evalLinearMap x v η := by
  rw [neg_neg]

/-- Negation symmetry on the form slot. -/
theorem evalLinearMap_neg_form_eq_neg
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (-η) = -(evalLinearMap x v η) :=
  evalLinearMap_neg x v η

/-- Reversed-orientation negation: `-(evalLinearMap x v (-η)) = evalLinearMap x v η`. -/
theorem evalLinearMap_neg_form_swap
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    -(evalLinearMap x v (-η)) = evalLinearMap x v η := by
  rw [evalLinearMap_neg, neg_neg]

end JacobianChallenge.HolomorphicForms
