import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear
import Jacobian.TraceDegree.PullbackFormsLinearMapSmul

/-!
# Combined smul/neg identities for bundled `pullbackFormsLinearMap`

A handful of combined ring-rewrite identities mixing scalar
multiplication, negation, and addition on the form side.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullback f (k • -η) = -(k • pullback f η)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_neg
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (k • -η) =
      -(k • pullbackFormsLinearMap f η) := by
  rw [pullbackFormsLinearMap_smul, pullbackFormsLinearMap_neg, smul_neg]

/-- `pullback f (-(k • η)) = -(k • pullback f η)`. -/
@[simp] theorem pullbackFormsLinearMap_neg_smul
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (-(k • η)) =
      -(k • pullbackFormsLinearMap f η) := by
  rw [pullbackFormsLinearMap_neg, pullbackFormsLinearMap_smul]

/-- `pullback f (-η + ζ) = -pullback f η + pullback f ζ`. -/
@[simp] theorem pullbackFormsLinearMap_neg_add
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (-η + ζ) =
      -pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_neg]

/-- `pullback f (η + -ζ) = pullback f η - pullback f ζ`. -/
@[simp] theorem pullbackFormsLinearMap_add_neg
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + -ζ) =
      pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_neg, ← sub_eq_add_neg]

end JacobianChallenge.TraceDegree
