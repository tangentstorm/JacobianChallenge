import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear
import Jacobian.TraceDegree.PullbackFormsLinearMapSmul

/-!
# Combined smul/add/sub identities for bundled `pullbackFormsLinearMap`

Ring-rewrite combinations of scalar multiplication with addition or
subtraction inside the form argument of the bundled pullback.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullback f (k • (η + ζ)) = k • (pullback f η + pullback f ζ)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_add
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (k • (η + ζ)) =
      k • (pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_smul, pullbackFormsLinearMap_add]

/-- `pullback f (k • (η - ζ)) = k • (pullback f η - pullback f ζ)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_sub
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (k • (η - ζ)) =
      k • (pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_smul, pullbackFormsLinearMap_sub]

/-- `pullback f ((k • η) + ζ) = k • pullback f η + pullback f ζ`. -/
@[simp] theorem pullbackFormsLinearMap_smul_left_add
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((k • η) + ζ) =
      k • pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_smul]

/-- `pullback f (η - k • ζ) = pullback f η - k • pullback f ζ`. -/
@[simp] theorem pullbackFormsLinearMap_sub_smul_right
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - k • ζ) =
      pullbackFormsLinearMap f η - k • pullbackFormsLinearMap f ζ := by
  rw [pullbackFormsLinearMap_sub, pullbackFormsLinearMap_smul]

end JacobianChallenge.TraceDegree
