import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear
import Jacobian.TraceDegree.PullbackFormsLinearMapIntSmul

/-!
# Combined ℕ/ℤ-smul interplay with add/sub for bundled `pullbackFormsLinearMap`

Integer-scalar combinations of the `_add` / `_sub` distributivity
laws for the bundled pullback, for arbitrary `f`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullback f (n • (η + ζ)) = n • (pullback f η + pullback f ζ)`. -/
@[simp] theorem pullbackFormsLinearMap_nsmul_add
    (f : X → Y) (n : ℕ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • (η + ζ)) =
      n • (pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_nsmul, pullbackFormsLinearMap_add]

/-- `pullback f (n • (η - ζ)) = n • (pullback f η - pullback f ζ)` for `n : ℕ`. -/
@[simp] theorem pullbackFormsLinearMap_nsmul_sub
    (f : X → Y) (n : ℕ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • (η - ζ)) =
      n • (pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_nsmul, pullbackFormsLinearMap_sub]

/-- `pullback f (n • (η + ζ)) = n • (pullback f η + pullback f ζ)` for `n : ℤ`. -/
@[simp] theorem pullbackFormsLinearMap_zsmul_add
    (f : X → Y) (n : ℤ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • (η + ζ)) =
      n • (pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_zsmul, pullbackFormsLinearMap_add]

/-- `pullback f (n • (η - ζ)) = n • (pullback f η - pullback f ζ)` for `n : ℤ`. -/
@[simp] theorem pullbackFormsLinearMap_zsmul_sub
    (f : X → Y) (n : ℤ) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (n • (η - ζ)) =
      n • (pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ) := by
  rw [pullbackFormsLinearMap_zsmul, pullbackFormsLinearMap_sub]

end JacobianChallenge.TraceDegree
