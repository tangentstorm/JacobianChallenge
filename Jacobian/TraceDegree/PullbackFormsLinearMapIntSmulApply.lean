import Jacobian.TraceDegree.PullbackFormsLinearMapIntSmul

/-!
# At-point apply forms for bundled `pullbackFormsLinearMap` ℕ/ℤ-smul

Adds the at-point `_apply` companions for the function-level
`pullbackFormsLinearMap_{n,z}smul` lemmas, and a couple of useful
helper variants.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- At-point: bundled pullback `ℕ`-smul. -/
theorem pullbackFormsLinearMap_nsmul_apply
    (f : X → Y) (n : ℕ) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (n • η) x =
      n • pullbackFormsLinearMap f η x := by
  rw [pullbackFormsLinearMap_nsmul]; rfl

/-- At-point: bundled pullback `ℤ`-smul. -/
theorem pullbackFormsLinearMap_zsmul_apply
    (f : X → Y) (n : ℤ) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (n • η) x =
      n • pullbackFormsLinearMap f η x := by
  rw [pullbackFormsLinearMap_zsmul]; rfl

/-- Bundled pullback of `(0 : ℕ) • η` is the zero map. -/
theorem pullbackFormsLinearMap_nsmul_zero
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((0 : ℕ) • η) = 0 := by
  rw [zero_nsmul, map_zero]

/-- Bundled pullback of `(0 : ℤ) • η` is the zero map. -/
theorem pullbackFormsLinearMap_zsmul_zero
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((0 : ℤ) • η) = 0 := by
  rw [zero_zsmul, map_zero]

end JacobianChallenge.TraceDegree
