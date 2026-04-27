import Jacobian.TraceDegree.PullbackFormsLinearMapConstDist

/-!
# Integer-scalar form-slot extras for bundled pullback along a constant map

Continues `PullbackFormsLinearMapConstDist` with the missing
`ℕ`/`ℤ`-scalar form-slot variants and a couple of small helper
identities. All collapse via the const-pullback zero identity.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over `ℕ`-scalar form mult. -/
theorem pullbackFormsLinearMap_const_nsmul_apply_vec
    (y : Y) (n : ℕ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (n • η) x v =
      n • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_const_zsmul_apply_vec
    (y : Y) (n : ℤ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (n • η) x v =
      n • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map of `-0` (form slot) is zero. -/
theorem pullbackFormsLinearMap_const_neg_zero_apply_vec
    (y : Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y)
        (-(0 : HolomorphicOneForm E Y)) x v = 0 := by
  rw [neg_zero, pullbackFormsLinearMap_const_apply_vec]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map of double-negated form (vec form). -/
theorem pullbackFormsLinearMap_const_neg_neg_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (- -η) x v =
      pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [neg_neg]

end JacobianChallenge.TraceDegree
