import Jacobian.AnalyticJacobian.EvalJacobianClassOps

/-!
# Integer-scaling on the vec slot of `evalJacobianClass`

Closes the vec-slot integer-action matrix on `evalJacobianClass`,
using the underlying `evalLinearMap` linearity. Full ℂ-action is
deferred until the analytic Jacobian carries a ℂ-Module structure.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

theorem evalLinearMap_vec_nsmul (x : X) (n : ℕ) (v : E) :
    evalLinearMap (X := X) x (n • v) = n • evalLinearMap (X := X) x v := by
  ext η
  exact evalLinearMap_nsmul_vec x n v η

theorem evalLinearMap_vec_zsmul (x : X) (n : ℤ) (v : E) :
    evalLinearMap (X := X) x (n • v) = n • evalLinearMap (X := X) x v := by
  ext η
  exact evalLinearMap_zsmul_vec x n v η

theorem evalJacobianClass_nsmul_vec (x : X) (n : ℕ) (v : E) :
    evalJacobianClass (E := E) (X := X) x (n • v) =
      n • evalJacobianClass (E := E) (X := X) x v := by
  rw [evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_nsmul, mk_nsmul]

theorem evalJacobianClass_zsmul_vec (x : X) (n : ℤ) (v : E) :
    evalJacobianClass (E := E) (X := X) x (n • v) =
      n • evalJacobianClass (E := E) (X := X) x v := by
  rw [evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_zsmul, mk_zsmul]

end JacobianChallenge.AnalyticJacobian
