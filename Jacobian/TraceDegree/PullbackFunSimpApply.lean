import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunSmul

/-!
# Pointwise apply forms for `pullbackFormsFun_{zero,neg,smul}`

The function-level simp lemmas plus `Pi.*_apply` already let `simp`
derive the pointwise versions, but explicit apply-forms are useful
for direct `rw`/`exact` proofs (Aristotle prompt style) without
firing the full simp set.

Mirrors `Jacobian/TraceDegree/PullbackFunAddSubApply.lean` (which
covered `_add` and `_sub`) and the Periods-side
`ChartedFormPullbackApplyLinear`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Pointwise apply form: pullback of the zero form is the zero CLM. -/
@[simp] theorem pullbackFormsFun_zero_apply
    (f : X → Y) (x : X) :
    pullbackFormsFun f (0 : HolomorphicOneForm E Y) x = 0 := by
  rw [pullbackFormsFun_zero]; rfl

/-- Pointwise apply form: pullback of `-η` negates pointwise. -/
@[simp] theorem pullbackFormsFun_neg_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f (-η) x = - pullbackFormsFun f η x := by
  rw [pullbackFormsFun_neg]; rfl

/-- Pointwise apply form: pullback is ℂ-linear pointwise. -/
@[simp] theorem pullbackFormsFun_smul_apply
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f (k • η) x = k • pullbackFormsFun f η x := by
  rw [pullbackFormsFun_smul]; rfl

end JacobianChallenge.TraceDegree
