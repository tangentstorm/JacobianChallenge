import Jacobian.TraceDegree.PullbackFormsLinearMapApply
import Jacobian.TraceDegree.PullbackFormsLinearMapSimp
import Jacobian.TraceDegree.PullbackFormsLinearMapSmul
import Jacobian.TraceDegree.PullbackFunAddSubApply

/-!
# Pointwise `_apply` forms of the LinearMap-level linearity simp lemmas

The bundled `pullbackFormsLinearMap f` is definitionally equal to the
unbundled `pullbackFormsFun f` at every point (via the rfl-bridge
`pullbackFormsLinearMap_apply_at`), so its linearity behaviour reduces
directly to the unbundled apply-form lemmas. These five facade lemmas
expose that fact at the LinearMap level for downstream callers that
work with the bundled form.

Parallels `Jacobian/Periods/ChartedFormPullbackLinearMapApplyLinear.lean`.
Out of scope of any in-flight Aristotle job (`82687eb7` targets
unbundled `_apply` forms in `PullbackFunSimpApply.lean`).
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Pointwise apply form: bundled pullback of the zero form is zero. -/
@[simp] theorem pullbackFormsLinearMap_zero_apply
    (f : X → Y) (x : X) :
    pullbackFormsLinearMap f (0 : HolomorphicOneForm E Y) x = 0 := by
  rw [pullbackFormsLinearMap_zero]; rfl

/-- Pointwise apply form: bundled pullback of `-η` negates pointwise. -/
@[simp] theorem pullbackFormsLinearMap_neg_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (-η) x = - pullbackFormsLinearMap f η x := by
  rw [pullbackFormsLinearMap_neg]; rfl

/-- Pointwise apply form: bundled pullback distributes over addition. -/
@[simp] theorem pullbackFormsLinearMap_add_apply
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (η + ζ) x =
      pullbackFormsLinearMap f η x + pullbackFormsLinearMap f ζ x := by
  rw [pullbackFormsLinearMap_add]; rfl

/-- Pointwise apply form: bundled pullback distributes over subtraction. -/
@[simp] theorem pullbackFormsLinearMap_sub_apply
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (η - ζ) x =
      pullbackFormsLinearMap f η x - pullbackFormsLinearMap f ζ x := by
  rw [pullbackFormsLinearMap_sub]; rfl

/-- Pointwise apply form: bundled pullback is ℂ-linear pointwise. -/
@[simp] theorem pullbackFormsLinearMap_smul_apply
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (k • η) x = k • pullbackFormsLinearMap f η x := by
  rw [pullbackFormsLinearMap_smul]; rfl

end JacobianChallenge.TraceDegree
