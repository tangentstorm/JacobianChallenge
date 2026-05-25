import Jacobian.HolomorphicForms.Ext
import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Extensionality through `evalLinearMap`

Repackages the `ext_toFun_apply_iff` extensionality criterion in
terms of the bundled `evalLinearMap`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Extensionality through `evalLinearMap`. -/
theorem ext_evalLinearMap_iff {η ζ : HolomorphicOneForm E X} :
    η = ζ ↔ ∀ x v, evalLinearMap x v η = evalLinearMap x v ζ := by
  rw [ext_toFun_apply_iff]; rfl

/-- Pointwise extensionality through `evalLinearMap`. -/
theorem ext_evalLinearMap {η ζ : HolomorphicOneForm E X}
    (h : ∀ x v, evalLinearMap x v η = evalLinearMap x v ζ) : η = ζ :=
  ext_evalLinearMap_iff.mpr h

/-- A form is zero iff every `evalLinearMap` value is zero. -/
theorem eq_zero_iff_evalLinearMap_eq_zero (η : HolomorphicOneForm E X) :
    η = 0 ↔ ∀ x v, evalLinearMap x v η = 0 := by
  rw [ext_evalLinearMap_iff]
  exact forall_congr' (fun x => forall_congr' (fun v => by simp))

/--
Sufficient witness condition: a non-vanishing `evalLinearMap`
proves the form is non-zero.
-/
theorem ne_zero_of_evalLinearMap_ne_zero (η : HolomorphicOneForm E X)
    (x : X) (v : E) (h : evalLinearMap x v η ≠ 0) : η ≠ 0 := by
  intro hη
  apply h
  rw [hη]
  exact (evalLinearMap x v).map_zero

end JacobianChallenge.HolomorphicForms
