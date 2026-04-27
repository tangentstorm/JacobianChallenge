import Jacobian.HolomorphicForms.ToFunApplyVec

/-!
# Negation simps for `HolomorphicOneForm.toFun` at points and vectors

Convenience wrappers around `neg_toFun_apply` and
`neg_toFun_apply_vec` that explicitly compose the negation in
either order or cancel double negations.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Double-negation cancels at the toFun-apply level. -/
@[simp] theorem neg_neg_toFun_apply
    (η : HolomorphicOneForm E X) (x : X) :
    (- -η).toFun x = η.toFun x := by
  rw [neg_neg]

/-- Double-negation cancels at the vec-apply level. -/
@[simp] theorem neg_neg_toFun_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    (- -η).toFun x v = η.toFun x v := by
  rw [neg_neg]

/-- `(-η).toFun x = -η.toFun x` reversed orientation. -/
theorem toFun_neg_apply_swap
    (η : HolomorphicOneForm E X) (x : X) :
    -((-η).toFun x) = η.toFun x := by
  rw [neg_toFun_apply, neg_neg]

/-- `(-η).toFun x v = -η.toFun x v` reversed orientation. -/
theorem toFun_neg_apply_vec_swap
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    -((-η).toFun x v) = η.toFun x v := by
  rw [neg_toFun_apply_vec, neg_neg]

end JacobianChallenge.HolomorphicForms
