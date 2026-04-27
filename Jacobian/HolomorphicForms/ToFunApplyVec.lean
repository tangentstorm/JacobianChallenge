import Jacobian.HolomorphicForms.ToFunApply

/-!
# Vec-apply forms of the pointwise `toFun` simps + `smul`

Companion to `ToFunApply`: vector-application forms (i.e. evaluating
the resulting `E →L[ℂ] ℂ` at a tangent vector) plus the missing
`smul` case.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem smul_toFun_apply
    (k : ℂ) (η : HolomorphicOneForm E X) (x : X) :
    (k • η).toFun x = k • η.toFun x := by
  change ((k • η : HolomorphicOneForm E X) : ∀ x, _) x =
    k • (η : ∀ x, _) x
  rw [ContMDiffSection.coe_smul]; rfl

@[simp] theorem zero_toFun_apply_vec (x : X) (v : E) :
    (0 : HolomorphicOneForm E X).toFun x v = 0 := by
  rw [zero_toFun_apply]; rfl

@[simp] theorem neg_toFun_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    (-η).toFun x v = -(η.toFun x v) := by
  rw [neg_toFun_apply]; rfl

@[simp] theorem add_toFun_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    (η + ζ).toFun x v = η.toFun x v + ζ.toFun x v := by
  rw [add_toFun_apply]; rfl

end JacobianChallenge.HolomorphicForms
