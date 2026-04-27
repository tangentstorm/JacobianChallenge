import Jacobian.HolomorphicForms.Defs

/-!
# Pointwise `toFun` apply lemmas for `HolomorphicOneForm`

The `ContMDiffSection` algebraic structure on `HolomorphicOneForm` is
inherited, but the pointwise `toFun` projections are not always
exposed as named simps. These convenience facade lemmas expose
`(0 : HolomorphicOneForm E X).toFun x = 0`, etc., for direct
`rw`/`exact` use without firing the full simp set.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem zero_toFun_apply (x : X) :
    (0 : HolomorphicOneForm E X).toFun x = 0 := by
  change ((0 : HolomorphicOneForm E X) : ∀ x, _) x = 0
  rw [ContMDiffSection.coe_zero]; rfl

@[simp] theorem neg_toFun_apply
    (η : HolomorphicOneForm E X) (x : X) :
    (-η).toFun x = -(η.toFun x) := by
  change ((-η : HolomorphicOneForm E X) : ∀ x, _) x = -((η : ∀ x, _) x)
  rw [ContMDiffSection.coe_neg]; rfl

@[simp] theorem add_toFun_apply
    (η ζ : HolomorphicOneForm E X) (x : X) :
    (η + ζ).toFun x = η.toFun x + ζ.toFun x := by
  change ((η + ζ : HolomorphicOneForm E X) : ∀ x, _) x =
    (η : ∀ x, _) x + (ζ : ∀ x, _) x
  rw [ContMDiffSection.coe_add]; rfl

@[simp] theorem sub_toFun_apply
    (η ζ : HolomorphicOneForm E X) (x : X) :
    (η - ζ).toFun x = η.toFun x - ζ.toFun x := by
  change ((η - ζ : HolomorphicOneForm E X) : ∀ x, _) x =
    (η : ∀ x, _) x - (ζ : ∀ x, _) x
  rw [ContMDiffSection.coe_sub]; rfl

end JacobianChallenge.HolomorphicForms
