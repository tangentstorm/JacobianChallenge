import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Underlying function of the pullback of a holomorphic 1-form

Defines `pullbackFormsFun f η`, the underlying function of the pullback
of a holomorphic 1-form `η` along a smooth map `f`, via the chain-rule
formula `(f^*η)_x = η_{f x} ∘ mfderiv f x`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/--
Underlying function of the pullback of a holomorphic 1-form
along a smooth map, via the chain-rule formula
`(f^*η)_x = η_{f x} ∘ mfderiv f x`. The smoothness of this function
(i.e., upgrading the result to `HolomorphicOneForm E X`) is a
separate follow-up.
-/
noncomputable def pullbackFormsFun
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    X → E →L[ℂ] ℂ :=
  fun x =>
    (η.toFun (f x)).comp
      (mfderiv (modelWithCornersSelf ℂ E)
               (modelWithCornersSelf ℂ E) f x)

/-- The pullback of the zero form is the zero function. -/
@[simp] theorem pullbackFormsFun_zero
    (f : X → Y) :
    pullbackFormsFun f (0 : HolomorphicOneForm E Y) = 0 := by
  funext x
  show ((0 : HolomorphicOneForm E Y).toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x) = 0
  have hcoe : ((0 : HolomorphicOneForm E Y) : ∀ x, _) (f x) = 0 := by
    rw [ContMDiffSection.coe_zero]
    rfl
  rw [show (0 : HolomorphicOneForm E Y).toFun (f x) = 0 from hcoe]
  exact ContinuousLinearMap.zero_comp _

/-- The pullback distributes over negation. -/
@[simp] theorem pullbackFormsFun_neg
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun f (-η) = -pullbackFormsFun f η := by
  funext x
  show ((-η).toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x) =
       -((η.toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x))
  have hcoe : ((-η) : ∀ x, _) (f x) = -(η : ∀ x, _) (f x) := by
    rw [ContMDiffSection.coe_neg]
    rfl
  rw [show (-η).toFun (f x) = -(η.toFun (f x)) from hcoe]
  exact ContinuousLinearMap.neg_comp _ _

/-- The pullback distributes over addition. -/
@[simp] theorem pullbackFormsFun_add
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsFun f (η + ζ) = pullbackFormsFun f η + pullbackFormsFun f ζ := by
  funext x
  show ((η + ζ).toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x) =
       (η.toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x) +
       (ζ.toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x)
  have hcoe : ((η + ζ) : ∀ x, _) (f x) = (η : ∀ x, _) (f x) + (ζ : ∀ x, _) (f x) := by
    rw [ContMDiffSection.coe_add]
    rfl
  rw [show (η + ζ).toFun (f x) = η.toFun (f x) + ζ.toFun (f x) from hcoe]
  exact ContinuousLinearMap.add_comp _ _ _

end JacobianChallenge.TraceDegree
