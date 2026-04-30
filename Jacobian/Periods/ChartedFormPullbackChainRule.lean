import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackEqPullbackFormsFun
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.PullbackFunComp

/-!
# Chain rule for `chartedFormPullback` of a `pullbackFormsBundledLM`

For `f : X → Y` smooth, `η : HolomorphicOneForm ℂ Y`, `c : OpenPartialHomeomorph X ℂ`,
and `e : ℂ` with `c.symm e ∈ X`, the chart-coord pullback of the smooth-bundled
pullback form factors via the chain rule:

  `chartedFormPullback c (pullbackFormsBundledLM X Y f hf η) e
    = (η.toFun (f (c.symm e))).comp (mfderiv (f ∘ c.symm) e)`

This is the **chart-coord chain rule** that drives chart-level pullback
naturality. It says: applying the chart-coord pullback to the smooth-bundled
pullback form yields the same as treating `f ∘ c.symm` as a single smooth
map and applying its `mfderiv` directly to `η.toFun`.

This is the project-local building block toward
`pathIntegralViaCover_pullbackFormsBundledLM`: in chart coordinates, the
pullback's curve-integrand reduces to `η`'s value on the pushed path's
chart-coord derivative.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.TraceDegree

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

/-- **Chart-coord chain rule** for the chart pullback of a smooth-bundled
form pullback. -/
theorem chartedFormPullback_pullbackFormsBundledLM
    (c : OpenPartialHomeomorph X ℂ) (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) (e : ℂ) :
    chartedFormPullback c (pullbackFormsBundledLM X Y f hf η) e =
      ((η.toFun (f (c.symm e))).comp
        (mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f (c.symm e))).comp
        (mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) c.symm e) := by
  -- chartedFormPullback c ω e := (ω.toFun (c.symm e)).comp (mfderiv c.symm e).
  -- Apply pullbackFormsBundledLM_apply_fun: (LM η).toFun = pullbackFormsFun f η.
  -- pullbackFormsFun f η x := (η.toFun (f x)).comp (mfderiv f x).
  -- So at e: ((η.toFun (f (c.symm e))).comp (mfderiv f (c.symm e))).comp (mfderiv c.symm e).
  rfl

/-- Composition form of the chain rule: combining the two `mfderiv`s into
the chain-rule derivative `mfderiv (f ∘ c.symm) e`. Requires `f` and
`c.symm` to be `MDifferentiableAt` at the relevant points. -/
theorem chartedFormPullback_pullbackFormsBundledLM_comp_mfderiv
    (c : OpenPartialHomeomorph X ℂ) (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) (e : ℂ)
    (hcs : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) c.symm e) :
    chartedFormPullback c (pullbackFormsBundledLM X Y f hf η) e =
      (η.toFun (f (c.symm e))).comp
        (mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (f ∘ c.symm) e) := by
  rw [chartedFormPullback_pullbackFormsBundledLM]
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  have hf_at : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) f (c.symm e) := hf.mdifferentiableAt htop
  rw [mfderiv_comp e hf_at hcs]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-- **Vector-applied form** of the chain rule: applying both sides at
a tangent vector `v : ℂ`. Useful when the chart-coord pullback appears
inside an integrand. -/
theorem chartedFormPullback_pullbackFormsBundledLM_apply
    (c : OpenPartialHomeomorph X ℂ) (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) (e v : ℂ) :
    chartedFormPullback c (pullbackFormsBundledLM X Y f hf η) e v =
      η.toFun (f (c.symm e))
        ((mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f (c.symm e))
          ((mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) c.symm e) v)) := by
  rw [chartedFormPullback_pullbackFormsBundledLM]
  rfl

end JacobianChallenge.Periods
