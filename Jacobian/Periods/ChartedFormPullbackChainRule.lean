import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackEqPullbackFormsFun
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.PullbackFunComp
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

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

/-- **Curve-integrand chain rule**: `curveIntegralFun` of the chart-coord
pullback of `pullbackFormsBundledLM X Y f hf η`, applied at a point `t`,
equals `η.toFun` evaluated at `f (c.symm (γ_X.extend t))`, applied to
the iterated `mfderiv` of `f` and `c.symm` on the path's `derivWithin`.

This is the integrand-level chain rule. It is the unfolding step
that drives path-level naturality: every term in the curve integral
of the chart-coord pullback factors through `η`'s value at
the pushed point and the chain-rule derivative. -/
theorem curveIntegralFun_chartedFormPullback_pullbackFormsBundledLM
    (c : OpenPartialHomeomorph X ℂ) (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) {a b : ℂ} (γ_X : Path a b) (t : ℝ) :
    curveIntegralFun (chartedFormPullback c (pullbackFormsBundledLM X Y f hf η)) γ_X t =
      η.toFun (f (c.symm (γ_X.extend t)))
        ((mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f
          (c.symm (γ_X.extend t)))
          ((mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) c.symm
            (γ_X.extend t))
            (derivWithin γ_X.extend unitInterval t))) := by
  rw [curveIntegralFun_def]
  exact chartedFormPullback_pullbackFormsBundledLM_apply c f hf η _ _

/-- **Identity case** of the chain rule: when `f = id`, the chart-coord
pullback of `id^*η` equals the chart-coord pullback of `η` directly. -/
theorem chartedFormPullback_pullbackFormsBundledLM_id
    (c : OpenPartialHomeomorph X ℂ) (η : HolomorphicOneForm ℂ X) :
    chartedFormPullback c (pullbackFormsBundledLM X X id contMDiff_id η) =
      chartedFormPullback c η := by
  rw [pullbackFormsBundledLM_id]
  rfl

/-- **Pointwise** identity-case of the chain rule. -/
theorem chartedFormPullback_pullbackFormsBundledLM_id_apply
    (c : OpenPartialHomeomorph X ℂ) (η : HolomorphicOneForm ℂ X) (e v : ℂ) :
    chartedFormPullback c (pullbackFormsBundledLM X X id contMDiff_id η) e v =
      chartedFormPullback c η e v := by
  rw [chartedFormPullback_pullbackFormsBundledLM_id]

/-- **Composition case** of the chain rule: pullback along `g ∘ f`
factors via the contravariant composition of pullbacks, by
`pullbackFormsBundledLM_comp`. -/
theorem chartedFormPullback_pullbackFormsBundledLM_comp
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]
    (c : OpenPartialHomeomorph X ℂ) (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) g)
    (η : HolomorphicOneForm ℂ Z) :
    chartedFormPullback c (pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) η) =
      chartedFormPullback c
        (pullbackFormsBundledLM X Y f hf
          (pullbackFormsBundledLM Y Z g hg η)) := by
  rw [pullbackFormsBundledLM_comp f hf g hg, LinearMap.comp_apply]

end JacobianChallenge.Periods
