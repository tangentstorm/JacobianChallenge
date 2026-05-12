import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Continuity of eval-at-one for cotangent sections
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The constant `1` section of the tangent bundle of a manifold modeled on
`modelWithCornersSelf ℂ ℂ` is `ContMDiff`.

**BLOCKER — missing prerequisite `[JacobianChallenge.Periods.StableChartAt ℂ X]`.**

Reducing via `Bundle.contMDiffAt_section` at a point `x₀ : X`, the goal becomes
smoothness of
  `fun x ↦ (trivializationAt ℂ (TangentSpace 𝓘(ℂ,ℂ)) x₀ ⟨x, 1⟩).2`
at `x₀`. Unfolding `trivializationAt = (tangentBundleCore _ _).localTriv (achart ℂ x₀)`
via `VectorBundleCore.localTriv_apply` gives
  `(tangentBundleCore 𝓘(ℂ,ℂ) X).coordChange (achart ℂ x) (achart ℂ x₀) x 1`.
This involves `achart ℂ x`, which depends on the chart selected at the variable
point `x`. In Mathlib's `ChartedSpace`, the chart selector
`x ↦ chartAt H x` carries **no** local-constancy or continuity guarantee, so the
above function is not smooth (or even continuous) in `x` without an extra
hypothesis.

The project's `JacobianChallenge.Periods.StableChartAt H M` typeclass
(`Jacobian/Periods/TrivializationContinuousLinearMapAt.lean`) supplies exactly
this missing assumption: `chartAt H q = chartAt H p` for `q ∈ (chartAt H p).source`.
Under `[StableChartAt ℂ X]`, `achart ℂ x = achart ℂ x₀` on `(chartAt ℂ x₀).source`
and `coordChange_self` collapses the expression to `1`, making the section
locally constant in the trivialization and hence smooth via
`ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const`.

To unblock: add `[JacobianChallenge.Periods.StableChartAt ℂ X]` to the variable
section of this file (this hypothesis is already standard on downstream uses
in `Jacobian/Solution.lean` and `Jacobian/Periods/HolomorphicOneFormToFunContinuous.lean`).
-/
theorem contMDiff_tangentSection_one :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => TotalSpace.mk' ℂ (E := TangentSpace (𝓘(ℂ, ℂ))) x (1 : ℂ)) := by
  sorry

/-- Eval-at-1 of a smooth cotangent section is continuous. Uses
`ContMDiff.clm_bundle_apply` to combine the cotangent section with
the constant tangent section. -/
theorem continuous_eval_at_one_of_contMDiffSection
    (σ : HolomorphicOneForm ℂ X) :
    Continuous (fun x => (σ.toFun x) (1 : ℂ)) := by
  -- Step 1: Apply clm_bundle_apply to get smooth section of trivial bundle
  have hresult : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => TotalSpace.mk' ℂ (E := Trivial X ℂ) x
        (show (Trivial X ℂ) x from (σ.toFun x) (1 : ℂ))) :=
    σ.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
  -- Step 2: Extract continuity from the trivial bundle section
  have hcont := hresult.continuous
  rw [continuous_iff_continuousAt] at hcont ⊢
  intro x₀
  have hx := hcont x₀
  rw [FiberBundle.continuousAt_totalSpace] at hx
  convert hx.2

end JacobianChallenge.HolomorphicForms
