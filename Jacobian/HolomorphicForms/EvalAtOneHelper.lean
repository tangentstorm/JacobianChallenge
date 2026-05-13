import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Continuity of eval-at-one for cotangent sections
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-- The constant `1` section of the tangent bundle of a manifold modeled on
`modelWithCornersSelf ℂ ℂ` is `ContMDiff`.

The proof uses `Bundle.contMDiffAt_section` to reduce smoothness of the
section to smoothness of its trivialization at `x₀`. By
`FiberBundleCore.localTriv_apply`, that trivialization sends
`⟨y, 1⟩ ↦ ⟨y, (tangentBundleCore _ X).coordChange (achart ℂ y) (achart ℂ x₀) y 1⟩`.
Under `[StableChartAt ℂ X]`, `achart ℂ y = achart ℂ x₀` on
`(chartAt ℂ x₀).source`, so the `coordChange` collapses to the identity
by `FiberBundleCore.coordChange_self`, giving the constant value `1`
on a neighbourhood of `x₀`. -/
theorem contMDiff_tangentSection_one :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => TotalSpace.mk' ℂ (E := TangentSpace (𝓘(ℂ, ℂ))) x (1 : ℂ)) := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  refine (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
  have hx₀ : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds hx₀] with y hy
  have hachart : achart ℂ y = achart ℂ x₀ :=
    JacobianChallenge.Periods.achart_eq_of_mem_source hy
  change (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ x₀) y (1 : ℂ) = (1 : ℂ)
  rw [hachart]
  exact (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
    (achart ℂ x₀) y hy (1 : ℂ)

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
