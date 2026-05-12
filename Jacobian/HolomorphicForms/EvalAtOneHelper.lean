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

**BLOCKER.** This statement is not provable for an arbitrary
`[ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]`. The trivialized
form of the constant-1 section at `x₀` is
`y ↦ (tangentBundleCore _ X).coordChange (achart ℂ y) (achart ℂ x₀) y · 1`,
whose first argument `achart ℂ y` need not be locally constant near
`x₀` — the abstract `ChartedSpace` API allows `chartAt` to be any
selector into the atlas. Without local compatibility of `chartAt`
(typically captured by `[JacobianChallenge.Periods.StableChartAt ℂ X]`,
under which `achart ℂ y = achart ℂ x₀` on `(chartAt ℂ x₀).source` and
the `coordChange` collapses to the identity by
`tangentBundleCore.coordChange_self`), this `coordChange` family is
generally not smooth as a function of `y`.

Missing prerequisite: a `[StableChartAt ℂ X]` hypothesis at this
declaration (and at `continuous_eval_at_one_of_contMDiffSection`
below), matching the convention used elsewhere in the project
(`Jacobian/Periods/HolomorphicOneFormToFunContinuous.lean`,
`Jacobian/HolomorphicForms/TraceBundled.lean`, etc.). The proof would
then proceed by `Bundle.contMDiffAt_section`,
`congr_of_eventuallyEq` against `contMDiffAt_const`, and
`TangentBundle.continuousLinearMapAt_trivializationAt_eq_core` together
with `tangentBundleCore.coordChange_self` (the model-space lemma
`TangentBundle.coordChange_model_space` only applies when `X = ℂ`). -/
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
