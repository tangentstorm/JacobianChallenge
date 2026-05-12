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

BLOCKER: this statement is not provable from the bare
`[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]` hypotheses alone.

By `Mathlib.Geometry.Manifold.VectorBundle.Tangent`, the second component
of the trivialization at `x₀` applied to `⟨y, 1⟩` is, by `localTriv_apply`
and `tangentBundleCore`,
`(tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange (achart ℂ y) (achart ℂ x₀) y 1`,
i.e. the derivative of the chart transition between `chartAt ℂ y` and
`chartAt ℂ x₀`, evaluated at `y` and applied to `1`. The smooth-vector-bundle
mixin `ContMDiffVectorBundle` only provides smoothness of `coordChange i j`
for `i, j` ranging over a fixed pair of atlas charts; here the first index
`achart ℂ y = (chartAt ℂ y, …)` varies with `y`, and there is no axiom on
`ChartedSpace.chartAt` forcing this assignment to be locally constant nor
even locally compatible.

Concrete counterexample: take `X = ℂ ∖ {0}` with atlas `{id, z ↦ 1/z}`
(transition `1/·` is smooth on the overlap, so `IsManifold 𝓘(ℂ, ℂ) ⊤ X`
holds) and define `chartAt ℂ z := id` when `Re z > 0` and `z ↦ 1/z`
otherwise. Then `(trivializationAt at (-1) ⟨y, 1⟩).2` equals the constant
`1` on `{Re y ≤ 0}` but equals `-1/y²` on `{Re y > 0}`; the two pieces
agree at the boundary (continuous) but their derivatives do not match
(non-smooth across `Re y = 0`).

Discharging this `sorry` therefore requires either
(a) strengthening the ambient hypothesis (e.g. adding that the underlying
manifold uses `chartedSpaceSelf` or that `chartAt` is locally constant on
its source), or
(b) reformulating the eval-at-one helper to use a *locally* smooth tangent
field (e.g. the pullback of `1` through `extChartAt ℂ x₀` near each `x₀`)
together with `Trivialization.contMDiffAt_iff` instead of a global section.

Until that upstream fix is made, the proof is intentionally left as a
`sorry`. -/
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
