import Mathlib
import Jacobian.HolomorphicForms.Defs

/-!
# Continuity of eval-at-one for cotangent sections
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The constant `1` section of the tangent bundle of a manifold modeled on
`modelWithCornersSelf ℂ ℂ` is `ContMDiff`. -/
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
