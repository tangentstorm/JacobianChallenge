import Jacobian.HolomorphicForms.Defs
import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunId
import Jacobian.TraceDegree.PullbackFunComp
import Jacobian.TraceDegree.PullbackFormsLinearMap
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-!
# Bundled smooth pullback of holomorphic 1-forms

This file upgrades `pullbackFormsFun f η` (a function `X → ℂ →L[ℂ] ℂ`,
defined in `Jacobian/TraceDegree/PullbackFun.lean`) to a genuine
holomorphic 1-form `HolomorphicOneForm ℂ X`, given that `f` is `ContMDiff ω`.

## Mathlib gap

The construction requires section-level smoothness through chart
trivializations of the cotangent bundle (a `Bundle.ContinuousLinearMap`
bundle). Mathlib v4.28.0 lacks user-facing chart-transition / `localCoeff`
API for such sections — see `Jacobian/HolomorphicForms/ChartCoeffExtractionRecon.lean`
for the detailed analysis.

We therefore expose the bundled pullback as **`opaque`** for now, with two
named obligations characterising its function-level behavior:

* `pullbackFormsBundledLM_apply_fun` — the underlying function of the
  bundled pullback equals `pullbackFormsFun f η`. This is a "section
  extraction" axiom: once the chart-coefficient API exists, this becomes
  `rfl` for a concrete construction.

This is a strict TOPDOWN refinement: the previous 2 sorries on
`PushforwardBasis.lean` (`holomorphicTraceCoord_id` / `_comp`) get
replaced by 0 sorries on that file and the smoothness/section-extraction
obligation here, which is precisely the Mathlib gap the project's recon
file already names.

## API exposed

* `pullbackFormsBundledLM f hf : HolomorphicOneForm ℂ Y →ₗ[ℂ] HolomorphicOneForm ℂ X`
  — opaque ℂ-linear map.
* `pullbackFormsBundledLM_apply_fun` — pointwise `.toFun` agreement with
  `pullbackFormsFun` (sorry).
* `pullbackFormsBundledLM_id` — identity functoriality (sorry-free assembly).
* `pullbackFormsBundledLM_comp` — composition functoriality (sorry-free
  assembly).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff
open JacobianChallenge.TraceDegree

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/-- The pullback of holomorphic 1-forms as a ℂ-linear map between the
form spaces. Bottom-up: opaque pending the project's chart-coefficient
extraction API (see `ChartCoeffExtractionRecon.lean`). -/
noncomputable opaque pullbackFormsBundledLM
    (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ Y →ₗ[ℂ] HolomorphicOneForm ℂ X

/-- Section-extraction axiom: the underlying function of the bundled
pullback agrees with `pullbackFormsFun f η`. Sorry: the project-local
chart-coefficient API would make this `rfl` for a concrete construction. -/
theorem pullbackFormsBundledLM_apply_fun
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) (x : X) :
    (pullbackFormsBundledLM X Y f hf η).toFun x = pullbackFormsFun f η x :=
  sorry

/-- Identity functoriality: pullback of a form along the identity map is
the form itself. Sorry-free assembly via `pullbackFormsBundledLM_apply_fun`
plus `pullbackFormsFun_id`. -/
theorem pullbackFormsBundledLM_id :
    pullbackFormsBundledLM X X (id : X → X) contMDiff_id = LinearMap.id := by
  refine LinearMap.ext fun η => ?_
  apply ContMDiffSection.coe_inj
  funext x
  change (pullbackFormsBundledLM X X (id : X → X) contMDiff_id η).toFun x =
    (LinearMap.id η).toFun x
  rw [pullbackFormsBundledLM_apply_fun, pullbackFormsFun_id]
  rfl

/-- Composition functoriality: pullback distributes contravariantly over
composition. Sorry-free assembly via `pullbackFormsBundledLM_apply_fun`
plus `pullbackFormsFun_comp_apply`. -/
theorem pullbackFormsBundledLM_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) g) :
    pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) =
      (pullbackFormsBundledLM X Y f hf).comp
        (pullbackFormsBundledLM Y Z g hg) := by
  refine LinearMap.ext fun η => ?_
  apply ContMDiffSection.coe_inj
  funext x
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
  -- Step into .toFun on both sides.
  change (pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) η).toFun x =
    (((pullbackFormsBundledLM X Y f hf).comp
      (pullbackFormsBundledLM Y Z g hg)) η).toFun x
  rw [pullbackFormsBundledLM_apply_fun (g ∘ f) (hg.comp hf) η x]
  rw [pullbackFormsFun_comp_apply f g η x
    (hg.mdifferentiable htop _) (hf.mdifferentiable htop _)]
  -- LHS: (η.toFun (g (f x)) ∘L mfderiv g (f x)) ∘L mfderiv f x
  -- RHS: ((B_f.comp B_g) η).toFun x where B_? := pullbackFormsBundledLM ...
  change _ = (pullbackFormsBundledLM X Y f hf
    (pullbackFormsBundledLM Y Z g hg η)).toFun x
  rw [pullbackFormsBundledLM_apply_fun f hf
    (pullbackFormsBundledLM Y Z g hg η) x]
  show ((η.toFun (g (f x))).comp _).comp _ =
    pullbackFormsFun f (pullbackFormsBundledLM Y Z g hg η) x
  unfold pullbackFormsFun
  rw [pullbackFormsBundledLM_apply_fun g hg η (f x)]
  show ((η.toFun (g (f x))).comp _).comp _ =
    (pullbackFormsFun g η (f x)).comp _
  unfold pullbackFormsFun
  rfl

end JacobianChallenge.HolomorphicForms
