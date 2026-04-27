import Jacobian.AbelJacobi.AnalyticOfCurveBasis

/-!
# Analytic pushforward on the basis-aligned carrier

A holomorphic map `f : X → Y` of compact Riemann surfaces induces a
pushforward `f_* : BasisAnalyticJacobian X → BasisAnalyticJacobian Y`,
typically constructed via the trace map on holomorphic 1-forms (or, in
basis coordinates, the dual of the trace), descended through the
period quotient.

This module mirrors `Jacobian/TraceDegree/PullbackBasis.lean` in the
opposite direction. Named obligations:

* `analyticPushforward f hf` — bundled `→ₜ+` hom on the basis-aligned
  carrier (`opaque`);
* `analyticPushforward_id_apply` — covariant identity functoriality;
* `analyticPushforward_comp_apply` — covariant composition;
* `analyticPushforward_contMDiff` — holomorphicity.

Bottom-up content: descent of the basis-aligned trace map on
`(Fin g_X → ℂ) →L[ℂ] (Fin g_Y → ℂ)` through periods.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/-- The analytic pushforward induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.

Top-down obligation. Bottom-up: descent of the basis-aligned trace map
on holomorphic 1-forms through the period quotient. -/
noncomputable opaque analyticPushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y

/-- The analytic pushforward is holomorphic.

Top-down obligation. Bottom-up: smoothness of the trace descent. -/
lemma analyticPushforward_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) := sorry

/-- Pushforward along the identity is the identity.

Top-down obligation. Bottom-up: the trace of the identity holomorphic
map is the identity. -/
lemma analyticPushforward_id_apply (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P := sorry

/-- Pushforward distributes covariantly over composition.

Top-down obligation. Bottom-up: trace is covariantly functorial under
composition of holomorphic maps. -/
lemma analyticPushforward_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) := sorry

end JacobianChallenge.TraceDegree
