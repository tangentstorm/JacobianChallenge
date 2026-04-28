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

open JacobianChallenge.ComplexTorus in
/-- Every continuous additive group homomorphism between complex tori
is smooth (`ContMDiff ω`).  This is a standard fact: continuous
homomorphisms between Lie groups are automatically smooth.

Bottom-up obligation.  The proof lifts the continuous homomorphism to a
continuous linear map on the covering spaces (automatically smooth),
then descends through the period-quotient projection (a local
diffeomorphism). -/
theorem contMDiff_continuousAddMonoidHom_complexTorus
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ΛV : FullComplexLattice V) (ΛW : FullComplexLattice W)
    (φ : quotient V ΛV →ₜ+ quotient W ΛW) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ W) ω φ := sorry

/-- Companion specification: the analytic pushforward is holomorphic.

Bottom-up obligation. Delegates to
`contMDiff_continuousAddMonoidHom_complexTorus`: the analytic
pushforward is a `ContinuousAddMonoidHom` between complex tori,
and every such homomorphism is smooth. -/
theorem analyticPushforward_contMDiff_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  contMDiff_continuousAddMonoidHom_complexTorus _ _ (analyticPushforward f hf)

/-- The analytic pushforward is holomorphic.

Top-down obligation. Assembly: delegates to
`analyticPushforward_contMDiff_spec`. -/
lemma analyticPushforward_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_spec f hf

/-- Specification: the trace of the identity holomorphic map on
holomorphic 1-forms is the identity; descending through the period
quotient preserves this.

Bottom-up obligation. Provable once `analyticPushforward` is concretized
as a descent of the basis-aligned trace map: the trace of the identity
branched covering (degree 1, single sheet) reduces to the identity on
forms, hence to the identity on the period quotient. -/
theorem analyticPushforward_id_spec (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P := sorry

/-- Pushforward along the identity is the identity.

Top-down obligation. Assembled from `analyticPushforward_id_spec`. -/
lemma analyticPushforward_id_apply (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P :=
  analyticPushforward_id_spec P

/-- Covariant composition specification for the analytic pushforward.

Companion spec tying `analyticPushforward` to its expected functorial
behaviour under composition.  Bottom-up: provable once
`analyticPushforward` is concretized as the descent of the
basis-aligned trace map on holomorphic 1-forms. -/
theorem analyticPushforward_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) := sorry

/-- Pushforward distributes covariantly over composition.

Top-down obligation. Assembled from `analyticPushforward_comp_spec`. -/
lemma analyticPushforward_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) :=
  analyticPushforward_comp_spec f hf g hg P

end JacobianChallenge.TraceDegree
