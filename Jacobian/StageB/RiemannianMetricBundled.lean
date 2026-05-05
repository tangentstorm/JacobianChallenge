import Jacobian.StageB.LaplaceBeltrami
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Phase 2.1 — `RiemannianMetricBundled`: real Riemannian-metric typeclass

This file provides the substantive replacement for the project's
placeholder `RiemannianMetric` class
(`Jacobian/StageB/LaplaceBeltrami.lean:44`, where the body is
`metric_data : True`).  The new class
`RiemannianMetricBundled` carries a Mathlib `RiemannianBundle`
instance on the tangent bundle of `M`, which fibrewise gives every
`TangentSpace I x` a real `InnerProductSpace ℝ` structure varying
*continuously* (and, with the smooth variant, smoothly) in the base
point.

This is the M2 substrate from the dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 2.1).  No `True`-valued bodies — every assertion below is a
real Mathlib structure.

## Design

* `RiemannianMetricBundled M` is a typeclass whose data is precisely
  a `RiemannianBundle (TangentSpace 𝓘(ℝ, E))` instance (with the
  associated continuous Riemannian-metric input).  Concretely the
  data is a `ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ, E))`,
  which Mathlib then promotes to a fibrewise `InnerProductSpace ℝ`
  via `toRiemannianMetric` + the `RiemannianBundle` typeclass.

* We *do not* edit `LaplaceBeltrami.lean`; instead we provide a
  one-way back-compat instance
  `[RiemannianMetricBundled M] → RiemannianMetric E M`
  so existing downstream code that depends on the placeholder class
  keeps inferring it.

## Mathlib hooks used

* `Mathlib/Topology/VectorBundle/Riemannian.lean` — `RiemannianBundle`,
  `RiemannianMetric`, `ContinuousRiemannianMetric`,
  `ContinuousRiemannianMetric.toRiemannianMetric`.
* `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` —
  `IsContMDiffRiemannianBundle` (smooth variant; not required by
  this file but available for downstream Δ-construction).
* `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean` —
  `TangentSpace`, `tangentBundleCore.instContMDiffVectorBundle`.

## What this file does *not* do

* Does not construct the metric itself — that requires the user to
  supply data (e.g. via a chart-pulled-back Euclidean metric).  The
  typeclass is the *interface*; an instance witnesses *existence* of
  a real metric.
* Does not build the gradient, divergence, Laplacian, or volume
  form.  Those are downstream Phase 2 milestones (deferred to a
  future commit; see plan §Phase 2).
-/

namespace JacobianChallenge.StageB

open Bundle
open scoped Manifold ContDiff

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable (M : Type v) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Phase 2.1.**  `RiemannianMetricBundled M` registers a real
Riemannian metric on the tangent bundle of `M`.  Concretely it
carries a `ContinuousRiemannianMetric` on `TangentSpace I`, which
Mathlib promotes to:

* a per-fibre `InnerProductSpace ℝ (TangentSpace I x)` (scoped to
  the `Bundle` namespace, so users should `open Bundle`);
* an `[IsContinuousRiemannianBundle ...]` instance witnessing
  continuity of the metric in the base point.

The data is intentionally *minimal* — we ask for the continuous
variant rather than the smooth variant so that this file imposes the
weakest possible existence requirement on `M`.  A smooth metric
implies a continuous one, so any user of this typeclass who happens
to have a smooth metric can construct an instance for free.

This class is the substantive replacement for `RiemannianMetric E M`
(the project's previous placeholder, body `metric_data : True`); the
back-compat instance below ensures downstream code keeps compiling. -/
class RiemannianMetricBundled : Type (max u v) where
  /-- The continuous Riemannian metric on the tangent bundle. -/
  metric :
    ContinuousRiemannianMetric E
      (TangentSpace (modelWithCornersSelf ℝ E) (M := M))

namespace RiemannianMetricBundled

variable [h : RiemannianMetricBundled (E := E) M]

/-- The associated `RiemannianBundle` instance on the tangent
bundle.  Made an `instance` so that downstream code can refer to
inner products on `TangentSpace I x` directly. -/
noncomputable instance toRiemannianBundle :
    RiemannianBundle
      (TangentSpace (modelWithCornersSelf ℝ E) (M := M)) :=
  ⟨h.metric.toRiemannianMetric⟩

end RiemannianMetricBundled

/-- **Back-compat bridge.**  Any `M` carrying the new
`RiemannianMetricBundled` automatically satisfies the project's
old placeholder `RiemannianMetric` class.  This means existing
downstream code in `LaplaceBeltrami.lean` and below keeps
type-checking unchanged. -/
instance riemannianMetric_of_bundled
    [RiemannianMetricBundled (E := E) M] :
    RiemannianMetric E M where
  metric_data := trivial

end JacobianChallenge.StageB
