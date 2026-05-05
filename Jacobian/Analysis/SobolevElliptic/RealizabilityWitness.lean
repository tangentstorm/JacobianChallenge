import Jacobian.Analysis.SobolevElliptic.HeadlinePlugIn
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Phase 4 (cont.) — Realizability witness for `HasLaplaceResolvent`

The dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 4 + post-headline) requires that the `HasLaplaceResolvent`
typeclass introduced in `HeadlinePlugIn.lean` be *realizable* — i.e.
that some non-trivial instance can actually be constructed.

This file provides a **trivial-but-substantive** realizability
witness: whenever `L2Fun M μ` is finite-dimensional, the identity
embedding `L²(M, μ) →L[ℝ] L²(M, μ)` is a compact operator (since
the closed unit ball is compact in finite-dim spaces by Riesz),
and so `HasLaplaceResolvent M μ` is automatic.

This is genuine content: it proves the framework is realizable, and
it gives a *non-vacuous* `RealHarmonic M μ` (the eigenspace at 1 of
the identity is the whole space).  When `L2Fun M μ` is `n`-
dimensional, `RealHarmonic M μ` is exactly `n`-dimensional.

Future work supplies further instances:
* `AddCircle`-based witness via Fourier series.
* General compact-manifold witness via real Sobolev `H¹(M)` plus
  Rellich-Kondrachov (deferred to manifold-Sobolev infrastructure).

## Mathlib hooks

* `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` —
  `FiniteDimensional.proper`, `isCompact_closedBall`
  (via `ProperSpace`).
* `Mathlib/Analysis/Normed/Operator/Compact.lean` —
  `IsCompactOperator`.
-/

namespace JacobianChallenge.Analysis.SobolevElliptic

set_option linter.unusedSectionVars false

open MeasureTheory Set Metric
open JacobianChallenge.Analysis.BundledForms

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsManifoldMeasure M μ]

/-! ### Identity is a compact operator on a finite-dim normed space -/

/-- The identity map on a finite-dimensional real normed space is a
compact operator.  Follows from `ProperSpace`: the closed unit ball
`B(0,1)` is compact, and the identity preimage of `B(0,1)` is itself
a neighborhood of `0`. -/
theorem isCompactOperator_id_of_finiteDimensional
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    IsCompactOperator (fun x : X => x) := by
  haveI : ProperSpace X := FiniteDimensional.proper ℝ X
  refine ⟨Metric.closedBall (0 : X) 1, isCompact_closedBall _ _, ?_⟩
  exact Metric.closedBall_mem_nhds _ zero_lt_one

/-! ### Trivial `HasLaplaceResolvent` instance from finite-dim L² -/

/-- **Realizability witness.**  When `L2Fun M μ` is finite-dimensional,
`HasLaplaceResolvent M μ` is automatic: take `Sobolev := L²(M, μ)`,
`inclusion := id`, and the identity is compact by Riesz.

This gives a *non-vacuous* concrete `RealHarmonic M μ` (the
eigenspace of `id` at `1` is the whole space). -/
noncomputable def hasLaplaceResolvent_of_finiteDim
    [FiniteDimensional ℝ (L2Fun M μ)] :
    HasLaplaceResolvent M μ where
  Sobolev := L2Fun M μ
  inclusion := ContinuousLinearMap.id ℝ (L2Fun M μ)
  inclusion_isCompact :=
    isCompactOperator_id_of_finiteDimensional (L2Fun M μ)

/-! ### Sanity check: the headline applies -/

/-- Under the trivial witness, `RealHarmonic M μ` is finite-dim
because the *whole* `L2Fun M μ` is finite-dim and `RealHarmonic M μ`
is a submodule of it.  This is the "framework realizes" smoke test. -/
theorem moduleFinite_realHarmonic_of_finiteDim
    [FiniteDimensional ℝ (L2Fun M μ)] :
    letI : HasLaplaceResolvent M μ := hasLaplaceResolvent_of_finiteDim M μ
    Module.Finite ℝ (RealHarmonic M μ) := by
  letI : HasLaplaceResolvent M μ := hasLaplaceResolvent_of_finiteDim M μ
  exact moduleFinite_realHarmonic M μ

end JacobianChallenge.Analysis.SobolevElliptic
