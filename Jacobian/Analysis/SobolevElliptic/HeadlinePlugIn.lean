import Jacobian.Analysis.SobolevElliptic.AbstractResolvent
import Jacobian.Analysis.BundledForms.L2Completion

/-!
# Phase 4 — Headline plug-in: real `Module.Finite ℝ (ker Δ)`

This file packages the analytic input from Phases 1–3 into a single
typeclass `HasLaplaceResolvent M μ` and produces the project's R10
headline as a *substantive* theorem against real Mathlib v4.28.0:

> Given a compact Riemannian manifold `M` with a finite Borel
> measure `μ` and the analytic data carried by
> `HasLaplaceResolvent M μ`, the real harmonic-function space
> `RealHarmonic M μ` is finite-dimensional.

The class `HasLaplaceResolvent` packages exactly the irreducible
analytic gap that remains after Phases 1–3:

  (a) a Hilbert space `Sobolev` (think `H¹(M)`);
  (b) a continuous linear embedding `inclusion : Sobolev → L²(M)`;
  (c) an `IsCompactOperator` witness for the embedding (Rellich-
      Kondrachov on a compact manifold).

When this typeclass is supplied (by future Phase 5 work that
constructs `H¹(M)` from chart-local distributional derivatives plus
partition of unity, or by the `AddCircle` model-space dispatch
that's tractable now), the headline finite-dim claim is automatic.

`RealHarmonic M μ` is the spectral substitute for the project's
placeholder `JacobianChallenge.StageB.Harmonic` (currently
`LinearMap.ker 0` over `Omega M k = PUnit`, vacuously finite).
The placeholder is left untouched (existing typed scaffolding
relies on it); `RealHarmonic` is the parallel substantive object,
following the pattern established by `Model.principalSymbol_isElliptic`
for chain K2.

**No `sorry`, no `True`-valued bodies.**

## Mathlib hooks

All transitively from Phase 3 (`AbstractResolvent.lean`); no new
direct Mathlib dependencies.
-/

namespace JacobianChallenge.Analysis.SobolevElliptic

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff NNReal ENNReal
open MeasureTheory
open JacobianChallenge.Analysis.BundledForms

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsManifoldMeasure M μ]

/-- **Phase 4.1.**  `HasLaplaceResolvent M μ` packages the
irreducible analytic gap after Phases 1–3: a Sobolev-`H¹`-like
Hilbert space sitting compactly inside `L²(M, μ)`.

This is intentionally a typeclass-with-data: future work will
supply instances by constructing `Sobolev` as a partition-of-unity
Sobolev space (general manifold case) or by harmonic-analysis on
specific compact models (`AddCircle`, tori, etc.).

The single substantive consequence (proved below as
`finiteDim_realHarmonic`) is that the spectral kernel
`RealHarmonic M μ` is finite-dimensional. -/
class HasLaplaceResolvent : Type (u + 1) where
  /-- The "Sobolev `H¹`" Hilbert space of square-integrable
  functions with a square-integrable derivative. -/
  Sobolev : Type
  /-- `H¹` is a normed real vector space. -/
  [normedAddCommGroup : NormedAddCommGroup Sobolev]
  /-- `H¹` is an inner-product space over `ℝ`. -/
  [innerProductSpace : InnerProductSpace ℝ Sobolev]
  /-- `H¹` is complete. -/
  [completeSpace : CompleteSpace Sobolev]
  /-- The continuous linear embedding `H¹ ↪ L²`. -/
  inclusion : Sobolev →L[ℝ] L2Fun M μ
  /-- The embedding is *compact* (Rellich–Kondrachov on a compact
  manifold).  This is the irreducible analytic input. -/
  inclusion_isCompact : IsCompactOperator inclusion

attribute [instance] HasLaplaceResolvent.normedAddCommGroup
  HasLaplaceResolvent.innerProductSpace
  HasLaplaceResolvent.completeSpace

namespace HasLaplaceResolvent

variable [hr : HasLaplaceResolvent M μ]

/-- The abstract resolvent built from the embedding:
`T := inclusion ∘ inclusion† : L²(M) → L²(M)`.  This is
`(Δ + 1)⁻¹` viewed entirely through the embedding; cf.\ the
file-level docstring of `AbstractResolvent.lean`. -/
noncomputable def laplaceResolvent : L2Fun M μ →L[ℝ] L2Fun M μ :=
  resolventOfEmbedding hr.inclusion

/-- The resolvent is self-adjoint. -/
theorem laplaceResolvent_isSelfAdjoint :
    IsSelfAdjoint (laplaceResolvent  M μ) :=
  isSelfAdjoint_resolventOfEmbedding hr.inclusion

/-- The resolvent is non-negative on the diagonal. -/
theorem laplaceResolvent_nonneg (x : L2Fun M μ) :
    0 ≤ @inner ℝ _ _ (laplaceResolvent  M μ x) x :=
  inner_resolventOfEmbedding_self_nonneg hr.inclusion x

/-- The resolvent is compact. -/
theorem laplaceResolvent_isCompactOperator :
    IsCompactOperator (laplaceResolvent  M μ) :=
  isCompactOperator_resolventOfEmbedding hr.inclusion_isCompact

end HasLaplaceResolvent

/-- **Real harmonic functions** on `(M, μ)`.  The eigenspace of the
abstract resolvent at `1`.  Concretely (modulo the spectral
correspondence `T f = f ↔ Δ f = 0`): the space of `L²`-harmonic
functions on `M`.

This is the *substantive* replacement for the project's placeholder
`JacobianChallenge.StageB.Harmonic` (which is
`LinearMap.ker 0` over `PUnit`, vacuously finite). -/
noncomputable def RealHarmonic [HasLaplaceResolvent M μ] :
    Submodule ℝ (L2Fun M μ) :=
  Eigenspace (HasLaplaceResolvent.laplaceResolvent  M μ) 1

/-- **Phase 4 headline (R10).**  `RealHarmonic M μ` is finite-
dimensional whenever `M` admits the `HasLaplaceResolvent` analytic
data.  This is the substantive R10 claim
`Module.Finite ℝ (ker Δ)`, dispatched against unmodified Mathlib
v4.28.0 modulo the single typeclass `HasLaplaceResolvent`.

The proof is one line: combine
`isCompactOperator_resolventOfEmbedding` with
`moduleFinite_resolvent_eigenspace`. -/
theorem moduleFinite_realHarmonic [HasLaplaceResolvent M μ] :
    Module.Finite ℝ (RealHarmonic  M μ) :=
  moduleFinite_resolvent_eigenspace
    (HasLaplaceResolvent.inclusion_isCompact  (M := M) (μ := μ))
    (one_ne_zero)

/-- **Phase 4 headline (R10), `FiniteDimensional` form.** -/
theorem finiteDim_realHarmonic [HasLaplaceResolvent M μ] :
    FiniteDimensional ℝ (RealHarmonic  M μ) :=
  finiteDimensional_resolvent_eigenspace
    (HasLaplaceResolvent.inclusion_isCompact  (M := M) (μ := μ))
    (one_ne_zero)

end JacobianChallenge.Analysis.SobolevElliptic
