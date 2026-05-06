import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# Operator continuity of tangent bundle local trivialization (Mathlib-style packet)

This file contributes a project-local Mathlib-style lemma:
**For the tangent bundle on a `C^∞` complex manifold modeled on a
finite-dimensional normed space `E`, the function
`b ↦ mfderiv (chartAt E p₀) b` is operator-continuous on
`(chartAt E p₀).source`.**

## Proof attempt and obstruction

After substantial analysis, the natural proof attempts hit a fundamental
circular dependency:

* By `mfderiv_chartAt_eq_tangentCoordChange`,
  `mfderiv (chartAt E p₀) b = tangentCoordChange b p₀ b`
  `= (tangentBundleCore I X).coordChange (achart E b) (achart E p₀) b`.
  The **first chart index varies with `b`** (via `achart E b`).

* `continuousOn_coordChange i j` (Mathlib) gives operator continuity
  for **fixed** indices `i, j` on `baseSet i ∩ baseSet j`. The
  `b`-varying first index breaks this.

* By `continuousOn_clm_apply` (FiniteDim), operator continuity reduces
  to pointwise continuity for each `v ∈ E`. By
  `Bundle.contMDiffWithinAt_section`, pointwise continuity is
  equivalent to continuity of the constant section
  `b ↦ ⟨b, v⟩ : baseSet → TangentBundle X`, which in trivialization-
  coordinates reads `b ↦ (b, A(b) v)` — circular.

* Heine-Cantor on the compact unit ball requires joint continuity of
  `(b, v) ↦ A(b) v` on `baseSet × E`, which has the same constant
  section obstruction.

* `coordChange_comp` decompositions via fixed intermediate trivializations
  isolate the chart-at-varying factor; the residual factor still has
  the same form.

## Conclusion

The lemma as stated may **require** an additional hypothesis (e.g.,
that `chartAt E b = chartAt E p₀` for `b` in a neighborhood of `p₀` in
`(chartAt E p₀).source`, which holds for "natural" charted spaces but
is not part of the abstract `ChartedSpace` typeclass) **or**
substantial new bundle infrastructure (a smooth-bundle-local-frame
construction that pre-empts the chart-at issue).

For the project, we mark it as a clearly-identified Mathlib gap. The
project's main theorem (`mfderiv_chartSymm_continuousOn`) is sorry-free
in body and depends on this single helper. The honest path forward is
to either:

1. Land an upstream Mathlib lemma using the appropriate generalization
   (likely requiring local-frame infrastructure or chart-compatibility
   conditions).

2. Restrict the project's scope to manifolds where chartAt is
   structurally well-behaved (e.g., manifolds built from a fixed atlas
   with a canonical chart selector — the case in practice for Riemann
   surfaces).

## Note on pure-mathematical truth

The mathematical statement IS true for all common smooth manifolds in
practice (smooth chart changes guarantee that the trivialization map's
fiber portion varies smoothly in any reasonable atlas). The technical
obstruction is **purely a property of Mathlib's `ChartedSpace`
abstraction**: `chartAt` is typeclass data with no continuity or
locality requirement, leaving the "chart-at varying" problem as a
genuine artifact of the formalization.
-/

namespace JacobianChallenge.Periods

open Bundle Set Filter
open scoped Manifold ContDiff Topology

/-- **Operator continuity of `mfderiv` of a chart on a finite-dim
complex manifold** (Mathlib-style packet, sorry-stubbed pending
upstream).

For `chartAt E p₀` on a `C^∞` manifold modeled on a finite-dim normed
space `E`, the function `b ↦ mfderiv (chartAt E p₀) b ∈ E →L[ℂ] E` is
operator-continuous on `(chartAt E p₀).source`.

**Status**: Identified as a clearly-marked Mathlib gap. The proof
either requires a chart-at-compatibility hypothesis (which holds for
all common manifold instances but is not part of the abstract
`ChartedSpace` typeclass) or significant bundle infrastructure (smooth
local frames). See module docstring for analysis. -/
theorem mfderiv_chartAt_continuousOn_of_finiteDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (p₀ : X) :
    ContinuousOn (fun b =>
      show E →L[ℂ] E from
        mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
          (chartAt E p₀) b)
      (chartAt E p₀).source := by
  sorry

end JacobianChallenge.Periods
