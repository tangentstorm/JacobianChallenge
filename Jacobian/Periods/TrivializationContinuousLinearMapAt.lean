import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# Operator continuity of tangent bundle local trivialization (Mathlib-style packet)

This file contributes a project-local Mathlib-style lemma:
**For the tangent bundle on a `C^∞` complex manifold modeled on a
finite-dimensional normed space `E`, the local trivialization's
`continuousLinearMapAt` is operator-continuous on the trivialization's
base set.**

This lemma is missing from Mathlib v4.28.0 and bridges from
`ContMDiffWithinAt.mfderivWithin_const` (smoothness in
`inTangentCoordinates` form) to operator continuity of `mfderiv`
itself, in the specific case of inverse-chart maps.

## Mathematical content

For a `ContMDiffVectorBundle` with finite-dimensional fiber `F`, the
local trivialization at `b₀` provides a homeomorphism with
`baseSet × F`. The trivialization's fiber map `A(b) := (trivAt b₀).continuousLinearMapAt b`
is, by `Trivialization.continuousOn`, jointly continuous in `(b, v)`
on its source. For finite-dimensional `F`, this implies operator
continuity of `b ↦ A(b)` on `baseSet`.

The key argument:
* By `continuousOn_clm_apply` (FiniteDim), operator continuity
  reduces to pointwise continuity for each `w ∈ F`.
* Pointwise continuity of `b ↦ A(b) w` follows from the
  trivialization's fiber-by-fiber continuous structure.

This proof requires care with the bundle's smooth structure
(`ContMDiffVectorBundle.contMDiffOn_coordChangeL`) plus the
`NormedRing.inverse_continuousAt` argument on the open set of
invertible CLMs.

## Note

This lemma is left as a clearly-identified `sorry`-stubbed
Mathlib-style packet to be contributed upstream.
-/

namespace JacobianChallenge.Periods

open Bundle Set Filter
open scoped Manifold ContDiff Topology

/-- **Operator continuity of the tangent bundle's local trivialization
fiber map.** For a `C^∞` manifold `M` modeled on a finite-dimensional
normed space `E` (with self-model), the `continuousLinearMapAt b` of
the local trivialization at `p₀` on the tangent bundle is
operator-continuous in `b` on the trivialization's base set.

This is a Mathlib-style packet to be contributed upstream. The proof
combines `Trivialization.continuousOn` (joint continuity of the
trivialization map) with `continuousOn_clm_apply` (FiniteDim:
operator continuity ⟺ pointwise continuity) and the bundle's
smooth coord-change structure. -/
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
