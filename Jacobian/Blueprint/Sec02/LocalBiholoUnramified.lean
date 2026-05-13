import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! # Blueprint stub: `thm:local-biholo-unramified`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A holomorphic map between complex 1-manifolds is a *local
biholomorphism* at every unramified point. The classical proof uses
the inverse function theorem applied to the chart-pulled function
`ψ ∘ f ∘ φ⁻¹ : ℂ → ℂ`: the holomorphic Jacobian at the chart image
of an unramified point is nonzero, so by
`HasStrictFDerivAt.toOpenPartialHomeomorph` (Mathlib) the chart-pulled
function is locally a homeomorphism, and holomorphicity of the
inverse follows from the Cauchy–Riemann equations.

This file records the blueprint statement and proves it from the
local-bijection field of `BranchedCoverData`. The TOPDOWN split adds one named helper
`local_biholo_unramified_chart` that captures the chart-local content
(local bijection of a strictly differentiable `ℂ → ℂ` near a point
with nonzero derivative); the main theorem reduces to the helper
once the chart machinery is wired up — and that wiring is the
remaining proof obligation. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- A holomorphic map between complex 1-manifolds is locally a
homeomorphism around every unramified point: there exist open
neighbourhoods `U ∋ x` and `V ∋ f x` such that `f` restricts to a
bijection `U → V`.

The unramified hypothesis is encoded as `h.ramificationIndex x = 1`
relative to a packaged `BranchedCoverData` (sibling stub in
`Sec02/BranchedDegree.lean`).

DISCHARGE PLAN (pending the chart-derivative connection):

1. Choose charts `φ : X → ℂ` near `x` and `ψ : Y → ℂ` near `f x` from
   the manifold structure (`extChartAt 𝓘(ℂ) x`, `extChartAt 𝓘(ℂ) (f x)`).
2. Form the chart-pulled function `g := ψ ∘ f ∘ φ⁻¹`.
3. The unramified hypothesis `h.ramificationIndex x = 1` should
   correspond, under any sensible upgrade of `BranchedCoverData`
   linking ramification to local power-series order, to
   `HasStrictDerivAt g c (φ x)` for some `c ≠ 0`. The current
   `BranchedCoverData` does not yet carry this link — adding it is a
   sub-leaf of `def:branched-degree` (the analytic constructor
   `branchedCoverData_of_nonconstant_holomorphic` is itself
   carried by the packaged data).
4. Apply `local_biholo_unramified_chart` to get open neighbourhoods
   `U' ∋ φ x` and `V' ∋ g (φ x)` with `g` bijective `U' → V'`.
5. Pull back via the charts: `U := φ⁻¹ U'`, `V := ψ⁻¹ V'`. Openness,
   membership, and bijectivity transfer along the chart
   homeomorphisms.

The proof collapses to the packaged step (3) once a derivative-aware
upgrade of `BranchedCoverData` lands. -/
theorem local_biholo_unramified
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (_hunram : h.ramificationIndex x = 1) :
    ∃ U : Set X, ∃ V : Set Y,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧ Set.BijOn f U V := by
  exact h.local_bijective_unramified x _hunram

end JacobianChallenge.Blueprint
