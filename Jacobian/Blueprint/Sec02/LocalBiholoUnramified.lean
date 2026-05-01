import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

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

This stub records the **statement only** (sorry-bearing, as MEDIUM
classification allows). The TOPDOWN split adds one named helper
`local_biholo_unramified_chart` that captures the chart-local content
(local bijection of a strictly differentiable `ℂ → ℂ` near a point
with nonzero derivative); the main theorem reduces to the helper
once the chart machinery is wired up — and that wiring is the
remaining sorry. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- **TOPDOWN helper (sorry).** Chart-local form of
`local_biholo_unramified`.

If `g : ℂ → ℂ` has a strict derivative `c ≠ 0` at `p`, then there
exist open neighbourhoods `U ∋ p` and `V ∋ g p` with `g` restricting
to a bijection `U → V`.

This is the chart-local content of the inverse function theorem
specialised to dimension 1 over `ℂ`. The discharge route: convert
`c` to a `ContinuousLinearEquiv ℂ ℂ` via `unitsEquivAut`, lift the
strict-deriv hypothesis to `HasStrictFDerivAt`, then take
`U := φ.source` and `V := φ.target` for
`φ := HasStrictFDerivAt.toOpenPartialHomeomorph` (in
`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`); the
`BijOn` follows from the partial-homeomorph data. The sorry is
recorded here so the main theorem below reduces to a single
named obligation. -/
theorem local_biholo_unramified_chart
    (g : ℂ → ℂ) (p : ℂ) (c : ℂ) (_hc : c ≠ 0)
    (_hg : HasStrictDerivAt g c p) :
    ∃ U V : Set ℂ,
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ g p ∈ V ∧ Set.BijOn g U V := by
  sorry

/-- A holomorphic map between complex 1-manifolds is locally a
homeomorphism around every unramified point: there exist open
neighbourhoods `U ∋ x` and `V ∋ f x` such that `f` restricts to a
bijection `U → V`.

The unramified hypothesis is encoded as `h.ramificationIndex x = 1`
relative to a packaged `BranchedCoverData` (sibling stub in
`Sec02/BranchedDegree.lean`).

DISCHARGE PLAN (sorry pending the chart-derivative connection):

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
   `sorry`-bearing).
4. Apply `local_biholo_unramified_chart` to get open neighbourhoods
   `U' ∋ φ x` and `V' ∋ g (φ x)` with `g` bijective `U' → V'`.
5. Pull back via the charts: `U := φ⁻¹ U'`, `V := ψ⁻¹ V'`. Openness,
   membership, and bijectivity transfer along the chart
   homeomorphisms.

The sorry collapses to the missing step (3) once a derivative-aware
upgrade of `BranchedCoverData` lands. -/
theorem local_biholo_unramified
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (_hunram : h.ramificationIndex x = 1) :
    ∃ U : Set X, ∃ V : Set Y,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧ Set.BijOn f U V := by
  sorry

end JacobianChallenge.Blueprint
