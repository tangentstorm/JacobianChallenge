import Jacobian.Periods.PathLift
import Jacobian.Periods.DivFinIcc
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Subpath

namespace JacobianChallenge.TraceDegree

open Set unitInterval JacobianChallenge.Periods

/-- **Piecewise-C¹ regularity condition for paths.**

Says: for every uniform-grain partition `n, pickX` and segment index
`i`, the chart-lifted segment of `γ` is `C¹` on `[0, 1]`, *and* its
derivative norm is uniformly bounded by `K` (the same `K` across all
partitions and segments).

On a compact manifold with smooth atlas, a path that is piecewise C¹
(in the manifold sense) always satisfies this: C¹ on each piece gives
continuous derivatives, compactness of the path image gives finitely
many chart sources covering it, and the chart-transition derivatives
are bounded on that compact image; composing these bounds gives the
uniform `K`. -/
abbrev ChartLiftPiecewiseC1
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} (γ : Path a b) (K : NNReal) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (pickX : Fin n → X) (i : Fin n)
    (h : Set.range (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                                (divFinIcc n hn (i.val + 1) i.isLt)) ⊆
          (chartAt ℂ (pickX i)).source),
    ContDiffOn ℝ 1 (chartLift (chartAt ℂ (pickX i))
      (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                  (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
      (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖derivWithin (chartLift (chartAt ℂ (pickX i))
        (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                    (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
        (Set.Icc (0 : ℝ) 1) t‖₊ ≤ K

/-- **Piecewise-C¹ regularity predicate.** A continuous path `γ : Path a b`
on a charted space `X` is *piecewise C¹ in chart coordinates* if there
exists a uniform derivative bound `K : NNReal` such that
`ChartLiftPiecewiseC1 γ K` holds — i.e. every chart-lifted segment of
every uniform-grain partition of `γ` is C¹ on `[0, 1]` with derivative
norm bounded by `K`.

Unlike the unconditional class `PiecewiseC1PathRegularity` below, this
predicate is mathematically correct: it picks out exactly those paths
for which the chart-lift regularity machinery applies. Non-examples
include nowhere-differentiable continuous paths (Weierstrass-style). -/
abbrev IsPiecewiseC1Path {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} (γ : Path a b) : Prop :=
  ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ K₀

/-- **Project-level regularity assumption (typeclass form, predicate-gated).**

Predicate-gated form: *given a piecewise-C¹ witness for a path, we can
extract the uniform `K₀` bound.* This is **vacuously true** (the witness
is the conclusion itself) — the class no longer makes a false universal
claim.

Historical context: the previous form of this class asserted that EVERY
continuous path is piecewise C¹ in chart coordinates with a uniform
derivative bound. That statement is **false for arbitrary continuous
paths** (a nowhere-differentiable continuous path inhabits `Path a b`).
The instance was a single isolated sorry.

The honest fix is to gate the conclusion on a per-path witness
`IsPiecewiseC1Path γ`. The class instance becomes trivial; callers
that need a witness for a SPECIFIC path provide it themselves. Callers
that need a witness for an arbitrary path (universally quantified) now
route through a named obligation (`cyclePathRegularity_obligation` in
`Jacobian/TraceDegree/PiecewiseC1Instance.lean`), making the residual
false content audit-friendly. -/
class PiecewiseC1PathRegularity (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  /-- Witness extractor: given a piecewise-C¹ witness for a path, return it.
  This is vacuous (`fun _ h => h`); the class exists only to keep the
  legacy typeclass discipline at consumer sites. -/
  out : ∀ {a b : X} (γ' : Path a b), IsPiecewiseC1Path γ' → IsPiecewiseC1Path γ'

/-- Accessor: extract the per-path bound from a piecewise-C¹ witness.
With the predicate-gated class, this is just a pass-through. -/
theorem pathPiecewiseC1_of_regularity {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [hReg : PiecewiseC1PathRegularity X]
    {a b : X} (γ' : Path a b) (h : IsPiecewiseC1Path γ') :
    ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ' K₀ :=
  hReg.out γ' h

/-- Accessor: chart-lift `C¹` regularity of a subpath in an atlas chart.

**Refactor note (post-rebase):** the previous body relied on
`PiecewiseC1PathRegularity.out` returning an `∃ K, ChartLiftPiecewiseC1 γ K`
existential, which our predicate-gating refactor replaced with the
identity-like function `IsPiecewiseC1Path γ → IsPiecewiseC1Path γ`.
The derivation no longer goes through without an `IsPiecewiseC1Path γ'`
witness at this call site; left as a named frontier sorry until callers
are routed through the witness-form of the API
(`pathPiecewiseC1_of_regularity`). -/
theorem chartLift_contDiffOn_of_regularity {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [PiecewiseC1PathRegularity X]
    {a b : X} (γ' : Path a b) (n : ℕ) (hn : 0 < n) (pickX : Fin n → X) (i : Fin n)
    (h : Set.range (γ'.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                                (divFinIcc n hn (i.val + 1) i.isLt)) ⊆
          (chartAt ℂ (pickX i)).source) :
    ContDiffOn ℝ 1 (chartLift (chartAt ℂ (pickX i))
      (γ'.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                   (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
      (Set.Icc (0 : ℝ) 1) :=
  sorry

end JacobianChallenge.TraceDegree
