import Jacobian.Periods.PathLift
import Jacobian.Periods.DivFinIcc
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Subpath

namespace JacobianChallenge.TraceDegree

open Set unitInterval JacobianChallenge.Periods

/-- **Piecewise-C¹ regularity condition for paths.**

Says: for every uniform-grain partition `n, pickX` and segment index
`i`, the chart-lifted segment of `γ` is C¹ on `[0, 1]`, *and* its
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
    DifferentiableOn ℝ (chartLift (chartAt ℂ (pickX i))
      (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                  (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
      (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖derivWithin (chartLift (chartAt ℂ (pickX i))
        (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                    (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
        (Set.Icc (0 : ℝ) 1) t‖₊ ≤ K

/-- **Project-level regularity assumption (typeclass form).**

The statement carried by an instance: *every continuous path `γ : Path a b`
on `X` admits a uniform `K₀` with `ChartLiftPiecewiseC1 γ K₀`* — i.e.
every continuous path is piecewise C¹ in chart coordinates with a
uniform derivative bound.

This is **false for arbitrary continuous paths**: a nowhere-
differentiable continuous path (e.g. a Weierstrass-style curve embedded
in a chart) inhabits `Path a b` but cannot satisfy
`ChartLiftPiecewiseC1`.

Carried as a typeclass so the `analyticPushforward` API can pick it up
implicitly without threading an explicit hypothesis through every
call site. Provided by a single named sorry-instance in
`Jacobian/TraceDegree/PiecewiseC1Instance.lean`. -/
class PiecewiseC1PathRegularity (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  /-- Witness: every path admits a uniform piecewise-C¹ bound. -/
  out : ∀ {a b : X} (γ' : Path a b), ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ' K₀

/-- Accessor: extract the per-path bound from a `PiecewiseC1PathRegularity X`
instance. -/
theorem pathPiecewiseC1_of_regularity {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [hReg : PiecewiseC1PathRegularity X]
    {a b : X} (γ' : Path a b) :
    ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ' K₀ :=
  hReg.out γ'

end JacobianChallenge.TraceDegree
