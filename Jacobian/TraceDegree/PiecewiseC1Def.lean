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

/-- **Regular path wrapper.**

This is the sound path domain for period integration: the underlying
topological `Path` is bundled together with chartwise piecewise-C¹
data and a uniform derivative bound. Lemmas should consume this
wrapper, or equivalent explicit hypotheses, when they need analytic
path integration. -/
structure PiecewiseC1Path
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (a b : X) where
  /-- The underlying continuous path. -/
  toPath : Path a b
  /-- A uniform derivative bound for all chart-lifted uniform subpaths. -/
  bound : NNReal
  /-- Chartwise piecewise-C¹ regularity with the chosen bound. -/
  regular : ChartLiftPiecewiseC1 toPath bound

/-- Coerce a regular path to its underlying continuous path. -/
instance
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} : CoeFun (PiecewiseC1Path (X := X) a b) (fun _ => unitInterval → X) where
  coe γ := γ.toPath

/-- The explicit regularity witness carried by a `PiecewiseC1Path`. -/
theorem PiecewiseC1Path.chartLiftPiecewiseC1
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} (γ : PiecewiseC1Path (X := X) a b) :
    ChartLiftPiecewiseC1 γ.toPath γ.bound :=
  γ.regular

/-- **Legacy project-level regularity assumption (typeclass form).**

The statement carried by an instance: *every continuous path `γ : Path a b`
on `X` admits a uniform `K₀` with `ChartLiftPiecewiseC1 γ K₀`* — i.e.
every continuous path is piecewise C¹ in chart coordinates with a
uniform derivative bound.

This is **false for arbitrary continuous paths**: a nowhere-
differentiable continuous path (e.g. a Weierstrass-style curve embedded
in a chart) inhabits `Path a b` but cannot satisfy
`ChartLiftPiecewiseC1`.

This class is retained only as a legacy explicit hypothesis for
frontier declarations that have not yet been moved to
`PiecewiseC1Path`/regular chain inputs. There is intentionally no
global instance in `Jacobian/TraceDegree/PiecewiseC1Instance.lean`. -/
class PiecewiseC1PathRegularity (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  /-- Witness: every path admits a uniform piecewise-C¹ bound. -/
  out : ∀ {a b : X} (γ' : Path a b), ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ' K₀
  /-- Chartwise C¹ regularity on each chart-source portion of the path.

  This is kept as part of the legacy frontier hypothesis because the
  period-integration API needs exactly this localized statement, while the
  uniform-subpath field above only applies after a whole subpath is already
  known to lie in a single chart source. -/
  chart_contDiffOn : ∀ {a b : X} (γ' : Path a b) (p : X),
    ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ'.extend)
      (γ'.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1)

/-- Accessor: extract the per-path bound from a `PiecewiseC1PathRegularity X`
instance. -/
theorem pathPiecewiseC1_of_regularity {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [hReg : PiecewiseC1PathRegularity X]
    {a b : X} (γ' : Path a b) :
    ∃ K₀ : NNReal, ChartLiftPiecewiseC1 γ' K₀ :=
  hReg.out γ'

/-- Accessor: chart-lift `C¹` regularity of a subpath in an atlas chart,
extracted from the strengthened `ChartLiftPiecewiseC1` data. This is a
sorry-free derivation from an explicit legacy regularity hypothesis. -/
theorem chartLift_contDiffOn_of_regularity {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [hReg : PiecewiseC1PathRegularity X]
    {a b : X} (γ' : Path a b) (n : ℕ) (hn : 0 < n) (pickX : Fin n → X) (i : Fin n)
    (h : Set.range (γ'.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                                (divFinIcc n hn (i.val + 1) i.isLt)) ⊆
          (chartAt ℂ (pickX i)).source) :
    ContDiffOn ℝ 1 (chartLift (chartAt ℂ (pickX i))
      (γ'.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                   (divFinIcc n hn (i.val + 1) i.isLt)) h).extend
      (Set.Icc (0 : ℝ) 1) :=
  ((hReg.out γ').choose_spec n hn pickX i h).1

end JacobianChallenge.TraceDegree
