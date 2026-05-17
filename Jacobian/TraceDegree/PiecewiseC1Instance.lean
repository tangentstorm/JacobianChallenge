import Jacobian.TraceDegree.PiecewiseC1Def

/-!
# Quarantine for the former global piecewise-C¹ path instance

This module intentionally provides **no**
`PiecewiseC1PathRegularity X` instance.

The previous version asserted, via a global instance, that every
continuous `Path` on an arbitrary charted space is piecewise-C¹ in
chart coordinates with a uniform derivative bound. That statement is
false: continuous paths can be nowhere differentiable inside a single
chart.

The sound replacement is in `Jacobian.TraceDegree.PiecewiseC1Def`:

* `ChartLiftPiecewiseC1 γ K` records explicit chartwise C¹ data for a
  particular path.
* `PiecewiseC1Path a b` bundles a continuous path with such data.
* Remaining legacy declarations may still take
  `[PiecewiseC1PathRegularity X]` as an explicit frontier hypothesis,
  but importing this file no longer synthesizes that hypothesis.

The missing topological theorem is separate: on a smooth compact
surface, the inclusion of smooth (or piecewise-C¹) singular chains
into all singular chains induces the expected homology isomorphism, so
every singular homology class admits a regular representative.
That theorem should feed the period-pairing construction through a
regular chain/cycle API, not by proving regularity for arbitrary
continuous paths.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.Periods

/-- Documentation marker for the quarantined false instance.

This proposition is deliberately trivial: it gives downstream files a
stable name to cite in comments without introducing any instance,
axiom, or proof obligation for the false global regularity statement. -/
theorem no_global_piecewiseC1PathRegularity_instance : True := by
  trivial

/-- Documentation marker for the remaining topological frontier.

The intended future theorem is not this `True` statement; it is the
standard smooth-approximation comparison saying that, on a smooth
compact surface, smooth or piecewise-C¹ singular chains compute the
same degree-one integral homology as all singular chains. Once that is
formalized, `IntegralOneCycle X` can be paired with regular
representatives without asserting regularity of arbitrary continuous
paths. -/
theorem smooth_chain_homology_comparison_frontier : True := by
  trivial

end JacobianChallenge.TraceDegree
