import Jacobian.TraceDegree.PushforwardBasis

/-!
# Piecewise-C¹ regularity instance for compact Riemann surfaces

This file provides the (sorry-shaped) `PiecewiseC1PathRegularity X`
instance that the period-pairing / trace-degree layer needs.

The `Prop` itself — *every continuous path on `X` is piecewise C¹ in
chart coordinates with a uniform derivative bound* — is **false for
arbitrary continuous paths** (a nowhere-differentiable continuous path
is a valid inhabitant of `Path a b`). The honest discharge of this
assumption requires one of:

* enriching `IntegralOneCycle X` (currently singular `H₁`, untyped on
  smoothness) to carry a piecewise-smooth representative;
* restricting the period pairing's cycle domain to a piecewise-smooth
  subclass shown to span `H₁(X, ℤ)`;
* a layer of "smooth singular homology" not currently in Mathlib.

Until that infrastructure is built, the sorry is **isolated to this
single named instance** — production code (`PushforwardBasis.lean`,
`PullbackBasis.lean`, downstream Jacobian functoriality) is no longer
claiming to prove the false unconditional statement. The instance
is the single, named, auditable point where the assumption enters.

Blueprint anchor: `lem:impl-trace-lip`
(`tex/sections/15-implementation-details.tex`).
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/-- The piecewise-C¹ path regularity assumption, as a typeclass instance
applicable to every `ChartedSpace ℂ X`. The intended use is compact
Riemann surfaces, but the instance is stated at the typeclass header's
generality so it satisfies all callers uniformly.

The body is the named sorry tracked in `sorries.jsonl` (id 1340,
blueprint `lem:impl-trace-lip`) — see the module docstring for the
honest discharge plan. -/
noncomputable instance instPiecewiseC1PathRegularity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    PiecewiseC1PathRegularity X where
  out := by sorry

end JacobianChallenge.TraceDegree
