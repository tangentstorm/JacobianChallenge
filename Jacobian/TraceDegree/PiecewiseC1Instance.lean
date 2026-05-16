import Jacobian.TraceDegree.PiecewiseC1Def

/-!
# Piecewise-C¹ regularity instance for compact Riemann surfaces

This file provides the `PiecewiseC1PathRegularity X` typeclass instance
that the period-pairing / trace-degree layer needs.

**2026-05-14 refactor — predicate gate.** The class field was previously
the **false** unconditional claim that every continuous path on `X` is
piecewise C¹. The class is now gated on a per-path
`IsPiecewiseC1Path γ` predicate (defined in `PiecewiseC1Def.lean`):
the instance asserts only that a witness can be extracted from a
witness, which is vacuously true.

The residual false content is **isolated** to a single named obligation
`cyclePathRegularity_obligation`, which states that EVERY continuous
path is piecewise C¹. This is the same false universal claim, but now
named, scoped, and audit-friendly. Production code routes through this
named obligation rather than the typeclass field.

The honest fix for `cyclePathRegularity_obligation` requires:

* enriching `IntegralOneCycle X` (currently singular `H₁`, untyped on
  smoothness) to carry a piecewise-smooth representative;
* restricting the period pairing's cycle domain to a piecewise-smooth
  subclass of `H₁(X, ℤ)` that is shown to span the homology;
* a smooth singular homology theory bridged to continuous singular
  homology via Whitney smooth approximation.

Blueprint anchor: `lem:impl-trace-lip`
(`tex/sections/15-implementation-details.tex`).
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/-- The piecewise-C¹ path regularity typeclass instance, predicate-gated.
The class field is the trivial extractor `fun γ h => h`: given a
piecewise-C¹ witness for `γ`, return it. Sorry-free. -/
instance instPiecewiseC1PathRegularity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    PiecewiseC1PathRegularity X where
  out := fun _γ h => h

/-- **Named residual obligation (BLOCKER, false universally).**

The cycle-level regularity assumption: every continuous path on `X` is
piecewise C¹ in chart coordinates with a uniform derivative bound.

This is **literally false** for arbitrary continuous paths (Weierstrass-
style nowhere-differentiable continuous paths inhabit `Path a b`). The
sorry is intentionally preserved as a NAMED obligation so the audit
trail is explicit at each call site.

Discharge path (multi-session work, see plan file):
1. Define a `PiecewiseC1Path a b X` structure carrying the smoothness
   witness as data (Phase 2).
2. Refactor `pathPotentialAsForm` (flagship descent) to construct paths
   via a smooth-manifold path-connectedness theorem instead of choosing
   arbitrary continuous paths (Phase 4).
3. Eliminate this obligation by either: (a) refactoring downstream
   `IntegralOneCycle X` to be smooth-quotient, or (b) restricting all
   callers to supply per-path `IsPiecewiseC1Path γ` witnesses.

Callers: `Jacobian/TraceDegree/PushforwardBasis.lean:388,390`,
`Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean:281` family. -/
theorem cyclePathRegularity_obligation
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} (γ : Path a b) :
    IsPiecewiseC1Path γ := by
  -- BLOCKED: the claim is false for arbitrary continuous paths.
  -- Discharge requires the multi-phase plan in
  -- /Users/eric.yhl/.claude/plans/can-you-try-to-stateful-whistle.md
  -- (smooth singular homology / smooth-path refactor of the flagship).
  sorry

end JacobianChallenge.TraceDegree
