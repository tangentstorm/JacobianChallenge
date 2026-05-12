import Jacobian.TraceDegree.PiecewiseC1Def

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
  subclass of `H₁(X, ℤ)` that is shown to span the homology;
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

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/-- The piecewise-C¹ path regularity assumption, as a typeclass instance
applicable to every `ChartedSpace ℂ X`. The intended use is compact
Riemann surfaces, but the instance is stated at the typeclass header's
generality so it satisfies all callers uniformly.

The body is the named sorry tracked in `sorries.jsonl` (id 1340,
blueprint `lem:impl-trace-lip`) — see the module docstring for the
honest discharge plan.

**BLOCKER — unconditional statement is false.**
The hypothesis quantifies over arbitrary `γ : Path a b`, which is
just a *continuous* map `unitInterval → X`. Unfolding
`chartLift c γ h = γ.map' (c.continuousOn_toFun.mono h)`, the lifted
path's `extend` is definitionally `c ∘ γ.extend`. For a
Weierstrass-style nowhere-differentiable continuous `γ` whose image
lies in a single chart source (take `n := 1`, `pickX 0 := a`, so the
subpath equals `γ` itself), `c ∘ γ.extend` is not
`DifferentiableOn ℝ` on `Icc 0 1`, hence no `K₀ : NNReal` can witness
`ChartLiftPiecewiseC1 γ K₀`.

**Missing prerequisites** required to discharge this honestly:
1. *Smooth singular homology over ℤ for a smooth manifold* —
   replace the current singular `IntegralOneCycle X` with a chain
   complex whose 1-simplices are required to be piecewise C¹ (or
   smooth) in chart coordinates. Mathlib (pinned commit
   `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) does not provide this.
2. *Smooth approximation / Whitney-style theorem*: the inclusion of
   the smooth chain complex into the singular chain complex induces
   an isomorphism on homology. This is the standard tool that lets
   one pick a smooth representative inside every singular homology
   class, which is exactly what `PiecewiseC1PathRegularity` should
   really be saying — restricted to a smooth subcomplex of cycles,
   not to all continuous paths.
3. *Refactor of the period pairing API* so that
   `IntegralOneCycle X` carries a smooth/piecewise-C¹ witness and
   downstream callers (`PushforwardBasis.lean`, `PullbackBasis.lean`,
   `analyticPushforward`) consume that witness instead of asking for
   the false unconditional regularity above.

Until items (1)–(3) are built, this instance must remain a single
named `sorry`. Direct tactic discharge is impossible because the
proposition is false; the only honest fix is to weaken the typeclass
to a smoothness-aware cycle domain. Statement is intentionally left
unchanged here per the project's "audit-trail of false assumptions"
discipline — see the module docstring. -/
noncomputable instance instPiecewiseC1PathRegularity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    PiecewiseC1PathRegularity X where
  out := by
    -- BLOCKED: proposition is false for arbitrary continuous paths.
    -- See module docstring + declaration docstring above for the
    -- missing prerequisites (smooth singular homology + smooth
    -- approximation theorem + period-pairing refactor).
    sorry
  out_contDiff := by
    -- BLOCKED for the same reason as `out`: `chartLift c γ h` is
    -- definitionally `c ∘ γ`, so a Weierstrass-style nowhere-
    -- differentiable continuous `γ` lifts to a non-C¹ path.
    -- The honest fix is the same smoothness-aware cycle domain
    -- described above.
    sorry

end JacobianChallenge.TraceDegree
