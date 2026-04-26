import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Path

/-!
# Reconnaissance: path integration and the period lattice

Queue D kickoff. This is a name-discovery and design document for
the period-lattice machinery needed by the analytic-Jacobian route.

Like the earlier `ComplexTorus/*Recon.lean` and
`HolomorphicForms/Recon.lean` files, this contains no production
declarations beyond a stub token; it is not re-exported.

## Phase context

Queue C now provides:
- `HolomorphicOneForm E X` — analytic `ContMDiffSection` of the
  cotangent bundle (`Jacobian/HolomorphicForms/Defs.lean`);
- `FiniteDimensionalHolomorphicOneForms E X` class (proof deferred);
- `analyticGenus E X = Module.finrank ℂ (HolomorphicOneForm E X)`.

The next layer is the period-lattice construction
`H₁(X, ℤ) → H⁰(X, Ω¹)*` whose image is a full lattice. This is the
"central technical bottleneck" per `plan.md` Phase 3.

## What Mathlib v4.28.0 has

* `MeasureTheory/Integral/CurveIntegral/Basic.lean` — `curveIntegral`
  `(∫ᶜ x in γ, ω x)` for `ω : E → E →L[𝕜] F` and `γ : Path a b` in
  a normed space `E`. **Normed-space only.** Includes
  `CurveIntegrable`, `curveIntegral_add`, `curveIntegral_trans`,
  `curveIntegral_symm`, `curveIntegral_refl`.
* `AlgebraicTopology/SingularHomology/Basic.lean` —
  `singularChainComplexFunctor`, `singularHomologyFunctor`. Mature
  homological backbone; concrete computations limited.
* `Topology/Path` — `Path a b` requires `a b : E` for a topological
  space. Path concatenation and reversal exist.
* `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean` —
  `FundamentalGroup`, `FundamentalGroupoid`.

## What Mathlib v4.28.0 does NOT have

* No path / curve integration on manifolds (only on normed spaces).
  No bridge from `curveIntegral` through a chart atlas.
* No cap product, no Künneth, no fundamental class for oriented
  manifolds.
* No computation of `H₁` for a compact Riemann surface.
* No pairing between singular homology and differential forms.
* No Hurewicz homomorphism `π₁^{ab} → H₁(X, ℤ)`.
* No Stokes / de Rham on manifolds with boundary; only box /
  rectangle versions.
* No proof that the period subgroup is a full lattice (this is
  essentially the nondegeneracy of the period pairing, classically
  via Riemann bilinear relations).

## Design choices

The challenge needs:
1. A type `IntegralOneCycle X` for integral 1-cycles;
2. A pairing `IntegralOneCycle X →+ HolomorphicOneFormDual X`
   (the period functional);
3. A `periodSubgroup X : AddSubgroup …` whose closure is a full
   complex lattice.

### Approach for (1): bridge to singular homology

Take `IntegralOneCycle X` to be the closed (boundary = 0) chains in
the singular chain complex with ℤ coefficients, modulo boundaries.
Equivalently, use Mathlib's `singularHomologyFunctor (n := 1)` at
`X`.

### Approach for (2): chart-local lift of `curveIntegral`

A 1-cycle is a finite ℤ-linear combination of singular 1-simplices,
each of which is a continuous map `Δ¹ → X`. To integrate a
holomorphic 1-form `ω` over such a simplex `σ`:

* Lift `σ` through charts: cover `Δ¹` (which is `[0, 1]` up to
  re-parametrization) by finitely many sub-intervals on each of
  which `σ` lands inside a chart `c` (uses compactness of `[0, 1]`
  + open chart sources);
* On each sub-interval, transport `ω` to a 1-form on `c.target ⊆ E`
  via the chart, and apply `curveIntegral`;
* Sum the contributions.

Path-independence (modulo periods) requires showing the result is
the same for any chart-cover refinement and for any homotopy
fixing endpoints.

### Approach for (3): periodSubgroup

Define `periodSubgroup X` as the image of the pairing constructed
in (2). Its closedness in the dual would follow from finiteness of
`H₁` (compact ⇒ finitely generated) and continuity of the pairing.

## Major gaps

* The chart-local lift in (2) is the largest piece of new
  infrastructure. It involves: re-parameterization of paths,
  compactness arguments, and a transport-along-chart lemma for
  1-forms.
* Closed-form invariance (Stokes on a chain) needs more than
  Mathlib currently has on manifolds.
* The full-lattice property of `periodSubgroup` needs Riemann
  bilinear / Hodge input — this is not a small final check.

## First Aristotle-sized packets (when queue unblocks)

1. **`Jacobian/Periods/PathIntegralChart.lean`** — given a chart
   `c : OpenPartialHomeomorph X E` and a 1-form `ω`, define the
   path integral of `ω` along a path that lands inside the chart.
   ~30–50 lines, uses `curveIntegral` directly.
2. **`Jacobian/Periods/PathIntegral.lean`** — extend (1) to paths
   that may cross chart boundaries via a finite chart cover and
   compactness.
3. **`Jacobian/Periods/IntegralOneCycle.lean`** — `IntegralOneCycle X`
   as `H₁(X, ℤ)` from `singularHomologyFunctor` (or a local
   wrapper).
4. **`Jacobian/Periods/PeriodFunctional.lean`** — assemble the
   pairing `IntegralOneCycle X →+ HolomorphicOneFormDual X`.
5. **`Jacobian/Periods/PeriodSubgroup.lean`** — define
   `periodSubgroup X` and state (proof deferred):
   `IsClosed periodSubgroup`, the full-lattice property.

## Anti-hack considerations

`periodSubgroup` must be the genuine period image, not the trivial
subgroup. Without nondegeneracy of the period pairing, the image
could collapse to `{0}`, which would falsify `pushforward_pullback`
through degree zero.

## Recommended next milestone

Get **(1)** and **(3)** in place independently. They have disjoint
write scopes and unlock the rest of the chain. Both are
Aristotle-friendly once the queue unblocks, and (1) is small enough
to land locally if needed.
-/

namespace JacobianChallenge.Periods

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.Periods
