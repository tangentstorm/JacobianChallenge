import Jacobian.AnalyticJacobian
import Jacobian.Periods

/-!
# Reconnaissance: the Abel-Jacobi map

Queue F kickoff. This is a name-discovery and design document for
the Abel-Jacobi map needed by `Jacobian/Challenge.lean`'s
`Jacobian.ofCurve` API.

Like the earlier `*/Recon.lean` files, this contains no production
declarations beyond a stub token; it is not re-exported by any
umbrella.

## Phase context

Queue C provides `HolomorphicOneForm E X`, its module structure,
and `analyticGenus`. Queue D provides chart-local path integration,
the integral 1-cycle type, and an opaque period pairing. Queue E
provides the abstract group quotient `AnalyticJacobianGroup E X`.

The next bridge is the Abel-Jacobi map:

```text
analyticOfCurve : (P : X) → X → AnalyticJacobianGroup E X
```

defined by `Q ↦ [ω ↦ ∫_P^Q ω] mod periodSubgroup`.

## Mathematical content

For each pair `P, Q : X` and each holomorphic 1-form `ω`, integrate
`ω` along *some* path from `P` to `Q`. The result depends on the
chosen path, but two different paths from `P` to `Q` give answers
that differ by an element of the period subgroup (homology of the
loop traced by going `P → Q` along one path then back along the
other). So the value mod periodSubgroup is well-defined.

## What is needed (gaps)

1. **Multi-chart path integration** (Queue D bottleneck). Without
   this, `pathIntegralFunctional P Q ω` cannot be defined for
   general `P, Q`.

2. **Path-existence in compact connected manifolds.** Mathlib has
   `PathConnectedSpace`; a compact connected manifold is path-
   connected (TODO: confirm whether mathlib has this lemma; if not,
   it is a small bridge from local-path-connectedness via charts +
   `IsLocallyPathConnected.connected_iff`).

3. **Path-independence modulo periods.** This is essentially the
   statement that the period pairing factors through `H₁(X, ℤ)`.
   Once `pathIntegralFunctional` is defined as a real function and
   `periodSubgroup` is the genuine range, the well-definedness is
   automatic (the difference of two paths is a 1-cycle, which goes
   to a period).

4. **`analyticOfCurve_self : analyticOfCurve P P = 0`.** The constant
   path from `P` to `P` integrates to `0` (refl/trivial path). With
   `pathIntegralInChart_refl` already in place, this should be a
   small lemma once the multi-chart integral lands.

5. **`analyticOfCurve_contMDiff`.** Smoothness of the Abel-Jacobi
   map. Needs the Jacobian's manifold structure (deferred) and
   smooth-dependence of `pathIntegralFunctional` on its endpoint
   (a calculus-of-1-forms lemma).

6. **`analyticOfCurve_injective` for positive genus.** This is the
   anti-hack theorem `ofCurve_inj`. Classical proof uses Abel's
   theorem (a homomorphism `Div⁰(X) → Jac X` with kernel principal
   divisors) — substantial mathematics.

7. **`challenge_ofCurve_eq_analytic`.** Bridge to the public API.
   Needs `analyticJacobianEquivChallenge` (Queue E deferred).

## What can move forward independently

* Define `analyticOfCurve` with the path argument explicit, before
  proving path-independence:
  ```text
  analyticOfCurveAlongPath : Π (γ : Path P Q),
      HolomorphicOneForm E X →ₗ[ℂ] ℂ
  ```
  This is "the period functional restricted to a single path".
  Useful as an intermediate step.

* State `analyticOfCurve_self` for the trivial path even before
  general path-independence: it is automatic from
  `pathIntegralInChart_refl`-style API.

## First Aristotle-sized packets (when queue unblocks)

1. **`Jacobian/AbelJacobi/PathFunctional.lean`** — define
   `analyticOfCurveAlongPath γ ω` for `γ : Path P Q` and
   `ω : HolomorphicOneForm`. Probably opaque (deferred to multi-chart
   integration) for now.
2. **`Jacobian/AbelJacobi/Defs.lean`** — define `analyticOfCurve P Q`
   as the class in `AnalyticJacobianGroup E X` of the path
   functional, picking some path (`Classical.choose` from
   path-connectedness).
3. **`Jacobian/AbelJacobi/SelfZero.lean`** — prove
   `analyticOfCurve P P = 0` using the trivial path.
4. **`Jacobian/AbelJacobi/PathIndependent.lean`** — state
   path-independence as a lemma (the difference of two path
   functionals lies in the period subgroup); proof deferred until
   `pathIntegralFunctional` is non-opaque.

## Anti-hack considerations

`Jacobian.ofCurve_inj` is the strongest of the four anti-hack
theorems: for positive genus, the Abel-Jacobi map must be injective.
A trivial Abel-Jacobi map (e.g. `fun _ => 0`) would violate this.
This is the anchor that ultimately makes Queue F mathematically
non-trivial; we cannot graduate `analyticOfCurve_injective` from
sorry until we have either Abel's theorem or some equivalent
positive-genus theorem.

## Recommendation

Until multi-chart path integration lands, Queue F is in a
"definition-shape" state — we can name the maps and state the
target lemmas, but the proofs all bottleneck on Queue D. After
multi-chart integration:
1. Define `analyticOfCurveAlongPath` and the path functional.
2. Prove `analyticOfCurve_self` (smallest, quickest).
3. Path independence (one-line once periods are real).
4. Smoothness (depends on Jacobian's manifold structure too).
5. Injectivity (the anti-hack theorem; deepest).
-/

namespace JacobianChallenge.AbelJacobi

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.AbelJacobi
