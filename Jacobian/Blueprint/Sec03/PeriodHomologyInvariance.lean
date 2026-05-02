import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.PeriodFunctional
import Jacobian.Blueprint.Sec03.HolomorphicFormIsClosed
import Jacobian.Blueprint.Sec03.StokesOnRSWithBoundary

/-! # Blueprint stub: `lem:period-homology-invariance`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

> If `γ` and `γ'` represent the same class in `H₁(X, ℤ)`, then
> `∫_γ ω = ∫_{γ'} ω` for every `ω ∈ H⁰(X, Ω¹)`.

## Status

**Two-layer stub (this file).** The lemma is given two complementary
formalisations, both depending on the exact same Mathlib blockers
(closed forms + Stokes), but at different abstraction levels.

* `period_homology_invariance` is the **typed** form. In the
  production typing `IntegralOneCycle X = H₁(X, ℤ)` (built from
  Mathlib's `singularHomologyFunctor` in
  `Jacobian/Periods/IntegralOneCycle.lean`), so two cycles
  representing the same class are *equal* in this type, and the
  conclusion of the lemma is a one-line `congrArg`.

  The hard mathematical content is *not* visible at this level: it
  was paid up-front when `periodPairing` was given the type
  `IntegralOneCycle X →+ ...` (rather than the chain-level type).
  That construction obligation lives in `period_homology_invariance_descent`.

* `period_homology_invariance_descent` is the **descent** form. It
  records the obligation that `periodPairing` is the homology descent
  of a chain-level integration, i.e. there exists a ℤ-linear map on
  singular 1-chains whose composition with `∂₂` vanishes and whose
  induced map on `H₁` is `periodPairing`. This is the form that
  surfaces the closed-forms + Stokes content.

## Blockers (Mathlib v4.28.0, commit `8f9d9cff…`)

1. **Path integration over singular 1-simplices.** Chart-local path
   integral `pathIntegralChart` exists
   (`Jacobian/Periods/PathIntegralChart.lean`); multi-chart wrapper
   `pathIntegralViaCoverWith` is partial
   (`Jacobian/Periods/PathIntegralViaCover.lean`). Linearity in the
   path/chain and well-definedness across partitions are in-progress.

2. **Holomorphic 1-forms are closed** (`dω = 0`):
   `lem:holomorphic-form-is-closed`, currently a `True` placeholder
   in `Jacobian/Blueprint/Sec03/HolomorphicFormIsClosed.lean` pending
   a manifold-side exterior-derivative API.

3. **Stokes' theorem on a 2-manifold with boundary**:
   `thm:stokes-on-rs-with-boundary`, eight-leaf decomposition in
   `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` (every
   non-trivial leaf currently `sorry` or `True`).

The combination (2)+(3) gives `chainIntegral ∘ ∂₂ = 0` on 2-chains,
which is exactly the descent hypothesis: integrating a closed form
over the boundary of a 2-chain is zero.

## Proof sketch (eventual real proof)

For singular 1-chains `c, c'` with `c - c' = ∂₂ Σ` for some 2-chain
`Σ`, write
```
∫_{c - c'} ω = ∫_{∂Σ} ω = ∫_Σ dω = 0,
```
using linearity of the chain integral, Stokes (3), and closedness (2)
in turn. Hence `∫_c ω = ∫_{c'} ω`.

Imports: `HolomorphicForms.Defs` (`HolomorphicOneForm`),
`Periods.IntegralOneCycle` (`IntegralOneCycle = H₁(X, ℤ)`),
`Periods.PeriodFunctional` (`periodPairing`), and the two blueprint
sub-leaf stubs we depend on.
-/

namespace JacobianChallenge.Blueprint.Sec03

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/-- **`lem:period-homology-invariance` (typed form).**

If `σ` and `τ` are integral 1-cycles representing the same class in
`H₁(X, ℤ)`, then `∫_σ ω = ∫_τ ω` for every holomorphic 1-form `ω`.

In the production typing, `IntegralOneCycle X` is *definitionally*
`H₁(X, ℤ)` (the degree-1 singular homology with ℤ coefficients,
from `Mathlib.AlgebraicTopology.SingularHomology.Basic`), so two
cycles representing the same homology class are equal as elements
of this type and the conclusion is `congrArg`.

The descent obligation that *justifies* the typing —
`periodPairing` as the homology descent of a chain-level
integration — is `period_homology_invariance_descent`. -/
theorem period_homology_invariance
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ τ : IntegralOneCycle X} (h : σ = τ)
    (ω : HolomorphicOneForm ℂ X) :
    (periodPairing ℂ X) σ ω = (periodPairing ℂ X) τ ω := by
  rw [h]

/-- **`lem:period-homology-invariance` (descent form, named blocker).**

The mathematical content of homology invariance: there exists a
chain-level integration of holomorphic 1-forms along singular
1-chains whose restriction to cycles descends through homology to
the period pairing. Concretely (eventual statement when the API
lands):

```
∃ chainIntegral :
    ((singularChainComplex (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)).obj X).X 1
      →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ),
  -- (a) chain-level linearity (built-in to →+);
  -- (b) chainIntegral ∘ ∂₂ = 0 — Stokes + dω = 0;
  -- (c) the homology descent of chainIntegral equals periodPairing.
```

While the chain-level differential-form integration API is absent
(see file docstring blockers 1–3), this declaration carries the
descent obligation as a `True`-placeholder so the blueprint
dep-graph picks up the `\lean{…}` annotation and downstream
consumers (the proof of `period_homology_invariance` once it is
strengthened to a non-tautological form) can name the obligation.

Once Mathlib gains the manifold-side exterior derivative + Stokes,
swap the conclusion for the real `∃ chainIntegral, …` statement
above; the proof body will then be an honest assembly of
`lem:holomorphic-form-is-closed` and
`thm:stokes-on-rs-with-boundary`. -/
theorem period_homology_invariance_descent
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    True := by
  trivial

end JacobianChallenge.Blueprint.Sec03
