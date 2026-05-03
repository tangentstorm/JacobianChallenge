/-! # Blueprint stub: `thm:hermitian-positivity`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

For a nonzero holomorphic 1-form `ω` on a compact Riemann surface,
```
i ∫_X ω ∧ ω̄ > 0.
```

## Status

**MEDIUM placeholder** per `ref/scope-out.md`. Once
`thm:bilinear-from-stokes` reduces the RHS to a symplectic-basis sum
of period products, the conclusion follows from local positivity of
the Hermitian wedge `i · h(z)·h(z̄) · dz ∧ dz̄ = |h(z)|² · dx ∧ dy`
in any chart, integrated over `X` (positive integrand on a positive
measure).

Sub-leaf the follow-up worker should factor out:

* local positivity of `i · ω ∧ ω̄` in a chart for nonzero `ω`
  (purely a chart computation, no manifold-with-corners API needed),
* the chart-positive-integrand integrates to a positive number on
  the support, then add up over a finite atlas.

The conclusion is stated as `True` and the proof is `trivial`; the
declaration name exists today so the blueprint dep-graph can pin
`\lean{...}` and `input:riemann-bilinear` can record its dependency
on it.

Imports: intentionally Mathlib-free. -/

namespace JacobianChallenge.Blueprint

/-- **MEDIUM placeholder.** Hermitian positivity of the
self-pairing of a nonzero holomorphic 1-form: `i · ∫_X ω ∧ ω̄ > 0`. -/
theorem hermitian_positivity : Nonempty Unit := ⟨()⟩

end JacobianChallenge.Blueprint
