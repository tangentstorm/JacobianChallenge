/-! # Blueprint stub: `thm:bilinear-from-stokes`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

For holomorphic one-forms `ω, η` on `X`,
```
∫_X ω∧η = Σ_{i=1}^g ((∫_{a_i} ω)·(∫_{b_i} η) − (∫_{b_i} ω)·(∫_{a_i} η))
```
expressing the Riemann bilinear identity as a symplectic-basis sum
of period products, derived by Stokes' theorem applied on the
polygonal model.

## Status

**DECOMPOSE placeholder** per `ref/scope-out.md`. Sub-leaves the
follow-up worker should factor out:

* `thm:stokes-on-rs-with-boundary` (already a DECOMPOSE umbrella in
  `Sec03/StokesOnRSWithBoundary.lean`, awaiting manifold-with-corners
  Stokes API);
* `lem:primitive-on-polygon` (already stubbed in
  `Sec03/PrimitiveOnPolygon.lean`);
* `thm:polygonal-model` (already stubbed in
  `Sec03/PolygonalModel.lean`) — identifies the polygon with the
  surface and reads off the symplectic-basis side identifications;
* assembly: cut-along-symplectic-basis + apply Stokes + sum the side
  contributions.

The conclusion is stated as `True` and the proof is `trivial`; the
declaration name exists today so the blueprint dep-graph can pin
`\lean{...}` and `thm:hermitian-positivity` /
`input:riemann-bilinear` can record their dependency on it.

Imports: intentionally Mathlib-free. -/

namespace JacobianChallenge.Blueprint

/-- **DECOMPOSE placeholder.** Bilinear identity from Stokes on the
polygon: `∫_X ω∧η` equals the symplectic-basis sum of period
products. -/
theorem bilinear_from_stokes : Nonempty Unit := ⟨()⟩

end JacobianChallenge.Blueprint
