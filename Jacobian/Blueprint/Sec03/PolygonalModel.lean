/-! # Blueprint stub: `thm:polygonal-model`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

A compact connected oriented Riemann surface `X` of genus `g` is
homeomorphic to a `4g`-gon `P` with sides identified in the standard
pattern `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_gb_ga_g⁻¹b_g⁻¹`, inducing the symplectic
basis on `H₁`.

## Status

**DECOMPOSE placeholder** per `ref/scope-out.md`. Sub-leaves the
follow-up worker should factor out:

* triangulation of a compact orientable surface,
* cut-along-cycles construction,
* fundamental polygon identification with the `4g`-gon glued in
  standard symplectic pattern.

Mathlib v4.28.0 has none of these as a packaged theorem; this is the
classical-topology side of Sec03's bookkeeping.

The conclusion is stated as `True` and the proof is `trivial`; the
declaration name exists today so the blueprint dep-graph can pin
`\lean{...}` and downstream Sec03 nodes (`primitive-on-polygon`,
`bilinear-from-stokes`) can record their dependency on it. The body
will be replaced with the real conclusion once the upstream
classical-topology API lands.

Imports: intentionally Mathlib-free, mirroring the Sec02
`BranchedDegree.lean` / `InputDegreeOneIsomorphism.lean` placeholder
pattern. -/

namespace JacobianChallenge.Blueprint

/-- **DECOMPOSE placeholder.** Polygonal model of a compact connected
oriented Riemann surface of genus `g`: homeomorphism with the
standard `4g`-gon under symplectic side identification. -/
theorem polygonal_model : True := trivial

end JacobianChallenge.Blueprint
