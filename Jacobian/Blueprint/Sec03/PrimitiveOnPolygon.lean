/-! # Blueprint stub: `lem:primitive-on-polygon`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

On the open polygon (interior of `P`) — which is simply connected —
every holomorphic 1-form `ω` has a holomorphic primitive
`F : P° → ℂ` with `dF = ω`.

## Status

**DECOMPOSE placeholder** per `ref/scope-out.md`. Sub-leaf the
follow-up worker should factor out:

* simply-connected-open-subset-of-`ℂ` ⇒ closed-form-has-primitive
  (Mathlib has primitives on simply-connected open subsets of `ℂ`;
  pulling back along the polygonal-model homeomorphism handles the
  manifold side).

The conclusion is stated as `True` and the proof is `trivial`; the
declaration name exists today so the blueprint dep-graph node has a
resolvable `\lean{...}` target. Body to be replaced with the real
existence statement once the polygonal-model homeomorphism API and
the manifold-side primitive-of-closed-form API land.

Imports: intentionally Mathlib-free. -/

namespace JacobianChallenge.Blueprint

/-- **DECOMPOSE placeholder.** Existence of a holomorphic primitive
of a holomorphic 1-form on the simply-connected interior of the
polygonal model. -/
theorem primitive_on_polygon : True := trivial

end JacobianChallenge.Blueprint
