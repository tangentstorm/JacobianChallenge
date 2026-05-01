/-! # Blueprint stub: `lem:principal-deg0-simple-support-deg1`

Section 5 of `tex/sections/05-abel-jacobi-map.tex`.

If `f ∈ Mer(X)^{×}` has principal divisor `(f) = Q₁ - Q₂` with
`Q₁ ≠ Q₂`, then the associated map `f̂ : X → ℂP¹` is nonconstant of
degree 1.

## Status

**SHORT placeholder.** The combinatorial reduction (deg = 0 + two-point
support of size 2 with ℤ-coefficients ⇒ one `+1` and one `-1`) is
trivial once the divisor / vanishing-order / degree-of-meromorphic-map
APIs land. Today those upstream pieces are still scaffolds:

* `JacobianChallenge.Blueprint.principalDivisor` returns `0` as a
  placeholder (see `Jacobian/Blueprint/Sec01/PrincipalDivisor.lean`);
* `MeromorphicFunctionType` is `X → OnePoint ℂ` (placeholder, see
  `Jacobian/Blueprint/Sec01/MeromorphicFunction.lean`);
* the degree of a holomorphic map to `ℂP¹` is not yet defined at the
  blueprint level.

So the conclusion is stated as `True` and the proof is `trivial`. The
declaration name exists today so the blueprint dep-graph node can pin
`\lean{}` on it; the body will be replaced with the real conclusion
once the upstream APIs land.

## Replacement target (sketch)

```
theorem principal_deg0_simple_support_deg1
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    Nonconstant (meromorphicToCp1 X f) ∧
    branchedDegree (meromorphicToCp1 X f) = 1 := by
  -- (deg = 0 of LHS, RHS = 1 + (−1) at distinct points) ⇒ done.
  sorry
```

This file is intentionally Mathlib-free, mirroring the Sec02
placeholder pattern (`InputDegreeOneIsomorphism.lean`,
`BranchedDegree.lean`). -/

namespace JacobianChallenge.Blueprint

/-- **SHORT placeholder.** Principal divisor of degree zero with
simple two-point support yields a degree-one map.

Replacement target: see file docstring. Returns `True` so the
blueprint dep-graph node has a resolvable `\lean{}` target without
committing to a specific bundle of `Nonconstant`/`branchedDegree`
APIs upstream of the children. -/
theorem principal_deg0_simple_support_deg1 : True := trivial

end JacobianChallenge.Blueprint
