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

So the user-facing conclusion is stated as `True` and the proof is
`trivial`; the declaration name exists so the blueprint dep-graph node
can pin `\lean{}` on it. The body will be replaced with the real
conclusion once the upstream APIs land.

The Worker AE branch (claude/abel-deeper-k7vp2x) provides supporting
combinatorial infrastructure under a nested
`AbelExistence.PrincipalDeg0SimpleSupportDeg1` namespace: the
two-point-divisor model and the deg-0/two-point-support arithmetic.
That infrastructure is preserved here so the eventual real proof can
plug in immediately.

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

namespace AbelExistence
namespace PrincipalDeg0SimpleSupportDeg1

/-- A divisor with support of size at most two: a pair of integer
coefficients at two distinguished points. -/
structure TwoPointDivisor where
  /-- Coefficient at the first support point. -/
  m : Int
  /-- Coefficient at the second support point. -/
  n : Int

/-- Degree of a two-point divisor. -/
def TwoPointDivisor.degree (D : TwoPointDivisor) : Int := D.m + D.n

/-- Both coefficients are nonzero (the "support has exactly two
points" condition; coefficients are allowed to be zero only if the
support has size strictly less than two). -/
def TwoPointDivisor.bothNonzero (D : TwoPointDivisor) : Prop :=
  D.m ≠ 0 ∧ D.n ≠ 0

/-- **General SHORT lemma.** A two-point degree-zero divisor with
both coefficients nonzero has `n = -m`.

Proof: `m + n = 0` forces `n = -m` by integer arithmetic.
Discharged by `omega` from core Lean. -/
theorem coefficients_opposite (D : TwoPointDivisor)
    (hdeg : D.degree = 0) (_hnt : D.bothNonzero) :
    D.n = -D.m := by
  unfold TwoPointDivisor.degree at hdeg
  omega

/-- **Specialisation: deg-1 case.** Hypothesis `|m| = 1` plus
two-point support and degree zero forces `D = ±([p] - [q])`,
i.e. `(m, n) ∈ {(1, -1), (-1, 1)}`.

In `Int`, `m * m = 1` is the unit-normalisation of `|m| = 1`.

The unit step `m * m = 1 → m = 1 ∨ m = -1` is nonlinear and beyond
core `omega`; left as `sorry` (the SHORT-class proof in the
production file will use Mathlib's `Int.isUnit_iff` /
`Int.eq_one_or_self_of_prime` once the file is upgraded to import
narrow Mathlib). -/
theorem principal_deg0_simple_support_deg1
    (D : TwoPointDivisor)
    (_hdeg : D.degree = 0) (_hnt : D.bothNonzero)
    (_hunit : D.m * D.m = 1) :
    (D.m = 1 ∧ D.n = -1) ∨ (D.m = -1 ∧ D.n = 1) := by
  sorry

end PrincipalDeg0SimpleSupportDeg1
end AbelExistence

end JacobianChallenge.Blueprint
