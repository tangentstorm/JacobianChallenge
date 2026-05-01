/-! Blueprint stub: `lem:principal-deg0-simple-support-deg1` in
`tex/sections/05-abel-jacobi.tex` (sec05 row of `ref/scope-out.md`,
classified **SHORT**).

Combinatorial lemma: a degree-zero divisor with two-point support
and integer coefficients has coefficients of opposite sign and
equal absolute value. The "deg-1" specialisation (used downstream
in `thm:abel-point-separation` to reduce to the case
`D = [p] - [q]`) is the case `|m| = |n| = 1`.

Per the SHORT-class sketch in `ref/scope-out.md`:

> degree=0 + 2-point support + Z-coefficients ⇒ one +1, one -1

We model the two-point support directly as a pair of `Int`-valued
coefficients on two distinct points; the lemma is a one-step
linear-arithmetic fact. No Mathlib import is needed; core Lean's
`Int` and `omega` decision procedure suffice.

## Conventions

* No Mathlib imports — pure Lean arithmetic.
* Helpers live in the nested namespace
  `JacobianChallenge.Blueprint.AbelExistence.PrincipalDeg0SimpleSupportDeg1`. -/

namespace JacobianChallenge.Blueprint
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
