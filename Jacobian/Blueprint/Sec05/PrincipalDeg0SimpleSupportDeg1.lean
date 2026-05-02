import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.MeromorphicToCp1

/-! # Blueprint stub: `lem:principal-deg0-simple-support-deg1`

Section 5 of `tex/sections/05-abel-jacobi-map.tex`.

If `f ∈ Mer(X)^{×}` has principal divisor `(f) = Q₁ - Q₂` with
`Q₁ ≠ Q₂`, then the associated map `f̂ : X → ℂP¹` is nonconstant of
degree 1.

## Status

**Real type signature.** The conclusion is stated with the genuine
`Nonconstant` / `branchedDegree` predicates; the proof is `sorry`
because the upstream analytic infrastructure (open-mapping theorem,
`BranchedCoverData` constructor for meromorphic maps) is still
frontier-bound.

The Worker AE branch (claude/abel-deeper-k7vp2x) provides supporting
combinatorial infrastructure under a nested
`AbelExistence.PrincipalDeg0SimpleSupportDeg1` namespace: the
two-point-divisor model and the deg-0/two-point-support arithmetic.
That infrastructure is preserved here so the eventual real proof can
plug in immediately.
-/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The point divisor `[P]`: the divisor assigning coefficient `1` to `P`
and `0` elsewhere. Wraps `Finsupp.single P 1`. -/
noncomputable def Divisor.point {X : Type*} (P : X) : Divisor X :=
  Finsupp.single P 1

/-- A function `g : X → Y` is *nonconstant*: there is no single value
`c : Y` assumed everywhere. -/
def Nonconstant {X Y : Type*} (g : X → Y) : Prop :=
  ¬ ∃ c : Y, ∀ x : X, g x = c

/-- **Placeholder.** The branched degree of a continuous map
`g : X → Y` between compact Riemann surfaces, viewed as a function.

The eventual definition builds a `BranchedCoverData` (see
`Jacobian/Blueprint/Sec02/BranchedDegree.lean`) from the
open-mapping / isolated-zeros theorems and reads off
`BranchedCoverData.branchedDegree`; that analytic constructor is
still frontier-bound, so we leave the body as `0` (an obviously
wrong but type-correct stand-in). -/
noncomputable def branchedDegreeOfMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (_g : X → Y) : ℕ := 0

/-- If `f ∈ Mer(X)^{×}` has principal divisor `(f) = Q₁ - Q₂` with
`Q₁ ≠ Q₂`, then the associated map `f̂ : X → ℂP¹` is nonconstant of
branched degree 1.

The proof requires the analytic `BranchedCoverData` constructor
(open-mapping theorem + isolated zeros ⇒ finite fibres and constant
weighted-fibre count) which is still frontier-bound; accordingly
the body is `sorry`. -/
theorem principal_deg0_simple_support_deg1
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    Nonconstant (meromorphicToCp1 X f) ∧
    branchedDegreeOfMap (meromorphicToCp1 X f) = 1 := by
  sorry

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

In `Int`, `m * m = 1` is the unit-normalisation of `|m| = 1`. The
unit step `m * m = 1 → m = 1 ∨ m = -1` is nonlinear, but a
case analysis combined with `Int.mul_le_mul_of_nonneg_left` and
`Int.neg_mul_neg` bounds `|m| * |m| ≥ 4` whenever `|m| ≥ 2`,
contradicting `m * m = 1`. -/
theorem principal_deg0_simple_support_deg1
    (D : TwoPointDivisor)
    (hdeg : D.degree = 0) (hnt : D.bothNonzero)
    (hunit : D.m * D.m = 1) :
    (D.m = 1 ∧ D.n = -1) ∨ (D.m = -1 ∧ D.n = 1) := by
  have hopp : D.n = -D.m := coefficients_opposite D hdeg hnt
  have hm_unit : D.m = 1 ∨ D.m = -1 := by
    by_cases hpos : 0 < D.m
    · by_cases h1 : D.m = 1
      · exact Or.inl h1
      · exfalso
        have h3 : 2 ≤ D.m := by omega
        have h3' : (0 : Int) ≤ D.m := by omega
        have h4 : D.m * 2 ≤ D.m * D.m :=
          Int.mul_le_mul_of_nonneg_left h3 h3'
        rw [hunit] at h4
        omega
    · by_cases hzero : D.m = 0
      · exfalso
        rw [hzero, Int.zero_mul] at hunit
        omega
      · by_cases hn1 : D.m = -1
        · exact Or.inr hn1
        · exfalso
          have h3 : 2 ≤ -D.m := by omega
          have h3' : (0 : Int) ≤ -D.m := by omega
          have h4 : (-D.m) * 2 ≤ (-D.m) * (-D.m) :=
            Int.mul_le_mul_of_nonneg_left h3 h3'
          have h5 : (-D.m) * (-D.m) = D.m * D.m := Int.neg_mul_neg D.m D.m
          rw [h5, hunit] at h4
          omega
  rcases hm_unit with hpm | hpm
  · refine Or.inl ⟨hpm, ?_⟩
    rw [hopp, hpm]
  · refine Or.inr ⟨hpm, ?_⟩
    rw [hopp, hpm]
    decide

end PrincipalDeg0SimpleSupportDeg1
end AbelExistence

end JacobianChallenge.Blueprint
