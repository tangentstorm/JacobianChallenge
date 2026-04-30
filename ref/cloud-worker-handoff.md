# Cloud Worker Handoff Plan (Blueprint Nodes)

This document is the operational handoff for less-capable agents.
For each node: implement *only* the file listed, keep theorem name stable,
and satisfy the acceptance check.

## Sec02

### `Jacobian/Blueprint/Sec02/AnalyticGenusDef.lean`
- **Target statement**: `analytic_genus` should become a wrapper around `JacobianChallenge.HolomorphicForms.analyticGenus`.
- **Implementation shape**: `noncomputable def analytic_genus ... : ℕ := JacobianChallenge.HolomorphicForms.analyticGenus ℂ X`.
- **Acceptance**: no placeholder `0`; compiles with manifold assumptions.

### `.../FdHolomorphicOneFormsThm.lean`
- **Target statement**: theorem asserting finite-dimensionality of holomorphic one-forms.
- **Bridge**: `JacobianChallenge.HolomorphicForms.compactRiemannSurface_finiteDimensionalHolomorphicOneForms`.
- **Acceptance**: theorem statement uses `FiniteDimensional ℂ (HolomorphicOneForm ℂ X)`.

### `.../GenusZeroClassification.lean`
- **Target statement**: genus-zero iff sphere/homeomorphic one-point compactification variant.
- **Bridge**: `JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere`.
- **Acceptance**: no `True` placeholder.

## Sec03

### `.../PeriodPairing.lean`
- **Target statement**: definition as additive map from cycle group to dual space.
- **Bridge**: `JacobianChallenge.Periods.periodPairing`.
- **Acceptance**: no `Unit`; type mentions additive hom.

### `.../PeriodLattice.lean`
- **Target statement**: image of period pairing is full lattice.
- **Bridge**: `JacobianChallenge.Periods.periodFullComplexLattice`.
- **Acceptance**: theorem mentions lattice/discrete+spanning property.

### `.../PeriodVectorsFullRealRank.lean`
- **Target statement**: period vectors are full real rank.
- **Bridge**: `JacobianChallenge.Periods.period_vectors_linearIndependent_of_symplectic`.
- **Acceptance**: theorem statement not `True`.

## Sec04

### `.../AnalyticJacobian.lean`
- **Target statement**: Jacobian as quotient torus.
- **Bridge**: `JacobianChallenge.AnalyticJacobian.AnalyticJacobianType` and `Jacobian`.
- **Acceptance**: no `Unit` placeholder.

## Sec05

### `.../AbelJacobiDef.lean`
- **Target statement**: map `X → Jacobian X` with basepoint parameter.
- **Bridge**: `Jacobian.ofCurve` or `JacobianChallenge.AbelJacobi.analyticOfCurve`.
- **Acceptance**: no `Unit` placeholder.

### `.../AbelJacobiInjective.lean`
- **Target statement**: injectivity under positive genus.
- **Bridge**: `Jacobian.ofCurve_inj`.
- **Acceptance**: theorem uses `Function.Injective` in statement.

### `.../AbelPointSeparation.lean`
- **Target statement**: period functionals separate points.
- **Bridge**: `JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points`.
- **Acceptance**: no `True` placeholder.

### `.../AjDivisorHom.lean`
- **Target statement**: Abel-Jacobi respects divisor addition.
- **Bridge**: compositional lemmas in `Jacobian/AbelJacobi/*.lean`.
- **Acceptance**: additive-hom statement form.

## Sec06

### `.../TracePullback.lean`
- **Target statement**: `tr_f(f^*η)=deg(f)•η`.
- **Bridge**: `JacobianChallenge.TraceDegree.analyticPushforward_analyticPullback`.
- **Acceptance**: theorem statement explicitly contains `•` and degree.

### `.../PushPullFunctoriality.lean`
- **Target statement**: descended maps holomorphic + id/comp laws.
- **Bridge**: `Jacobian.pushforward_contMDiff`, `pushforward_id_apply`, `pushforward_comp_apply`, `pullback_contMDiff`, `pullback_id_apply`, `pullback_comp_apply`.
- **Acceptance**: theorem statement includes at least one identity and one composition law.

### `.../PushforwardPullback.lean`
- **Target statement**: `f_*(f^*P)=deg(f)•P`.
- **Bridge**: `Jacobian.pushforward_pullback`.
- **Acceptance**: no `True` placeholder.

## Sec07

### `.../ChallengeApi.lean`
- **Target statement**: aggregate proposition bundling final API members.
- **Bridge**: declarations in `Jacobian/Challenge.lean`.
- **Acceptance**: replace trivial theorem with conjunction/structure listing key declarations.
