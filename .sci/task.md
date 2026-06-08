# Worker jc0 — Milestone C1.5j: prove target meromorphicity helper

## Assignment

Execute one target-side support proof for C1.5. After C1.5i removed the target
order-one field from the remaining #234 provider, the only target field still
carried by `BiholomorphOnePointSimplePolePullbackFieldFacts` is target
meromorphicity:

```lean
∀ q : OnePoint ℂ,
  JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
    (onePointSimplePoleCoordinate Q) q
```

Prove a local sorry-free helper in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:

```lean
theorem meromorphicAtX_onePointSimplePoleCoordinate
    (Q : OnePoint ℂ) :
    ∀ q : OnePoint ℂ,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        (onePointSimplePoleCoordinate Q) q
```

Use the existing explicit coordinate normal forms. For `Q = ∞`, reduce to the
finite projection `x.getD 0` in the `OnePoint ℂ` charts. For `Q = (a : ℂ)`,
split the local point `q`; away from the finite pole reduce locally to the
holomorphic function `(z - a)⁻¹` or the constant `0` near `∞`, and at the pole
use the inversion/local-coordinate normal form already used by the target
order-one proof.

This is a support-proof commit only. Do not thread the helper into
`BiholomorphOnePointSimplePolePullbackFieldFacts` yet, do not remove
`target_meromorphic_everywhere` from the provider in this step, and do not
attempt any source transport field.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve public theorem names and signatures, especially
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not introduce new sorries, axioms, or unsafe declarations.
- Do not route through the circular fixed-pole/Riemann--Roch chain:
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Checklist

- [x] Confirm `.sci/plan.md` marks C1.5i complete and lists C1.5/C1 as the
      next C1 proof work.
- [x] Inspect the local definitions of
      `MeromorphicAtX`, `onePointSimplePoleCoordinate`, the `onePointExtend`
      normal forms, and the chart-local helpers used by
      `mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole`.
- [x] Prove any narrowly scoped chart-local meromorphicity helpers needed for
      the `Q = ∞` branch.
- [x] Prove any narrowly scoped chart-local meromorphicity helpers needed for
      the finite-pole branch away from and at the pole.
- [x] Add the public local helper
      `meromorphicAtX_onePointSimplePoleCoordinate`.
- [x] Keep the five-field provider as the sole reachable #234 root; do not
      remove `target_meromorphic_everywhere` from the provider in this step.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      remains
      `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`
      with no net new reachable sorries.
- [x] Run
      `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`
      and confirm no new axiom/unsafe declarations and only the expected real
      sorries in this file.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds
  with existing `uses sorry` warnings at the five-field provider and
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root remains
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
- `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:
  no axiom/unsafe declarations; only the expected two real `sorry`s in this
  file plus explanatory comments.
