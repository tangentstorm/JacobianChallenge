# Worker jc0 — Milestone C1.5h: prove target coordinate order-one helper

## Assignment

Execute one target-side support proof for C1.5. After C1.5g discharged the
target modulus-divergence field from the remaining #234 provider, prove a local
sorry-free helper in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:

```lean
theorem mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole
    (Q : OnePoint ℂ) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
      (onePointExtend (onePointSimplePoleCoordinate Q) Q) Q = 1
```

Use the existing target extension normal forms. For `Q = ∞`, reduce the
one-point extension to `id` and prove order one in the infinity chart. For
`Q = (a : ℂ)`, use the finite-pole extension normal form as
`onePointSphereInversion ∘ OnePoint.map (fun z : ℂ => z - a)` and prove the
local order is one at `↑a` by reducing to the standard local coordinate.

If needed, add small local sorry-free helper lemmas for the exact chart/order
translation on `OnePoint ℂ`, but keep them scoped to this target coordinate.

This is a Lean-code support commit for one target field only. Do not thread the
helper into `BiholomorphOnePointSimplePolePullbackFieldFacts` yet. Do not
attempt to prove target meromorphicity or any source transport field in this
step, and do not move the reachable #234 root.

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

- [x] Confirm `.sci/plan.md` marks C1.5g complete and lists C1.5h/C1.5 as the
      next C1 support/proof work.
- [x] Inspect the definitions and local API for
      `mapAnalyticOrderAt`, `onePointExtend`, `onePointSimplePoleCoordinate`,
      `onePointExtend_onePointSimplePoleCoordinate_infty_eq_id`, and
      `onePointExtend_onePointSimplePoleCoordinate_coe_eq_comp`.
- [x] Inspect the relevant `OnePoint ℂ` chart/inversion order lemmas already in
      `MeromorphicToBranchedCover.lean`, `OnePointCxChartedSpace.lean`, and
      local analytic-order files before adding any helper.
- [x] Prove the `Q = ∞` order-one case.
- [x] Prove the finite-pole order-one case, adding only narrowly scoped
      sorry-free helper lemmas if needed.
- [x] Add the public local helper
      `mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole`.
- [x] Keep the six-field provider as the sole reachable #234 root; do not
      remove `target_orderAt_pole` from the provider in this step.
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
  with existing `uses sorry` warnings at the six-field provider and
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root remains
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
- `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:
  no axiom/unsafe declarations; only the expected two real `sorry`s in this
  file plus explanatory comments.
