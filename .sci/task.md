# Worker jc0 — Milestone C1.5i: discharge target order field in #234 provider

## Assignment

Execute a narrow provider-tightening step for C1.5. C1.5h proved the target
order-one helper:

```lean
theorem mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole
    (Q : OnePoint ℂ) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
      (onePointExtend (onePointSimplePoleCoordinate Q) Q) Q = 1
```

Use that helper to remove the target order-one obligation from the remaining
#234 field-facts provider in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.

Concretely, update `BiholomorphOnePointSimplePolePullbackFieldFacts` so it no
longer has a `target_orderAt_pole` field. Then update
`biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` so the
target `HasComplexSimplePolePrincipalPart.orderAt_pole` field is filled
directly by
`mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole (e P)`.

This should narrow the reachable #234 frontier from six exposed fields to five
exposed fields. Do not attempt to prove target meromorphicity or any source
transport field in this step, and do not change any public theorem signatures.

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

- [x] Confirm `.sci/plan.md` marks C1.5h complete and lists C1.5i/C1.5 as the
      next C1 support/provider-tightening work.
- [x] Inspect `BiholomorphOnePointSimplePolePullbackFieldFacts`,
      `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`,
      and `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`.
- [x] Remove the `target_orderAt_pole` field from
      `BiholomorphOnePointSimplePolePullbackFieldFacts` and update comments to
      say the provider now carries five remaining fields.
- [x] Fill `targetPrincipalPart.orderAt_pole` from
      `mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole (e P)`.
- [x] Keep the C1.4 field-facts provider as the sole reachable #234 root, but
      with one fewer required target field.
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
