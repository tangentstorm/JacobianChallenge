# Worker jc0 — Milestone C1.5k: discharge target meromorphicity field

## Assignment

Execute a narrow provider-tightening step for C1.5. C1.5j proved the target
meromorphicity helper:

```lean
theorem meromorphicAtX_onePointSimplePoleCoordinate
    (Q : OnePoint ℂ) :
    ∀ q : OnePoint ℂ,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        (onePointSimplePoleCoordinate Q) q
```

Use that helper to remove the final target-side obligation from the remaining
#234 field-facts provider in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.

Concretely, update `BiholomorphOnePointSimplePolePullbackFieldFacts` so it no
longer has a `target_meromorphic_everywhere` field. Then update
`biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` so the
target `HasComplexSimplePolePrincipalPart.meromorphic_everywhere` field is
filled directly by
`meromorphicAtX_onePointSimplePoleCoordinate (e P)`.

This should narrow the reachable #234 frontier from five exposed fields to the
four source transport fields only. Do not attempt to prove any source transport
field in this step, and do not change any public theorem signatures.

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

- [x] Confirm `.sci/plan.md` marks C1.5j complete and lists C1.5/C1 as the
      next C1 proof work.
- [x] Inspect `BiholomorphOnePointSimplePolePullbackFieldFacts`,
      `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`,
      and `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`.
- [x] Remove the `target_meromorphic_everywhere` field from
      `BiholomorphOnePointSimplePolePullbackFieldFacts` and update comments to
      say the provider now carries four source transport fields.
- [x] Fill `targetPrincipalPart.meromorphic_everywhere` from
      `meromorphicAtX_onePointSimplePoleCoordinate (e P)`.
- [x] Keep the C1.4 field-facts provider as the sole reachable #234 root, but
      with only the source transport fields remaining.
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
  with existing `uses sorry` warnings at the four-source-field provider and
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root remains
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
- `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:
  no axiom/unsafe declarations; only the expected two real `sorry`s in this
  file plus explanatory comments.
