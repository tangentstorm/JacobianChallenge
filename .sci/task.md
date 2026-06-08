# Worker jc0 — Milestone C1.4: expose simple-pole principal-part field facts

## Assignment

Execute C1.4 from `.sci/plan.md`: replace the remaining #234 facts-provider
`sorry` with a narrower provider that exposes the exact field-level obligations
needed to build `HasComplexSimplePolePrincipalPart` for both the explicit target
coordinate and the pulled-back source coordinate.

Add a local structure in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, for example
`BiholomorphOnePointSimplePolePullbackFieldFacts`, whose fields are the concrete
components of the two principal-part predicates:

- for `onePointSimplePoleCoordinate (e P)` at `e P`:
  meromorphic everywhere, continuous one-point extension, order one, and
  punctured-neighborhood modulus divergence;
- for `biholomorphPulledBackSimplePoleCoordinate P e` at `P`:
  meromorphic everywhere, continuous one-point extension, order one, and
  punctured-neighborhood modulus divergence.

Then add a named provider returning `Nonempty` of this field-facts structure
with the single remaining `sorry`, and prove
`biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` by
assembling the two `HasComplexSimplePolePrincipalPart` records from those
fields.

This is a Lean-code commit. It should not prove the analytic field facts yet;
it should make the remaining #234 frontier strictly narrower by exposing the
eight concrete proof obligations instead of hiding them inside bundled
principal-part predicates.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve public theorem names and signatures, especially
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not add more than one new `sorry`; the new field-facts provider must
  replace the existing
  `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` `sorry`,
  not add a second reachable gap.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Checklist

- [x] Confirm `.sci/plan.md` marks C1.3 complete and lists C1.4 as the next
      unchecked milestone.
- [x] Inspect `HasComplexSimplePolePrincipalPart`,
      `BiholomorphOnePointSimplePolePullbackFacts`, and the current facts
      provider.
- [x] Add the field-facts structure carrying the four target fields and four
      source fields needed for `HasComplexSimplePolePrincipalPart`.
- [x] Add the named field-facts provider with exactly one `sorry`, documenting
      it as the remaining explicit-coordinate analytic frontier.
- [x] Replace the body of
      `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` with
      sorry-free assembly of the target and source principal-part records from
      the field facts.
- [x] Keep `BiholomorphOnePointSimplePolePullbackData`,
      `complexSimplePolePrincipalPart_of_biholomorph_onePoint`, and downstream
      `singlePoleAnalyticData_of_biholomorph_onePoint` unchanged except for any
      name drift forced by the provider replacement.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      moved to the new field-facts provider, with no net new reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds;
  this file now has warnings at
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint` and
  the existing `genusZeroHomeomorphOnePoint_of_analyticGenus_zero` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry`
  warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root moved to
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
