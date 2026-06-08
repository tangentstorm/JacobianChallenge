# Worker jc0 — Milestone C1.5a: correct finite-pole target coordinate normal form

## Assignment

Execute a smaller prerequisite step before retrying C1.5. The rejected C1.5
attempt exposed that the current finite-pole branch of
`onePointSimplePoleCoordinate` is not the continuous target coordinate at
`∞`: for `Q = (a : ℂ)`, it currently evaluates the generic `getD 0` formula at
`∞`, giving `(-a)⁻¹` instead of the correct limiting value `0`.

Change the finite-pole branch of
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` so it explicitly
handles `∞` by `0`, for example by using
`x.elim 0 (fun z => if z = a then 0 else (z - a)⁻¹)`.

Then add small sorry-free local normal-form lemmas for the explicit coordinate:
evaluation at `∞`, evaluation at a finite pole, and evaluation at finite
off-pole points. This task is only the coordinate correction plus basic
supporting lemmas; do not attempt to prove the target-side simple-pole field
facts or move the #234 frontier in this commit.

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

- [x] Confirm `.sci/plan.md` marks reverted C1.5 unchecked and lists C1.5a as
      the next unchecked milestone.
- [x] Inspect the current `onePointSimplePoleCoordinate` definition and nearby
      provider stack in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- [x] Change the finite-pole coordinate branch so `∞` maps to `0` and finite
      values are `if z = a then 0 else (z - a)⁻¹`.
- [x] Add sorry-free normal-form/evaluation lemmas for the infinite-pole
      coordinate, finite-pole coordinate at `∞`, finite-pole coordinate at the
      pole, and finite-pole coordinate away from the pole.
- [x] Keep the C1.4 field-facts provider as the sole reachable #234 root; do
      not replace it with target/source transport providers in this step.
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
  with existing `uses sorry` warnings at the field-facts provider and
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root remains
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
- `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:
  no axiom/unsafe declarations; only the expected two real `sorry`s in this
  file plus explanatory comments.
