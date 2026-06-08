# Worker jc0 — Milestone C1.5b: expose target one-point extension normal forms

## Assignment

Execute a narrow support step for C1.5. After C1.5a corrected
`onePointSimplePoleCoordinate`, add sorry-free local lemmas describing the
associated one-point extension
`onePointExtend (onePointSimplePoleCoordinate Q) Q`.

The goal is to make the target-side continuity/order proof tractable without
moving the #234 frontier yet. Prove definitional normal forms for the extension
at the pole and away from the pole, split into the two target cases
`Q = ∞` and `Q = (a : ℂ)`. In particular, record that:

- at the pole, the one-point extension takes value `∞`;
- for `Q = ∞`, finite points map to their usual finite coordinate;
- for `Q = (a : ℂ)`, `∞` maps to `0`, the finite pole maps to `∞` through the
  extension, and finite off-pole points map to `(z - a)⁻¹`.

This is a Lean-code support commit only. Do not attempt to prove the full
target-side `HasComplexSimplePolePrincipalPart`, do not split or replace the
C1.4 field-facts provider, and do not move the reachable #234 root in this
step.

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

- [x] Confirm `.sci/plan.md` marks C1.5a complete and lists C1.5b/C1.5 as the
      next C1 support/proof work.
- [x] Inspect `onePointExtend`, `onePointSimplePoleCoordinate`, and the C1.4
      field-facts provider in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- [x] Add sorry-free `[simp]`/normal-form lemmas for
      `onePointExtend (onePointSimplePoleCoordinate (∞ : OnePoint ℂ)) ∞` at
      the pole and finite target points.
- [x] Add sorry-free `[simp]`/normal-form lemmas for
      `onePointExtend (onePointSimplePoleCoordinate ((a : ℂ) : OnePoint ℂ))
      ((a : ℂ) : OnePoint ℂ)` at `∞`, at the finite pole, and at finite
      off-pole points.
- [x] Keep the C1.4 field-facts provider as the sole reachable #234 root; do
      not introduce target/source provider splits in this step.
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
