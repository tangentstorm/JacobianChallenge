# Worker jc0 — Milestone C1.5c: package target extension function normal forms

## Assignment

Execute a narrow support step for C1.5. After C1.5b added pointwise normal
forms for
`onePointExtend (onePointSimplePoleCoordinate Q) Q`, package those facts into
whole-function normal forms that later continuity/order proofs can rewrite
with directly.

Add sorry-free local lemmas in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` showing:

- for `Q = ∞`,
  `onePointExtend (onePointSimplePoleCoordinate (∞ : OnePoint ℂ)) ∞ = id`;
- for `Q = (a : ℂ)`, the one-point extension equals the explicit case map
  `fun x => x.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z => if z = a then OnePoint.infty else (((z - a)⁻¹ : ℂ) : OnePoint ℂ))`.

This is a Lean-code support commit only. Do not attempt to prove target-side
continuity, order, meromorphicity, or modulus divergence yet. Do not split or
replace the C1.4 field-facts provider, and do not move the reachable #234 root
in this step.

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

- [x] Confirm `.sci/plan.md` marks C1.5b complete and lists C1.5c/C1.5 as the
      next C1 support/proof work.
- [x] Inspect the C1.5a coordinate lemmas, C1.5b extension pointwise lemmas,
      and the C1.4 field-facts provider in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- [x] Add a sorry-free whole-function identity for the `Q = ∞` extension as
      `id`, proved by extensionality/cases using the C1.5b pointwise lemmas.
- [x] Add a sorry-free whole-function identity for the finite-pole extension as
      the explicit `OnePoint.elim`/`if z = a` case map.
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
