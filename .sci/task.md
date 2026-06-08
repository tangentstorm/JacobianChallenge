# Worker jc0 — Milestone C1.5d: prove target extension continuity helper

## Assignment

Execute one target-side support proof for C1.5. After C1.5c packaged the
target one-point extension into whole-function normal forms, prove a local
sorry-free helper in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:

```lean
theorem continuous_onePointExtend_onePointSimplePoleCoordinate
    (Q : OnePoint ℂ) :
    Continuous (onePointExtend (onePointSimplePoleCoordinate Q) Q)
```

Use the existing case split on `Q`. For `Q = ∞`, rewrite with the C1.5c
identity normal form and discharge continuity by continuity of `id`. For
`Q = (a : ℂ)`, use the C1.5c finite-pole normal form and prove the explicit
case map is continuous on `OnePoint ℂ` from local primitives. If needed, add
small local sorry-free continuity lemmas for the finite-pole case map, but keep
them scoped to this target coordinate.

This is a Lean-code support commit for one target field only. Do not attempt to
prove target meromorphicity, order, or modulus divergence in this step. Do not
split or replace the C1.4 field-facts provider, and do not move the reachable
#234 root yet.

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

- [x] Confirm `.sci/plan.md` marks C1.5c complete and lists C1.5d/C1.5 as the
      next C1 support/proof work.
- [x] Inspect the C1.5c whole-function normal forms and available continuity
      facts for `OnePoint ℂ` maps in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- [x] Prove the `Q = ∞` continuity case by rewriting the extension to `id`.
- [x] Prove the finite-pole continuity case, adding only narrowly scoped
      sorry-free helper lemmas if needed.
- [x] Add the public local helper
      `continuous_onePointExtend_onePointSimplePoleCoordinate`.
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
