# Worker jc0 — Milestone C1.5f: prove target modulus divergence helper

## Assignment

Execute one target-side support proof for C1.5. After C1.5e discharged the
target continuity field from the remaining #234 provider, prove a local
sorry-free helper in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:

```lean
theorem tendsto_norm_onePointSimplePoleCoordinate_atTop
    (Q : OnePoint ℂ) :
    Filter.Tendsto (fun q => ‖onePointSimplePoleCoordinate Q q‖)
      (nhdsWithin Q ({Q}ᶜ : Set (OnePoint ℂ))) Filter.atTop
```

Use the existing case split on `Q`. For `Q = ∞`, use the normal form
`onePointSimplePoleCoordinate ∞ q = q.getD 0` and prove that `‖z‖ → ∞` along
the cocompact/punctured neighborhood of `∞`. For `Q = (a : ℂ)`, use the finite
normal form `(z - a)⁻¹` off the pole and prove the norm tends to `∞` along the
punctured finite neighborhood of `a`.

If needed, add small local sorry-free filter lemmas for translating between
`OnePoint ℂ` punctured neighborhoods and the corresponding complex filters,
but keep them scoped to this target coordinate.

This is a Lean-code support commit for one target field only. Do not thread the
helper into `BiholomorphOnePointSimplePolePullbackFieldFacts` yet. Do not
attempt to prove target meromorphicity or order in this step, and do not move
the reachable #234 root.

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

- [x] Confirm `.sci/plan.md` marks C1.5e complete and lists C1.5f/C1.5 as the
      next C1 support/proof work.
- [x] Inspect the coordinate normal-form lemmas and available `OnePoint` filter
      facts for finite points and `∞` in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` and
      `OnePointCxChartedSpace.lean`.
- [x] Prove the `Q = ∞` modulus-divergence case.
- [x] Prove the finite-pole modulus-divergence case, adding only narrowly
      scoped sorry-free filter helper lemmas if needed.
- [x] Add the public local helper
      `tendsto_norm_onePointSimplePoleCoordinate_atTop`.
- [x] Keep the seven-field provider as the sole reachable #234 root; do not
      remove `target_modulus_tendsto` from the provider in this step.
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
  with existing `uses sorry` warnings at the seven-field provider and
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root remains
  `biholomorphOnePointSimplePolePullbackFieldFacts_of_biholomorph_onePoint`.
- `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`:
  no axiom/unsafe declarations; only the expected two real `sorry`s in this
  file plus explanatory comments.
