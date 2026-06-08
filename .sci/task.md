# Worker jc0 — Milestone A1.1: isolate #232 gluing-data provider

## Assignment

Execute the newly recorded Milestone A1.1 from `.sci/plan.md`: replace the
broad public #232 `sorry` in
`exists_biholomorph_onePoint_of_genus_zero` with one narrower named provider
for completed global gluing data.

Introduce `genusZeroGlobalGluingData_of_homeomorph_onePoint`, returning
`Nonempty (GenusZeroGlobalGluingData X)` from the given topological
homeomorphism `X ≃ₜ OnePoint ℂ`, and prove
`exists_biholomorph_onePoint_of_genus_zero` by applying
`GenusZeroGlobalGluingData.exists_contMDiff_homeomorph` to that data.

This is a Lean-code commit. It should not solve the analytic selector
existence yet; it should make the remaining #232 gap strictly narrower,
explicitly named, and easier to attack in the next step.

## Scope

- Edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`,
  `.sci/plan.md`, and `.sci/task.md`.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Do not use the circular fixed-pole/Riemann--Roch route.
- Do not add more than one new `sorry`; the new provider must replace the
  public #232 `sorry`, not add a second reachable gap.
- Preserve the public theorem name and signature of
  `exists_biholomorph_onePoint_of_genus_zero`.

## Checklist

- [x] Confirm `.sci/plan.md` marks Milestone 0 complete and contains A1.1 as
      the next explicit Milestone A substep.
- [x] Inspect current ordering of `GenusZeroGlobalGluingData`,
      `GenusZeroGlobalGluingData.exists_contMDiff_homeomorph`, and
      `exists_biholomorph_onePoint_of_genus_zero`.
- [x] Add `genusZeroGlobalGluingData_of_homeomorph_onePoint` with exactly one
      `sorry`, documenting it as the remaining analytic selector/gluing-data
      existence frontier.
- [x] Replace the body of `exists_biholomorph_onePoint_of_genus_zero` with
      sorry-free assembly from the provider via
      `GenusZeroGlobalGluingData.exists_contMDiff_homeomorph`.
- [x] Keep downstream references to `exists_biholomorph_onePoint_of_genus_zero`
      compiling after any necessary relocation.
- [x] Run `lake build Jacobian.HolomorphicForms.GenusZeroClassification`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable genus-zero
      root moved from `exists_biholomorph_onePoint_of_genus_zero` to
      `genusZeroGlobalGluingData_of_homeomorph_onePoint`, with no net new
      reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.GenusZeroClassification`: succeeds;
  the only warning in this file is the new
  `genusZeroGlobalGluingData_of_homeomorph_onePoint` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the
  genus-zero root moved from `exists_biholomorph_onePoint_of_genus_zero` to
  `genusZeroGlobalGluingData_of_homeomorph_onePoint`.
