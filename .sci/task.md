# Worker jc0 — Milestone A1.2: isolate normalized Montel selector provider

## Assignment

Execute the newly recorded Milestone A1.2 from `.sci/plan.md`: replace the
current gluing-data provider `sorry`
`genusZeroGlobalGluingData_of_homeomorph_onePoint` with an even narrower named
provider for a completed normalized Montel patch selector.

Introduce `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`,
returning `Nonempty (GenusZeroNormalizedMontelPatchSelector X)` from the given
topological homeomorphism `X ≃ₜ OnePoint ℂ`, and prove
`genusZeroGlobalGluingData_of_homeomorph_onePoint` by assembling a
`GenusZeroGlobalGluingData X` from that selector using the existing
`genusZeroGlobalGluing_*` lemmas.

This is a Lean-code commit. It should not solve normalized selector existence
yet; it should make the remaining #232 frontier strictly narrower and keep the
public uniformization theorem unchanged.

## Scope

- Edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`,
  `.sci/plan.md`, and `.sci/task.md`.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Do not use the circular fixed-pole/Riemann--Roch route.
- Do not add more than one new `sorry`; the selector provider must replace the
  gluing-data provider `sorry`, not add a second reachable gap.
- Preserve the public theorem name and signature of
  `exists_biholomorph_onePoint_of_genus_zero`.

## Checklist

- [x] Confirm `.sci/plan.md` marks A1.1 complete and contains A1.2 as the next
      explicit Milestone A substep.
- [x] Inspect the fields of `GenusZeroGlobalGluingData` and the existing
      `genusZeroGlobalGluing_*` lemmas that fill those fields from
      `GenusZeroNormalizedMontelPatchSelector`.
- [x] Add `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint` with
      exactly one `sorry`, documenting it as the remaining normalized-selector
      existence frontier.
- [x] Replace the body of `genusZeroGlobalGluingData_of_homeomorph_onePoint`
      with sorry-free assembly from the selector provider.
- [x] Keep `exists_biholomorph_onePoint_of_genus_zero` assembling through
      `genusZeroGlobalGluingData_of_homeomorph_onePoint` unchanged.
- [x] Run `lake build Jacobian.HolomorphicForms.GenusZeroClassification`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable genus-zero
      root moved from `genusZeroGlobalGluingData_of_homeomorph_onePoint` to
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`, with no
      net new reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.GenusZeroClassification`: succeeds;
  the only warning in this file is the new
  `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the
  genus-zero root moved from `genusZeroGlobalGluingData_of_homeomorph_onePoint`
  to `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.
- The public theorem `exists_biholomorph_onePoint_of_genus_zero` was left with
  the same name/signature and continues to assemble through
  `genusZeroGlobalGluingData_of_homeomorph_onePoint`.
