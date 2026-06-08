SUGGESTED TASK: Milestone B2 wire the universe-u period-rank companions #241/#240.

Objective: complete the Chapter-06 Cluster B blueprint map by wiring the
universe-`u` Riemann-bilinear and H1-basis companion frontiers into the B1 #227
dependency story. After this step, #227, #241, and #240 should each expose only
their genuine remaining frontier rather than floating from the statement bank.

Scope:
- Read `Jacobian/Periods/PeriodVectorsLIU.lean`,
  `Jacobian/Periods/H1BasisU.lean`, `Jacobian/Periods/PeriodFunctionalU.lean`,
  and any small adjacent Periods files needed to identify green wrappers around
  #241 and #240.
- In the blueprint, add or move compact `\lean{}`-tracked nodes so:
  - `lem:riemann-classical-real-li-input-u` (#241) explicitly points to the
    Type-0 #227 input and any green universe-transport wrappers.
  - `lem:h1-basis-of-compact-riemann-surface-u` (#240) explicitly points to its
    surface-classification/H1-basis frontier and does not look like another
    Riemann-bilinear analytic gap.
  - `thm:period-lattice` continues to use the public #240/#241 nodes, but those
    nodes now have their own proof skeleton.
- Prefer editing `tex/statements/statement-bank.tex` only as needed to expose
  the #240/#241 nodes; use `tex/sections/06-periods-and-riemann-bilinear.tex`
  for shared explanatory substrate if that keeps Cluster B coherent.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- Confirm every new `\lean{}` declaration exists.
- For every new node marked `\leanok`, verify the corresponding Lean
  declarations are genuinely sorry-free using `#print axioms` and/or
  `sorries.jsonl` evidence.
- Run `scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh`.
- Update `.sci/result.md` with the B2 mapping summary and the next recommended
  milestone.

Checklist:
- [x] Survey the universe-`u` period-rank files and identify green #241/#240
      wrappers or transport substrate.
- [x] Add or refine blueprint nodes for #241 so its dependency on #227 and
      universe transport is explicit.
- [x] Add or refine blueprint nodes for #240 so its H1-basis/surface-frontier
      dependency is explicit and separate from #227/#241.
- [x] Verify all new Lean declarations and green-ness claims.
- [x] Run `scripts/blueprint_audit.py`.
- [x] Run `bash scripts/build-blueprint.sh`.
- [x] Update `.sci/result.md` with B2 findings and the next mapping
      recommendation.
- [x] Commit the tex/result/task/plan/sorries updates and set
      `.sci/status-line` to `READY: Chapter 06 B2 universe period-rank map`.
