# Worker jc1 — Plan: Chapter 06 (Periods & Riemann Bilinear) blueprint-to-Mathlib

Lead the planning for Chapter 06. **Phase 1 (now): map the chapter's blueprint
all the way to Mathlib** — every node's `\uses` chain bottoms out in a green
project node or a named Mathlib lemma. **Phase 2: the 8 sorries are split for
execution across jc1 / jc4 / jc5** per the split you write in `result.md`.

See `goal.md` § FIRST JOB for the full framing and the 3 clusters.

## 0. Allowed write scope (planning phase)
* **Write:** `tex/sections/06-periods-and-riemann-bilinear.tex` (+ any tex needed
  to connect Chapter-06 nodes); `.sci/result.md` for the split proposal. Read
  freely across `Jacobian/Periods/` and `Jacobian/HolomorphicForms/`.
* **Forbidden:** `Jacobian/Challenge.lean`. Do not edit Lean proofs in files
  another worker is active in: jc3 (StableChartAt reroute —
  `Periods/HolomorphicOneFormToFunContinuous.lean`, `TraceSpec.lean`, …);
  jc2 (`TietzeReduction.lean`, `HandleSwapHomeo.lean`).

## 1. The 8 chapter-06 sorries (3 clusters)
* **A — Hurewicz / singular homology:** `polygon4g_quotient_path_finite_lift_subdivision` (#228),
  `polygon4g_partial_side_arc_homologous_to_edge_chain` (#229),
  `edgeChain_sum_singular_boundary_scalar_coefficient_zero` (#230) — Periods/Hurewicz.lean.
* **B — Riemann bilinear / period rank:** `riemann_classical_real_LI_input` (#227, **keystone**) —
  Periods/PeriodFunctional.lean; `riemann_classical_real_LI_inputU` (#241) — Periods/PeriodVectorsLIU.lean;
  `h1_basis_of_compact_riemann_surfaceU` (#240) — Periods/H1BasisU.lean.
* **C — de Rham / Hodge exactness:** `deRhamComparisonMap1_zero_period_primitiveExists_provider` (#242) —
  HolomorphicForms/DeRhamComparisonMap.lean; `hodgeRemainder_periodPayload_exact` (#243) —
  HolomorphicForms/HodgeProjection.lean.

## 2. Commit sequence — Phase 1 (blueprint mapping)

### Milestone 0 — Baseline audit
- [x] **0.** Inventory the current Chapter-06 blueprint nodes in
      `tex/sections/06-periods-and-riemann-bilinear.tex` and which of the 8 sorry
      nodes float without a proof skeleton. Confirm no dangling `\uses`/`\ref`.
      `bash scripts/build-blueprint.sh` and `scripts/blueprint_audit.py` baseline-clean.

### Milestone B-map — Riemann bilinear (the keystone first)
- [x] **B1.** Survey the sorry-free substrate beneath #227
      (`PeriodFunctional.lean`: wedge-integration pairing, Hodge positivity on
      periods, the Stokes-on-polygon input) and add `\lean{}`-tracked green
      blueprint nodes wired with `\uses` down to green nodes / Mathlib (Stokes,
      integration, Hodge star). #227 is the keystone — its U-companions #241/#240
      are mechanical ports, so map B before A/C.
- [x] **B2.** Wire #227, #241, #240 so each one's only remaining
      orange/uncoloured dependency is its genuine gap.

### Milestone A-map — Hurewicz / singular homology
- [x] **A1.** Survey the green substrate beneath the 3 Hurewicz sorries
      (4g-gon quotient charts, edge-chain cellular model, singular-chain
      subdivision) and add green nodes with `\uses` down to Mathlib (Arzelà–Ascoli
      / quotient-map / cellular-homology facts) or green project lemmas.
- [ ] **A2.** Wire #228/#229/#230 to their genuine frontier leaves only.

### Milestone C-map — de Rham / Hodge exactness
- [ ] **C1.** Refine `input:hodge-deRham` so #242 is the unique de Rham
      primitive-existence frontier and #243 is the unique Hodge
      closed = harmonic + exact frontier; add green nodes for the surrounding
      assemblies (zero-period-to-kernel, primitive-to-exact, harmonic projection
      kernel/exact) and cite the classical/Mathlib bottom leaves honestly.

### Milestone V — Verify + split
- [ ] **V1.** Green-ness audit: every new `\lean{}` node's decl exists and is
      genuinely sorry-free if green (`scripts/list-sorries.py --text`,
      `#print axioms`); never `\leanok` an open frontier node.
- [ ] **V2.** `bash scripts/build-blueprint.sh` (fails on unresolved labels) and
      `scripts/blueprint_audit.py` both clean; `lake build Jacobian.Solution`
      green (no new sorries).
- [ ] **V3.** Write `.sci/result.md`: the jc1/jc4/jc5 execution split with
      ordering — **#227 before #241**; Cluster-A lift/side-arc before #230
      coefficient independence; #242/#243 split by de Rham vs Hodge frontier;
      plus cross-worker coordination notes from the dependency graph.
- [ ] **V4.** Commit the tex/result/task updates; set status
      `READY: Chapter 06 blueprint-to-Mathlib plan`.

## 3. Notes
* Phase 1 adds/relabels blueprint nodes only — it introduces NO new Lean sorries
  and changes no Lean proof. Net reachable-sorry change: 0.
* The execution phase (discharging the 8) follows the split you produce — that is
  a separate assignment, not this planning job.
* Per proving-guide: never declare blocked on a Mathlib gap — but in the planning
  phase, an honest Mathlib citation at a leaf IS the correct bottoming-out.
