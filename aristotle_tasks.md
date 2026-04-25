# Aristotle Task Index

This file indexes the Lean statement bank in
`Jacobian/WorkPackets/StatementBank.lean`.

Claude should treat each queue below as a source of small Aristotle jobs. Before
submitting, Claude should copy the relevant declarations into a narrower target
file and ask Aristotle to work only on that file.

The Aristotle account is shared with other projects; job IDs from
`aristotle list` may belong to FourColor or other unrelated work. Record every
JacobianChallenge submission in `aristotle_jobs.jsonl` so future ticks can
identify our jobs without inspecting tarballs.

## Live Status (2026-04-25 17:15 EDT)

- Active jobs (ours): 2/5
  | ID         | Target file                                          | Kind  | Status      |
  | ---------- | ---------------------------------------------------- | ----- | ----------- |
  | 58789fac   | `Jacobian/ComplexTorus/LocalSectionRightInv.lean`    | proof | in flight   |
  | f1d1e010   | `Jacobian/ComplexTorus/LocalSectionContinuous.lean`  | proof | in flight   |
- Retrieved + integrated earlier today: ChartBall (21cc9828) and
  LocalSection (cdbfd6d5). Both clean, sorry-free.
- Submitted earlier this tick: 58789fac (left-inverse `localSection (mk x) = x`
  on the ball, uses `MkInjOnSmallBall.mk_injOn_ball_of_isolation`) and
  f1d1e010 (continuity of the local section on the chart image — the
  substantive piece needed for the `OpenPartialHomeomorph` assembly).
- Major Claude-owned activity this tick (separate concern, not
  Aristotle): applied the structural feedback in
  `feedback/ComplexTorus.md`. Specifically:
  - Removed `ZLatticeRecon`, `ManifoldRecon`, `DiscretenessRecon` from
    the public umbrella `Jacobian/ComplexTorus.lean` (recon files
    still build standalone but aren't re-exported as API).
  - Fixed `ManifoldRecon.lean`'s construction outline: the false
    "show `Λ.subgroup` is discrete from `Λ.isClosed` + finite-dim"
    claim is gone; the outline now starts from `Λ.isDiscrete` and
    cites the existing primitives.
  - Tightened `secondCountableTopology_quotient` to require
    `[SecondCountableTopology V]` rather than relying on `inferInstance`
    finding something dubious.
  - Collapsed the compactness duplication: the proof of
    `compactSpace_quotient_of_cover` now lives in `Defs.lean` and the
    `quotient_compactSpace` instance specializes it.
  - Migrated the complex-torus core out of
    `Jacobian/WorkPackets/StatementBank.lean` into a new
    `Jacobian/ComplexTorus/Defs.lean`. All 35 sibling files now
    import `Defs.lean` directly. `StatementBank.lean` keeps only the
    not-yet-implemented placeholder targets and the higher-layer
    queues, and imports `Defs.lean` for what it needs.
- Deferred (per the user's explicit guidance and the
  reviewer-acknowledged staging-phase tradeoff): file granularity
  consolidation, naming-convention alignment, and the
  `FullComplexLattice → Submodule + IsZLattice` design change. These
  belong to the eventual Mathlib-prep cleanup, not this phase.

## General Job Template

```text
Working directory: C:\ver\JacobianChallenge
Target file: <one Lean file>
Allowed writes: only <target file>
Do not edit: Jacobian/Challenge.lean
Task: prove or implement the named declarations below.
Expected verification: lake build <module name>
If blocked: leave the theorem statement unchanged and add a short comment naming
the missing prerequisite.
```

## Queue A: Inventory

Source namespace:

```lean
JacobianChallenge.Inventory
```

Useful declarations:

- `MathlibInventory`
- `inventoryComplete`

Expected output:

- a factual inventory of existing Mathlib declarations at the pinned commit;
- exact file paths and declaration names;
- a list of missing infrastructure.

## Queue B: Complex Tori

Source namespace:

```lean
JacobianChallenge.ComplexTorus
```

Useful declarations:

- `FullComplexLattice`
- `quotient`
- `mk`
- `mk_surjective`
- `map`
- `map_mk`
- `map_id`
- `map_comp`
- `quotientChartedSpaceStatement`
- `quotientIsManifoldStatement`
- `quotientLieAddGroupStatement`

Good first Aristotle packets:

- prove quotient-map universal property lemmas;
- prove `map_mk`, `map_id`, and `map_comp`;
- replace placeholder lattice fields with existing Mathlib predicates if found;
- isolate the exact quotient-manifold theorem needed.

## Queue C: Holomorphic Forms and Genus

Source namespace:

```lean
JacobianChallenge.HolomorphicForms
```

Useful declarations:

- `HolomorphicOneForm`
- `FiniteDimensionalHolomorphicOneForms`
- `analyticGenus`
- `genus_eq_analyticGenus`
- `analyticGenus_eq_zero_iff_homeomorphic_sphere`

Expected packets:

- define holomorphic 1-forms using existing differential-form API;
- prove vector-space structure;
- state finite-dimensionality as a named theorem;
- connect analytic genus to the challenge `genus`.

## Queue D: Periods

Source namespace:

```lean
JacobianChallenge.Periods
```

Useful declarations:

- `IntegralOneCycle`
- `HolomorphicOneFormDual`
- `periodFunctional`
- `periodSubgroup`
- `periodSubgroup_isClosed`
- `periodFullComplexLattice`
- `period_homology_invariance_statement`
- `period_pairing_full_rank_statement`

Expected packets:

- define path/cycle integration;
- prove homology invariance of periods;
- prove period subgroup is closed;
- prove the full-lattice theorem.

## Queue E: Analytic Jacobian

Source namespace:

```lean
JacobianChallenge.AnalyticJacobian
```

Useful declarations:

- `AnalyticJacobian`
- `analyticJacobianEquivChallenge`
- `analyticJacobian_homeomorph_challenge`

Expected packets:

- define Jacobian from the period lattice;
- bridge to the public challenge type;
- handle universe issues deliberately.

## Queue F: Abel-Jacobi

Source namespace:

```lean
JacobianChallenge.AbelJacobi
```

Useful declarations:

- `pathIntegralFunctional`
- `analyticOfCurve`
- `analyticOfCurve_path_independent`
- `analyticOfCurve_self`
- `analyticOfCurve_contMDiff`
- `analyticOfCurve_injective`
- `challenge_ofCurve_eq_analytic`

Expected packets:

- prove path independence modulo periods;
- prove basepoint maps to zero;
- prove holomorphicity;
- prove injectivity for positive genus.

## Queue G: Trace, Degree, Pushforward, Pullback

Source namespace:

```lean
JacobianChallenge.TraceDegree
```

Useful declarations:

- `pullbackForms`
- `traceForms`
- `analyticDegree`
- `trace_pullback_forms`
- `degree_eq_analyticDegree`
- `pullbackForms_preserves_periods`
- `traceForms_preserves_periods`
- `analyticDegree_comp`
- `pushforward_pullback_from_trace`

Expected packets:

- define pullback of forms;
- define trace of forms;
- prove the trace-pullback identity;
- define degree compatibly;
- descend maps to Jacobians.

## Queue H: Anti-Hack Theorems

Source namespace:

```lean
JacobianChallenge.AntiHack
```

Useful declarations:

- `genus_zero_topological_sphere`
- `positive_genus_nontrivial_jacobian`

Expected packets:

- prove or trace dependencies for the anti-hack theorems;
- keep these theorems separate from convenience API;
- do not weaken their statements.
