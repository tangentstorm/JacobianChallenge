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

## Live Status (2026-04-25 10:03 EDT)

- Active jobs (ours): 3/5
  | ID         | Target file                                  | Lemma(s)                          |
  | ---------- | -------------------------------------------- | --------------------------------- |
  | cb03cf32   | `Jacobian/ComplexTorus/MapClmSurjective.lean`| `mapClm_surjective`               |
  | 01dfbc1f   | `Jacobian/ComplexTorus/MkHomKer.lean`        | `mkHom_ker = Λ.subgroup`          |
  | 65e8da6e   | `Jacobian/ComplexTorus/MapZero.lean`         | `zero_preserves_lattices`, `mapClm_zero` |
- Integrated this tick: none.
- These three are small follow-up packets (continuous-linear-map
  surjectivity wrapper, kernel of the bundled projection, and the
  zero-CLM corner case).

- Active jobs (ours): 4/5 (queue refilled)
  | ID         | Target file                              | Lemma(s)                            |
  | ---------- | ---------------------------------------- | ----------------------------------- |
  | 02468cd4   | `Jacobian/ComplexTorus/MkImage.lean`     | `mk_image_isCompact/Open`           |
  | 98392eb4   | `Jacobian/ComplexTorus/MkPreimage.lean`  | `mk_preimage_isOpen/Closed`         |
  | 0faaf3e5   | `Jacobian/ComplexTorus/MkBundled.lean`   | `mkHom`, `mkHom_apply`              |
  | 2649200e   | `Jacobian/ComplexTorus/MkRange.lean`     | `range_mk`, `mk_image_univ`         |
- Integrated this tick: none (no completions to integrate).
- These are API-rounding packets — small, direct one-liners — to keep
  Aristotle busy while planning the next substantive layer (manifold
  structure, ZLattice bridge).

- Active jobs (ours): 5/5 (all queued, just submitted)
  | ID         | Target file                                | Lemma(s)                                    |
  | ---------- | ------------------------------------------ | ------------------------------------------- |
  | 5a37a9c3   | `Jacobian/ComplexTorus/Connected.lean`     | `connectedSpace_quotient`                   |
  | 83af50d3   | `Jacobian/ComplexTorus/Nhds.lean`          | `nhds_mk_eq`                                |
  | f2a1782c   | `Jacobian/ComplexTorus/Dense.lean`         | `dense_mk_image_iff` / `dense_preimage_mk_iff` |
  | 88c7c85c   | `Jacobian/ComplexTorus/FirstCountable.lean`| First/second-countable instances            |
  | 5573ebd7   | `Jacobian/ComplexTorus/PathConnected.lean` | `pathConnectedSpace_quotient`               |
- Integrated this tick (5):
  - `20ebfd1c` — `map_injective_of_preimage_subset` (Aristotle's proof
    used `simp +decide`; replaced with a clean tactic proof using
    `mk_eq_iff` + `f.map_add` + `f.map_neg`).
  - `518be471` — `mk_neg = rfl`; `continuous_neg = ContinuousNeg.continuous_neg`.
  - `650e16fe` — `mk_add = rfl`; `continuous_add = _root_.continuous_add`.
  - `fb51396b` — `mk_zsmul`/`mk_nsmul` via `map_zsmul`/`map_nsmul` of `mk'`.
  - `7250ad71` — `mapClm_continuous = map_continuous f.continuous hf`.
- Done previously: `c97ef7ec`, `6e60ff64`, `4d2fa17c`, `21a882aa`,
  `e2c130cc`, `07e77aac`; algebraic `mk` / `map` / `map_id` / `map_comp`
  in `StatementBank.lean`; `mk_continuous`, `mk_isOpenQuotientMap`,
  `mk_isOpenMap` in `Basic.lean`.
- Next planned submissions: compactness from cocompact lattice;
  lattice-image preservation under continuous maps; bridge to a real
  `ZLattice` / `IsZLattice` predicate; topological-group instance
  bundling on the quotient.

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
