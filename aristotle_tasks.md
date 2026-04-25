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

## Live Status (2026-04-25 11:46 EDT)

- Active jobs (ours): 3/5
  | ID         | Target file                                       | Kind  | Status  |
  | ---------- | ------------------------------------------------- | ----- | ------- |
  | 8d77f7d8   | `Jacobian/ComplexTorus/IsolationAtZero.lean`      | proof | QUEUED  |
  | 1841ae34   | `Jacobian/ComplexTorus/MkInjOnSmallBall.lean`     | proof | QUEUED  |
  | c5beb23a   | `Jacobian/ComplexTorus/DiscretenessRecon.lean`    | recon | QUEUED  |
- Retrieved/integrated earlier this tick (separate commit `eb31864`):
  5c13793d ZLatticeFundDom — packaging helper landed clean and was
  wired into `fullComplexLatticeOfZLattice` to drop its remaining
  sorry. The ZLattice→FullComplexLattice bridge is now sorry-free.
- Three new disjoint-write-scope packets just submitted (queue
  refilled to 3/5):
  - `8d77f7d8` proves a generic isolation-at-zero lemma for any
    `DiscreteTopology`-equipped `AddSubgroup` of a seminormed group.
    Hypothesis-form, source-agnostic.
  - `1841ae34` proves `mk` is injective on small balls under an
    explicit isolation hypothesis. Independent of how the lattice
    is sourced; takes `δ` as data.
  - `c5beb23a` is a reconnaissance packet for the standing trap:
    closed cocompact ⇏ discrete in finite-dim normed real spaces
    (counterexample `ℝ × ℤ ⊂ ℝ²`). Aristotle answers five
    structured questions about the cleanest discreteness predicate
    and how `IsZLattice` already supplies it. Output is comments
    only; no proofs, no new declarations.
- Holding 3/5 (not 5/5) deliberately: the next two slots want to be
  the chart-layer packets (small-ball open embedding, chartAt atlas),
  but those need the FullComplexLattice discreteness field to be
  in place first. The discreteness refactor is a deliberate
  Claude-owned step planned for next tick, informed by `c5beb23a`'s
  recon results.

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
