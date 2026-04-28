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

## Live Status (2026-04-28 03:34 EDT)

- **Aristotle: 1/5 ours active.** (63158306 returned & integrated)
  - `d493c66b` follow-up TOPDOWN refinement on
    `holomorphicOneForm_onePointCx_toFun_eq_zero` in
    `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — the
    chart-coefficient extraction sorry exposed by `90750074`.
    IN_PROGRESS at 37%, ~1h34min (stuck ~60 min).
- **Aristotle integration this tick:** `63158306` Step 1 of the
  Banach-data construction.  NEW 115-line sorry-free file
  `Jacobian/HolomorphicForms/SectionFiberNorm.lean` with
  `ContMDiffSection.fiberNorm` + `continuous_fiberNorm`.  Documents
  Mathlib v4.28.0 API gap: no `NormedVectorBundle` class, so the
  continuity proof needs an `hcompat` hypothesis (trivialization
  preserves fiber norms).  Build green (8026 jobs).
  Aristotle integrations to date: 101.

- **Claude-owned structural move this tick:** Blocker 5 RESOLVED.
  Added a `norm_le` field to `HolomorphicOneFormBanachData` in
  `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`:
  ```
  norm_le : ∀ (σ : HolomorphicOneForm ℂ X) (x : X),
    ‖σ.1 x‖ ≤ toNorm.norm σ
  ```
  Connects the abstract Banach norm to pointwise fiber evaluation,
  making `holomorphicOneForm_montel B` no-longer-false for arbitrary B.
  No constructor breaks because the only constructor
  (`holomorphicOneForm_normedSpace_uniformOnCompact`) is itself still
  a sorry; the eventual sup-norm construction satisfies the bound
  trivially.  `plan.md` Phase 2 updated to mark Blocker 5 resolved.
  Build green: `lake build Jacobian.HolomorphicForms.CompactRiemannSurface`
  (2409 jobs); `lake build Jacobian.Challenge` (8026 jobs).
- **Local proof work this tick (Aristotle stalled):** extended
  `Jacobian/HolomorphicForms/EntireZero.lean` with a fifth corollary:
    * `Differentiable.eq_zero_of_norm_eventually_le` — entire +
      `‖f z‖ ≤ g z` eventually along `cocompact ℂ` for some `g`
      tending to 0 ⇒ identically 0.
  General form of the decay corollaries.  Build green (8026 jobs).
- Past hour: 4 substantive Aristotle integrations
  (5dfd5106 / 848a0c88 / 6992e390 / 90750074) + Aristotle 100th
  integration milestone + Claude-owned `EntireZero.lean`
  (4 sorry-free Liouville-zero lemmas) + `dc8af381` partial-rescue
  with local proof.
- **Prior tick:** `90750074` Liouville core
  TOPDOWN refinement — substantive 3-piece split:
    1. `entire_tendsto_zero_eq_zero` (Liouville application).
       Aristotle's proof was 5 lines using
       `Complex.liouville_theorem_aux` + `simp_all +decide`.  Replaced
       by Claude with a one-liner reference to
       `Differentiable.eq_zero_of_tendsto_zero_cocompact` from
       `EntireZero.lean` (avoids duplicate proof).
    2. NEW sorry `holomorphicOneForm_onePointCx_toFun_eq_zero` —
       the chart-coefficient-extraction obligation.  Excellent
       docstring documenting the chart-pullback proof structure
       (identity chart → f(z) dz; inversion chart → -f(1/w)/w² dw
       forces f → 0 at infinity; Liouville).  Names the Mathlib gap:
       no API for reading `ContMDiffSection` of cotangent bundle
       through chart trivializations.
    3. `holomorphicOneForm_onePointCx_subsingleton` is now sorry-free
       assembly via `ext_toFun`.
  NET: file sorry count UNCHANGED (3) but structure significantly
  better — deep analytic content (Liouville) fully discharged via
  `EntireZero.lean`; remaining sorry is specifically the chart
  extraction.  Added import: `Jacobian.HolomorphicForms.Ext` (for
  `ext_toFun`) and `Jacobian.HolomorphicForms.EntireZero`.
  Build green (8036 jobs); Challenge green (8026 jobs).
- **Prior tick rescue:** `dc8af381` returned with
  status COMPLETE_WITH_ERRORS.  Diff was unusable as-is (broad
  `import Mathlib`, commented-out docstring delimiter, tangled
  `convert ... aesop` chain that didn't typecheck).  HOWEVER the
  proof OUTLINE was correct, identifying the right Mathlib API
  (`Module.Free.chooseBasis`, `Module.Basis.ofZLatticeBasis`,
  `ZSpan.fundamentalDomain`, `ZSpan.floor`,
  `ZSpan.fract_mem_fundamentalDomain`).  Claude wrote a clean
  ~30-line local proof using that outline:
    1. Get `bℤ := Module.Free.chooseBasis ℤ (basisAlignedPeriodSubmoduleℤ X)`.
    2. Get `bR := bℤ.ofZLatticeBasis ℝ _` (lifts to ℝ-basis of ambient).
    3. `D := closure (ZSpan.fundamentalDomain bR)` — compact via
       `(fundamentalDomain_isBounded bR).isCompact_closure` (proper
       space).
    4. Coverage: for any `v`, take `g := ZSpan.floor bR v`.  Then
       `v - g = ZSpan.fract bR v ∈ ZSpan.fundamentalDomain bR ⊆ D`.
       Lift `g` from `Submodule ℤ` to `AddSubgroup` via
       `AddSubgroup.toIntSubmodule_toAddSubgroup`.
  Subtleties: (a) the theorem had to be MOVED to the bottom of the
  file (after the `_isZLattice` instance) since it now uses it; (b)
  `▸` substitution on `Module.Basis.ofZLatticeBasis_span` blows up
  motive-inference (basis index type depends on the Submodule), so
  used `congrArg Submodule.toAddSubgroup` to lift the equality at
  the AddSubgroup level instead.
  Sorry count `PeriodFunctional.lean` reduced 3→2.  Build green
  (2960 jobs); `lake build Jacobian.Challenge` green (8026 jobs).
  Aristotle's broken diff is NOT integrated — only the outline was
  used; `dc8af381` logged as `failed_partial_used_for_outline`.
- **Aristotle integration this tick:** `5dfd5106`
  `holomorphicOneForm_montel` survey, +275 lines of docstring on
  `CompactRiemannSurface.lean`.  7-step proof outline (chart cover
  → chartwise representation → Cauchy ⇒ equicontinuity →
  Arzelà–Ascoli → diagonal extraction → Weierstrass closedness →
  sequential ⇔ topological compactness).  KEY STRUCTURAL FINDING
  (Blocker 5): `holomorphicOneForm_montel` is FALSE for arbitrary
  `B : HolomorphicOneFormBanachData X` because the structure has no
  axiom relating `B.toNorm` to pointwise section evaluation.
  Recommends adding `norm_le_iSup` (or `norm_eq_iSup`) field.
  Statement-shape change deferred until step (a)
  (`holomorphicOneForm_normedSpace_uniformOnCompact`) is being
  attacked — currently itself a sorry, so no constructor breaks.
- **Build:** `lake build Jacobian.HolomorphicForms.CompactRiemannSurface`
  green (2409 jobs).  Sorry count unchanged in that file (3).
- **Open structural design item:** Blocker 5 (norm-vs-pointwise
  axiom on `HolomorphicOneFormBanachData`).  Track in `## Top open
  correctness item` below.
- **Sub-agent delegation:** none this tick — Aristotle survey
  retrieval was the focus.  Next opportunity is the
  uniformization-lite transport step
  `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx`
  (different theorem from `90750074`'s target but in the same file —
  must wait for `90750074` to retire before dispatching).
- **Sorry recount per file:** Claude-owned production sorries 9 across
  3 files (CompactRiemannSurface 3, GenusZeroClassification 3,
  PeriodFunctional 3 — PeriodLattice fully delegating with 0 own
  sorries).  User-WIP at 12 across 5 files.  383/391 production files
  sorry-free.

- **Aristotle: 3/5 active.** Per user request to "give aristotle
  multiple jobs in parallel" with focus on biggest bottom-up gaps:
  - `b782c387` ContMDiffSection topology recon — IN_PROGRESS at 17%,
    ~6h54m elapsed.
  - `5dfd5106` `holomorphicOneForm_montel` survey — just submitted.
    Riemann-Roch chain step (b).
  - `848a0c88` NEW `SectionTopologyConstructionRecon.lean` — just
    submitted. Companion to b782c387, focused specifically on
    constructing the Banach data on `ContMDiffSection` for compact X.
- **Sub-agents (2 async):**
  - #1: refining `analyticGenus_eq_zero_of_homeomorphic_sphere`
    (genus-zero easy direction) in `GenusZeroClassification.lean`.
  - #2: bridging `periodSubgroup_isZLattice` to `IsZLattice ℝ`
    instance in `PeriodFunctional.lean`.
- **Disjoint write scopes:** sub-agent #1 → GenusZero; sub-agent #2
  → PeriodFunctional; Aristotle 5dfd5106 → CompactRiemannSurface;
  Aristotle 848a0c88 → NEW file. No two workers target the same file.
- **Local proof work this tick:** scaled up parallel delegation to
  4 workers (2 sub-agents + 2 Aristotle).

- **Codex round integrated this tick:** introduced
  `theorem periodSubgroup_isZLattice` in `PeriodFunctional.lean` as
  the named bottom-up obligation; refined
  `basisAlignedPeriodSubgroup_isDiscrete` in `PeriodLattice.lean`
  to a one-liner delegation. Codex initially used `opaque` (build
  error: Prop needs Inhabited/Nonempty); Claude fixed by switching
  to `theorem ... := sorry` per TOPDOWN.md rule 7. Build green.
- **Local proof work this tick:** integrated codex round + post-fix.



## Layer status

- **Complex torus layer: complete (sorry-free).**
- **Queue C foundation in place.**
- **Queue D scaffolding (1 opaque, no sorries):** 11 files +
  umbrella; growing.
- **Queue E foundation:** `AnalyticJacobianGroup E X` + umbrella.
- **Queue F:** Recon document.
- **Queue G:** Recon document (`Jacobian/TraceDegree/Recon.lean`)
  inventories `mfderiv`/`ContMDiff` (PRESENT) vs `pullbackForms`/
  `traceForms`/`analyticDegree` (ABSENT); lays out chain-rule for
  pullback, fiber-sum for trace, 6 packets, flags
  `pushforward_pullback` as the strongest multiplicative anti-hack
  theorem.
- All challenge queues (A through G) have at least a recon document
  or production scaffold; Queue H's theorems live in
  `Jacobian/Challenge.lean` directly.

### Queued for next submission round (gated on current batch)

- `pullbackFormsFun_smooth` — Queue G follow-up to `0b8b1163`:
  prove the chain-rule pullback function is `ContMDiff` when `f` is.
  The substantive piece for upgrading to `HolomorphicOneForm E X`.
- `pathIntegralViaChartCorrect` linearity (zero/neg/add) — gated on
  `ee3ce016` + `fe592ee1`.
- Multi-chart `pathIntegralViaCover` definition combining
  `exists_uniform_chart_partition` (from `PathPartition`) with
  chart-local integrals. Needs Claude-owned design step first
  (subpath / affine reparam), then a clean Aristotle packet for
  the well-definedness lemmas.
- Decomposed TorusExample replacement (split into "constant
  function `_ ↦ id` is `ContMDiff`" as a standalone helper, then
  build the section on top), retrying `259b18a1`'s scope.

## Top open correctness item

`chartedForm c ω e v` should equal
`ω.toFun (c.symm e) (D(c.symm)_e v)`, but the current definition
drops the chart-derivative `D(c.symm)_e` and only evaluates the
section at `c.symm e`. Lean accepts the type only because
`TangentSpace I _ = E` trivially. Consequence: `pathIntegralInChart`
is the right integral only when chart transitions are translations
(torus case); it is wrong on a general Riemann surface. Flagged in
the `ChartedForm.lean` docstring and tracked here as the highest-
priority correctness fix. The proper version uses
`mfderiv 𝓘(ℂ, E) (chartedSpaceSelf ...) c.symm e` (or the
inverse-chart partial derivative API).
- Deferred (per the user's explicit guidance and the
  reviewer-acknowledged staging-phase tradeoff): file granularity
  consolidation, naming-convention alignment, and the
  `FullComplexLattice → Submodule + IsZLattice` design change. These
  belong to the eventual Mathlib-prep cleanup, not this phase.

## Planned packets (queued for Aristotle when queue unblocks)

The chart layer is complete; the next layer is `LieAddGroup` smoothness
of `+` and `-` on `quotient V Λ`. Decomposition into Aristotle-sized
packets below. Each packet targets one new file; allowed writes are
that file only; forbidden files always include `Jacobian/Challenge.lean`.

1. **`Jacobian/ComplexTorus/AddSmoothLocal.lean`** — `ContMDiffAt`
   of `(q1, q2) ↦ q1 + q2` at a single point. Strategy: at point
   `(q1, q2)` lift to representatives `v1, v2` via `Function.surjInv`,
   use the chart machinery (the same δ from
   `exists_pos_le_norm_of_discreteTopology` works for both factors),
   and observe that on a small ball the chart-coordinate addition is
   exactly the linear sum on `V × V → V`, then mk back. Re-uses
   `localSection_mk_locally_translate`-style reasoning; no new heavy
   API.

2. **`Jacobian/ComplexTorus/AddSmooth.lean`** — promote (1) to
   `ContMDiff (modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V)
   (modelWithCornersSelf ℂ V) ⊤ (fun p => p.1 + p.2)` and from there
   to a `ContMDiffAdd` instance.

3. **`Jacobian/ComplexTorus/NegSmoothLocal.lean`** — `ContMDiffAt` of
   `q ↦ -q`. Same lift+chart pattern; in chart coordinates negation
   is `x ↦ -x` on `V`, which is `ContDiff ℂ ω`.

4. **`Jacobian/ComplexTorus/NegSmooth.lean`** — promote (3) to
   `ContMDiff` everywhere.

5. **`Jacobian/ComplexTorus/LieAddGroup.lean`** — combine the
   `ContMDiffAdd` instance from (2) and the `contMDiff_neg` from (4)
   into a `LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
   (quotient V Λ)` instance. One- or two-line `where`-clause once the
   pieces are in place.

When the queue unblocks, submit (1) and (3) in parallel (disjoint
write scopes), then (2) and (4), then (5). All five fit the
"prefer simple tactics" guideline.

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
