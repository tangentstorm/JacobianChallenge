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

## Live Status (2026-04-28 09:46 EDT)

- **PROMPT.md §3 rule: every production sorry has a 1:1 Aristotle job.**
  21 production sorries, ~14 covered by active packets (some older
  packets still in flight may not be visible in `aristotle list`'s
  top-10 window).
- **Aristotle integrations to date: 116** (from `aristotle_jobs.jsonl`).
- **Backend status:** queue saturated since ~08:21 EDT; all 11 visible
  packets have been QUEUED for 10–95 minutes with **none transitioning
  to IN_PROGRESS**. The Aristotle backend appears to be offline or
  heavily backlogged. Treating "Never wait on an Aristotle result"
  literally: working locally on whatever Claude can close.

### Active our-packets (visible in `aristotle list`)

| ID | File | Sorry | Submitted |
|---|---|---|---|
| `f914a263` | PushforwardBasis | `contMDiff_continuousAddMonoidHom_complexTorus` | 08:21 |
| `654d5071` | AnalyticOfCurveBasis | `pathIntegralFunctional_contMDiff_spec` | 08:21 |
| `7f3ec297` | PullbackBasis | `analyticPullback_mk_eq` + `basisDualPullback_comp` paired | 08:23 |
| `e3dcd529` | PushforwardBasis | `analyticPushforward_mk_spec` | 08:23 |
| `0a5f74a8` | PeriodFunctional | one of 2 sorries | 09:01 |
| `03715a4d` | GenusZeroClassification | one of 4 sorries | 09:01 |
| `05100f76` | PullbackBasis | `basisDualPullback_id` | 09:01 |
| `b7799fc9` | PushforwardBasis | `pushforwardTraceLift_id` | 09:24 |
| `6b2f47f1` | AnalyticOfCurveBasis | `pathIntegralFunctional_separates_points_spec` | 09:35 |

### Older our-packets (likely still queued; not in top-10 window)

- `8585f085` Step 4 SectionComplete (Banach-data construction).
- `bbe527bb` AnalyticDegree anti-hack #4 (now matches the
  Claude-introduced `_spec` companion, same content).
- `c7feba63` CompactRiemannSurface `holomorphicOneForm_montel`.
- `d8fd495f` ULiftTransport `_contMDiff_up`.
- `2bd5f151` ULiftTransport `_contMDiff_down`.

### Cancelled this session (replaced by local discharge)

- `c69fcd88` (analyticPullback_id_spec) — local split via
  `basisDualPullback_id` companion.
- `369f3f7b` (analyticPullback_contMDiff) — local 1-line application
  of `contMDiff_continuousAddMonoidHom_complexTorus`.
- `16277f52` (quotientMk_contMDiff_spec) — local 1-line application
  of `ComplexTorus.contMDiff_mk` (existing infra).
- `65001239` (analyticPushforward_id_eq) — local split via
  `pushforwardTraceLift_id` companion.

### Recent local Claude moves (this session, ordered)

- Integrated 6 Aristotle deeper-companion-spec splits in one cluster:
  99825c13, 777f976c, 3264c622, a3b5ae84, 09a7e39c, 90fc4a81 —
  collectively promoted ~6 spec sorries to real assembly proofs.
- Skipped 2aab5e91 (structural conflict with 99825c13's
  `basisDualPullback`) and 7f273ec8 (redundant blocker docstring).
- Local discharges: 4 sorries (listed in Cancelled above).
- Split `analyticPushforward_analyticPullback` (anti-hack #4) per
  Option A in its own docstring: introduced `_spec` companion, public
  lemma is now sorry-free assembly.
- Submitted 9 new packets for newly-emerged or orphaned sorries.

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
