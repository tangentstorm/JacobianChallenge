# Whole-Project Axiom Audit

**Audit date:** 2026-06-01
**Audit branch:** `jc3-axiom-audit` (off accepted M3 tip `8d3dae1e`)
**Auditor:** jc3 (per Option C directive in `.sci/result.md` 2026-06-01)
**Scope:** READ-ONLY. No source edits. Probed via temporary throwaway
`_AuditProbe.lean` (NOT committed) running `#print axioms` per declaration.
**Build state:** `lake build Jacobian.Solution` → exit 0, 3831 jobs, 37
`uses sorry` warnings (the reachable-sorry baseline), zero non-sorry warnings.
**Reachable sorries:** 37 across 11 files (per `scripts/list-sorries.py --text`).

---

## §1. Custom axioms — exhaustive catalogue

`grep -rn "^axiom \|^private axiom " --include="*.lean" Jacobian/` confirms
exactly **ONE custom axiom** project-wide:

| Axiom | Declared at | Namespace |
|---|---|---|
| `localPullbackAt_holomorphic` | `Jacobian/TraceDegree/TraceDefinition.lean:220` | **`JacobianChallenge.HolomorphicForms`** |

> ⚠ **Namespace correction.** The 2026-06-01 manager directive in
> `.sci/result.md` L33 names this axiom as
> `JacobianChallenge.TraceDegree.localPullbackAt_holomorphic`. That is
> incorrect — the file is in `Jacobian/TraceDegree/` but `TraceDefinition.lean`
> opens `namespace JacobianChallenge.HolomorphicForms` at L210 before declaring
> the axiom at L220. The Lean-resolved name is
> `JacobianChallenge.HolomorphicForms.localPullbackAt_holomorphic`. Every
> `#print axioms` output below confirms this.

### Statement

```lean
axiom localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x)
```

The stated content is: *"holomorphicity of the inverse branch combined with
smooth holomorphic variation of the cotangent pushforward in local
coordinates."* It is the remaining local analytic section-regularity
obligation for the trace-pullback construction.

### Transitive dependents (every declaration that uses this axiom)

Determined by `#print axioms` containing `localPullbackAt_holomorphic`:

#### A. TraceSpec.lean public theorems (jc3's sorry-free territory)
- `JacobianChallenge.HolomorphicForms.traceAtRegularValue_locally_bounded_near_branch_values`
- `JacobianChallenge.HolomorphicForms.traceForm_global_extension`
- `JacobianChallenge.HolomorphicForms.traceFormsBundled_eq_zero_of_constant`

These three are **`sorryAx`-FREE** (no `sorryAx` in their dependency closure)
and depend ONLY on `[propext, Classical.choice, Quot.sound,
localPullbackAt_holomorphic]`. They are the "axiom frontier" of the
trace-form route — the deepest sorry-free reach of the trace machinery.

#### B. TraceDegree pullback chain
- `JacobianChallenge.TraceDegree.analyticPullback`
- `JacobianChallenge.TraceDegree.analyticPullback_contMDiff`
- `JacobianChallenge.TraceDegree.analyticPullback_id_apply`
- `JacobianChallenge.TraceDegree.analyticPullback_comp_apply`
- `JacobianChallenge.TraceDegree.analyticPushforward_analyticPullback`

These depend on **both** `sorryAx` *and* `localPullbackAt_holomorphic`. The
`sorryAx` arrives via the `analyticOfCurve` /
`analyticGenus_eq_zero_iff_homeomorphic_sphere` chain (`AbelJacobi` and
`GenusZeroClassification` layers); the custom axiom arrives via the
pullback definition itself.

#### C. Solution.lean (Type-0 mirror) pullback chain
- `JacobianChallenge.Solution.Jacobian₀.pullback`
- `JacobianChallenge.Solution.Jacobian₀.pullback_contMDiff`
- `JacobianChallenge.Solution.Jacobian₀.pullback_id_apply`
- `JacobianChallenge.Solution.Jacobian₀.pullback_comp_apply`
- `JacobianChallenge.Solution.Jacobian₀.pushforward_pullback`

Same dual dependence (`sorryAx` + custom axiom) — these are thin ULift
wrappers around the `TraceDegree.analytic{Pullback,Pushforward}` decls in
§B above.

**Total decls touching the custom axiom: 13.** All on the pullback /
pullback-composition path. The pushforward side and the genus / Abel–Jacobi
sides do NOT depend on this axiom.

---

## §2. `#print axioms` per probed declaration

Standard kernel axioms abbreviated as `STD = [propext, Classical.choice,
Quot.sound]`. The `+sorry` column marks `sorryAx` presence; `+LP` marks
`localPullbackAt_holomorphic`.

### §2.1 — Top-level public spec (`Jacobian/Solution.lean`, lines 184–285)

This is the **public API** that mirrors `Jacobian/Challenge.lean`. Currently
defined as `sorry` stubs awaiting jc5's `Type → Type*` widen integration.

| Decl | STD | +sorry | +LP |
|---|---|---|---|
| `genus` | ✓ | ✓ | — |
| `genus_eq_zero_iff_homeo` | ✓ | ✓ | — |
| `Jacobian` | ✓ | ✓ | — |
| `Jacobian.ofCurve` | ✓ | ✓ | — |
| `Jacobian.ofCurve_contMDiff` | ✓ | ✓ | — |
| `Jacobian.ofCurve_self` | ✓ | ✓ | — |
| `Jacobian.ofCurve_inj` ★ | ✓ | ✓ | — |
| `Jacobian.pushforward` | ✓ | ✓ | — |
| `Jacobian.pushforward_contMDiff` | ✓ | ✓ | — |
| `Jacobian.pushforward_id_apply` | ✓ | ✓ | — |
| `Jacobian.pushforward_comp_apply` | ✓ | ✓ | — |
| `Jacobian.pullback` | ✓ | ✓ | — |
| `Jacobian.pullback_contMDiff` | ✓ | ✓ | — |
| `Jacobian.pullback_id_apply` | ✓ | ✓ | — |
| `Jacobian.pullback_comp_apply` | ✓ | ✓ | — |
| `Jacobian.pushforward_pullback` ★ | ✓ | ✓ | — |
| `ContMDiff.degree` | ✓ | — | — |
| `ContMDiff.degree_constant` | ✓ | — | — |

★ = anti-hack theorem (per CLAUDE.md §"Anti-hack theorems"). All anti-hack
top-level theorems are currently `sorryAx`-blocked.

> 🟢 `ContMDiff.degree` and `ContMDiff.degree_constant` are **sorry-free
> and axiom-clean** (depend only on STD). The `ContMDiff.degree` is the
> only public top-level decl currently free of `sorryAx`. This is because
> it has an explicit `noncomputable def` body (Solution.lean L264-273)
> using `Classical.choice` on `BranchedCoverData` existence — no `sorry`.

> 🔴 The custom axiom `localPullbackAt_holomorphic` does **NOT** appear in
> any of the public top-level `Jacobian.*` decls' axiom sets — because
> they are gated by `sorryAx` upstream of the trace-pullback chain. After
> jc5's widen lands and the `pullback`/`pullback_*` decls are wired to the
> Type-0 implementation, this axiom **will** appear in the comparator
> targets' axiom sets. The custom axiom IS on the path to the public
> `pushforward_pullback` anti-hack theorem.

### §2.2 — Anti-hack theorems (CLAUDE.md §"Anti-hack theorems")

CLAUDE.md lists four anti-hack mechanisms:

1. **`genus_eq_zero_iff_homeo`** — forces `genus` to be tied to topology
   (no `genus X := 0`).
2. **`ofCurve_inj`** — forces nonconstant injective Abel–Jacobi for
   positive genus (no `Jacobian X := PUnit`).
3. **Compact complex Lie-group instances on `Jacobian X`** — force
   torus-like analytic structure.
4. **`pushforward_pullback`** — forces pushforward/pullback/degree to
   interact through the classical trace identity.

| Anti-hack | Public top-level | Solution `Jacobian₀` (Type-0) impl |
|---|---|---|
| `genus_eq_zero_iff_homeo` | `STD + sorry` | `STD + sorry` |
| `ofCurve_inj` | `STD + sorry` | `STD + sorry` |
| Lie-group instances | (instances not directly probed; see §2.1 — all instance-stubs `STD + sorry`) | wired through `inferInstanceAs (… ULift …)` per Solution.lean L71-80 |
| `pushforward_pullback` | `STD + sorry` | **`STD + sorry + LP`** |

The Type-0 mirror's `pushforward_pullback` is the one declaration where the
custom axiom is load-bearing for an anti-hack theorem. Discharging
`localPullbackAt_holomorphic` is what makes the trace identity REAL on the
implementation side.

### §2.3 — Implementation namespace (`JacobianChallenge.Solution.Jacobian₀.*`)

The sorry-free Type-0 implementation. After jc5's widen, the top-level
`Jacobian.*` decls will delegate to these.

| Decl | STD | +sorry | +LP |
|---|---|---|---|
| `Jacobian₀` (type) | ✓ | ✓ | — |
| `Jacobian₀.ofCurve` | ✓ | ✓ | — |
| `Jacobian₀.ofCurve_contMDiff` | ✓ | ✓ | — |
| `Jacobian₀.ofCurve_self` | ✓ | ✓ | — |
| `Jacobian₀.ofCurve_inj` | ✓ | ✓ | — |
| `Jacobian₀.ofCurve_inj_with_meromorphicData` | ✓ | ✓ | — |
| `Jacobian₀.pushforward` | ✓ | ✓ | — |
| `Jacobian₀.pushforward_contMDiff` | ✓ | ✓ | — |
| `Jacobian₀.pushforward_id_apply` | ✓ | ✓ | — |
| `Jacobian₀.pushforward_comp_apply` | ✓ | ✓ | — |
| `Jacobian₀.pullback` | ✓ | ✓ | ✓ |
| `Jacobian₀.pullback_contMDiff` | ✓ | ✓ | ✓ |
| `Jacobian₀.pullback_id_apply` | ✓ | ✓ | ✓ |
| `Jacobian₀.pullback_comp_apply` | ✓ | ✓ | ✓ |
| `Jacobian₀.pushforward_pullback` | ✓ | ✓ | ✓ |
| `Solution.genus` | ✓ | ✓ | — |
| `Solution.genus_eq_zero_iff_homeo` | ✓ | ✓ | — |
| `Solution.genus_eq_zero_with_routeData_homeo` | ✓ | ✓ | — |

**Asymmetry observation:** The `pushforward` chain has NO `LP` dependency,
but the `pullback` chain has `LP` on every decl. This matches the
mathematical asymmetry: pullback requires holomorphic-section regularity
(the content of `localPullbackAt_holomorphic`), pushforward does not.

### §2.4 — Mid-layer intermediates (`AbelJacobi`, `TraceDegree`, `HolomorphicForms`)

| Decl | STD | +sorry | +LP |
|---|---|---|---|
| `AbelJacobi.analyticOfCurve` | ✓ | ✓ | — |
| `AbelJacobi.analyticOfCurve_contMDiff` | ✓ | ✓ | — |
| `AbelJacobi.analyticOfCurve_self` | ✓ | ✓ | — |
| `AbelJacobi.analyticOfCurve_injective` | ✓ | ✓ | — |
| `AbelJacobi.analyticOfCurve_injective_with_meromorphicData` | ✓ | ✓ | — |
| `TraceDegree.analyticPushforward` | ✓ | ✓ | — |
| `TraceDegree.analyticPushforward_contMDiff` | ✓ | ✓ | — |
| `TraceDegree.analyticPushforward_id_apply` | ✓ | ✓ | — |
| `TraceDegree.analyticPushforward_comp_apply` | ✓ | ✓ | — |
| `TraceDegree.analyticPullback` | ✓ | ✓ | ✓ |
| `TraceDegree.analyticPullback_contMDiff` | ✓ | ✓ | ✓ |
| `TraceDegree.analyticPullback_id_apply` | ✓ | ✓ | ✓ |
| `TraceDegree.analyticPullback_comp_apply` | ✓ | ✓ | ✓ |
| `TraceDegree.analyticDegree` | ✓ | — | — |
| `TraceDegree.analyticPushforward_analyticPullback` | ✓ | ✓ | ✓ |
| `HolomorphicForms.analyticGenus` | ✓ | — | — |
| `HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere` | ✓ | ✓ | — |
| `HolomorphicForms.localPullbackAt_holomorphic` | ✓ | — | (self) |

> 🟢 **`analyticDegree`** and **`analyticGenus`** are sorry-free AND
> axiom-clean (depend only on STD). The numeric-output decls (degree, genus
> as ℕ) are completely honest. Only their classification *theorems*
> (`genus = 0 ↔ sphere`) drag in `sorryAx`.

> 🟢 **TraceSpec's three public theorems** (`traceAtRegularValue_locally_bounded_near_branch_values`,
> `traceForm_global_extension`, `traceFormsBundled_eq_zero_of_constant`) —
> jc3's M1–M3 deliverable — are **`sorryAx`-FREE**. Their only non-STD
> axiom is `localPullbackAt_holomorphic`. This is the cleanest layer in
> the project: jc3 has driven the trace-form route down to a single
> custom axiom.

### §2.5 — Reachable frontier sorries (per `scripts/list-sorries.py`)

Each reachable frontier sorry shows up as a `sorryAx` dependency in
something. The probed *theorem-level* names corresponding to each reachable
sorry:

| Reachable sorry | Public decl probed | STD | +sorry | +LP |
|---|---|---|---|---|
| `analyticOfCurve_injective` | `AbelJacobi.analyticOfCurve_injective` | ✓ | ✓ | — |
| `deRhamComparisonMap1_smooth_local_representatives_period_cycle_axiom_frontier` | (probed by same name) | ✓ | ✓ | — |
| `deRhamComparisonMap1_zero_period_exact_axiom_frontier` | (probed by same name) | ✓ | ✓ | — |
| `exists_contMDiff_homeomorph_to_onePointCx` | (probed by same name) | ✓ | ✓ | — |
| `genusZero_singlePoleMeromorphicAnalyticData_nonempty` | (probed by same name) | ✓ | ✓ | — |
| `genusZero_pointRRSection_meromorphic_getD_exists` | (probed by same name) | ✓ | ✓ | — |
| `cut_along_nonTree_yields_unfoldedDisk` | (probed by same name) | ✓ | ✓ | — |
| `handlePrefix_tailRotate_homeomorph` | (probed by same name) | ✓ | ✓ | — |
| `edgeChain_sum_singular_boundary_scalar_coefficient_zero` | (probed by same name) | ✓ | ✓ | — |
| `polygon4g_partial_side_arc_homologous_to_edge_chain` | (probed by same name) | ✓ | ✓ | — |
| `polygon4g_quotient_path_finite_lift_subdivision` | (probed by same name) | ✓ | ✓ | — |
| `riemann_classical_real_LI_input` | (probed by same name) | ✓ | ✓ | — |
| `brahana_orientable_core` | **private** — not cross-module probable | — | — | — |
| `inverseCancel_geometric_maps` | **private** — not cross-module probable | — | — | — |
| `Solution.lean L29 instance (StableChartAt)` | (instance — present in all `Solution.*` sorryAx sets) | ✓ | ✓ | — |
| `Solution.lean L33 instance (FiniteDimensionalHolomorphicOneForms)` | (instance — present in all `Solution.*` sorryAx sets) | ✓ | ✓ | — |
| `Solution.lean L199–283 top-level Jacobian.* sorry stubs` (21 sorries) | per §2.1 — all `STD + sorry` | ✓ | ✓ | — |

> 🟢 **None of the reachable frontier sorries currently depends on the
> custom axiom.** The custom axiom is consumed only by sorry-free decls
> (the TraceSpec triple) and by the pullback/pullback-composition chain
> (which is also `sorryAx`-tainted from above). So discharging the custom
> axiom is INDEPENDENT of discharging the frontier sorries; both can
> proceed in parallel.

---

## §3. The single source of truth: what must land for `comparator/jacobian.json` (final mode)

To reach an axiom-clean, sorry-free public `Jacobian.*` API, the following
must all be discharged:

### §3.1 — The 17 reachable sorries outside Solution.lean
(All present in some public decl's `+sorry` axiom set per §2.5)

| File | Sorries | Worker | Anti-hack relevance |
|---|---|---|---|
| `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` | 1 (`analyticOfCurve_injective`) | (unowned; jc3-adjacent) | ofCurve_inj |
| `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` | 2 (period-cycle, zero-period-exact frontiers) | jc0 | indirect via genus |
| `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | 1 (`exists_contMDiff_homeomorph_to_onePointCx`) | jc0 | genus_eq_zero_iff_homeo |
| `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` | 1 (`genusZero_singlePoleMeromorphicAnalyticData_nonempty`) | jc0 | genus_eq_zero_iff_homeo |
| `Jacobian/HolomorphicForms/RiemannRoch.lean` | 1 (`genusZero_pointRRSection_meromorphic_getD_exists`) | jc0 | genus_eq_zero_iff_homeo |
| `Jacobian/Periods/DualGraphCut.lean` | 1 | Periods | DeRham → genus |
| `Jacobian/Periods/HandleSwapHomeo.lean` | 1 | Periods | DeRham → genus |
| `Jacobian/Periods/Hurewicz.lean` | 3 | Periods | DeRham → genus |
| `Jacobian/Periods/PeriodFunctional.lean` | 1 | Periods | period lattice → Jacobian instances |
| `Jacobian/Periods/TietzeReduction.lean` | 2 (both private) | Periods | DeRham → genus |

**Total: 14 reachable sorries** in non-Solution files.

### §3.2 — The 23 reachable sorries in Solution.lean
These are the **top-level `Jacobian.*` stubs** awaiting jc5's `Type → Type*`
widen. Once the widen lands, each is a one-line delegation to the matching
`Jacobian₀.*` (Type-0) impl. The implementation is already done sorry-free
on the Type-0 side; this is mechanical wiring.

**Total: 23 stubs** in Solution.lean.

### §3.3 — The custom axiom
**`JacobianChallenge.HolomorphicForms.localPullbackAt_holomorphic`** must be
either:
- discharged as a theorem (turning it from `axiom` into `theorem` with a
  real proof), or
- replaced by an equivalent sorry-free construction.

**Total: 1 custom axiom.** Currently load-bearing on 13 decls (per §1) —
all of which become sorry-free + axiom-clean once both this axiom AND the
upstream `sorryAx` are discharged.

### §3.4 — Grand total

To pass `comparator/jacobian.json` (final mode) with zero `sorryAx` and
zero custom axioms on every public decl:

**14 (non-Solution sorries) + 23 (Solution stubs, via widen) + 1 (custom
axiom) = 38 obligations.** Net reachable count: 37 (sorries) + 1 (axiom).

---

## §4. Alarming items / red flags

### §4.1 — None of the four anti-hack theorems is currently trivially satisfied
All four anti-hacks (per CLAUDE.md):
- `genus_eq_zero_iff_homeo` — `STD + sorry`, NOT proved trivially. The
  Type-0 mirror `Solution.genus_eq_zero_iff_homeo` is also `STD + sorry`
  (delegates to `analyticGenus_eq_zero_iff_homeomorphic_sphere` which is
  `STD + sorry` via `exists_contMDiff_homeomorph_to_onePointCx` and the
  meromorphic-data chain). When all upstream sorries discharge, this WILL
  be honest. No trivialization detected.
- `ofCurve_inj` — same pattern. `Solution.Jacobian₀.ofCurve_inj` delegates
  to `AbelJacobi.analyticOfCurve_injective` which is sorry-blocked. When
  that sorry discharges, this becomes honest.
- Lie-group instances — `Solution.Jacobian₀` wires through
  `inferInstanceAs (… ULift …)` to the `ComplexTorus.quotient` type, which
  is built from the period lattice (real construction). No instance is
  `:= sorry`-only on the implementation side; the public top-level
  instances at `Solution.lean:207-213` are sorry-stubbed pending jc5's
  widen but the underlying Type-0 instances are real.
- `pushforward_pullback` — `Solution.Jacobian₀.pushforward_pullback` is
  `STD + sorry + LP`. After upstream sorries + axiom discharge, this
  becomes the genuine trace identity. Currently NOT trivially satisfied;
  delegates to `TraceDegree.analyticPushforward_analyticPullback` which is
  the real classical-trace proof modulo the same dependencies.

> 🟢 **All four anti-hacks pass the audit.** No trivial fake construction
> detected.

### §4.2 — Custom axiom on a comparator-target path: YES, by design

`localPullbackAt_holomorphic` IS on the path to the public
`pushforward_pullback` (via the pullback chain). This is the project's
explicit "one axiom left" — known. Per `ref/plan.md` and the project's
roadmap, the eventual goal is to discharge this axiom into a theorem.
Currently, this means **the project, on final-mode comparator, will still
report one custom axiom on the `pullback`/`pushforward_pullback` route**
until that discharge happens. NOT a defect — explicit project state.

### §4.3 — Public decl with surprising axiom set: NO

Every probed public decl's axiom set is exactly the expected superset of
`STD = [propext, Classical.choice, Quot.sound]`, with `sorryAx` and/or
`localPullbackAt_holomorphic` added as predicted by the dependency graph.
No unexpected axioms; no leakage of unusual extensions.

### §4.4 — The `+LP` / `+sorry` overlap on the pullback chain

The 13 decls touching the custom axiom are ALL also `+sorry` right now.
This means *the custom axiom is currently NOT a tight gate* — even after
the axiom discharges, those decls still depend on `sorryAx` upstream until
the relevant `analyticOfCurve` /
`analyticGenus_eq_zero_iff_homeomorphic_sphere` sorries clear. Conversely:
discharging the axiom alone produces no axiom-clean public theorem; this
is a **necessary** step but not by itself **sufficient**.

> Practical implication: jc3 (or whoever inherits the axiom-discharge
> work) should NOT expect axiom-cleanness on any consumer until the
> upstream sorry frontier also clears. The two streams must converge.

### §4.5 — The private TietzeReduction sorries are invisible to `#print axioms` cross-module

`brahana_orientable_core` and `inverseCancel_geometric_maps` are declared
`private` and cannot be probed by name from a separate file. They do show
up in `scripts/list-sorries.py --text` as REACHABLE, meaning some public
decl in the import closure depends on them. They cannot be enumerated by
this audit's methodology — flagged here for completeness. Audit suggestion:
the manager may want a follow-up where the TietzeReduction sorries are
locally probed by inserting `#print axioms` in the same file.

---

## §5. Routing guidance for endgame discharges

Per the manager directive ("intelligence to route the endgame discharges"):

### §5.1 — Highest-leverage single discharge
**`localPullbackAt_holomorphic`** as a theorem. Eliminates the project's
ONE custom axiom. Touches 13 dependent decls. Lives in jc3's natural
trace-degree territory. Substantial work — requires proving holomorphicity
of a section through the local inverse branch — but the mathematical
content is bounded and chart-local, similar in shape to DB-B.

### §5.2 — Jc5's `Type → Type*` widen (E2 route-β)
Unblocks the 23 Solution.lean stubs and makes them one-line delegations
to the Type-0 implementation. After this lands, the public anti-hack
theorems inherit their Type-0 axiom sets verbatim. **Highest count
reduction**; minimal mathematical content.

### §5.3 — `analyticOfCurve_injective` (`AbelJacobi`)
**One sorry**, unblocks `ofCurve_inj` (anti-hack #2). Lives in
`Jacobian/AbelJacobi/`. Currently unowned per `.sci/task.md` mapping;
plausible jc3 follow-up if the manager reassigns turf.

### §5.4 — The DeRham → Periods chain
`exists_contMDiff_homeomorph_to_onePointCx`, the meromorphic / RiemannRoch
chain, Hurewicz, TietzeReduction. **Long pole** — many sorries with
genuine homological content. Out of jc3's natural turf; jc0 / Periods
owner work.

### §5.5 — Cleanest current path to a sorry-free anti-hack
**`pushforward_pullback` (anti-hack #4)** is closest to discharge because:
- `pushforward` side is sorry-free except for the upstream
  `analyticOfCurve` / `analyticGenus` chain.
- `pullback` side needs `localPullbackAt_holomorphic` + the same upstream.
- The classical-trace identity itself
  (`analyticPushforward_analyticPullback`) is already proved at the
  `TraceDegree` layer.

The mathematical content is **complete**; the obligations are upstream
discharge work. Once `localPullbackAt_holomorphic` becomes a theorem and
the `analytic*` sorries clear, `pushforward_pullback` is axiom-clean.

---

## §6. Methodology + reproducibility

**Probe approach:** Temporary file `_AuditProbe.lean` at repo root
(NOT committed; NOT a lake target — `Jacobian/` lib root excludes it).
The probe imports `Jacobian.Solution` and runs `#print axioms` on every
target decl, captured via:

```bash
lake env lean _AuditProbe.lean 2>&1 > /tmp/axiom-audit-raw.txt
```

The raw output `/tmp/axiom-audit-raw.txt` (192 lines, zero errors after
two iteration cycles to correct namespace mismatches) is the audit's
source of truth. Probe file deleted on audit completion.

**Reproducibility:** A reviewer can regenerate the raw data by:
1. Checking out commit (this audit's tip) on a clean working tree.
2. Re-creating `_AuditProbe.lean` from the namespace list in §2.1–§2.5.
3. Running `lake env lean _AuditProbe.lean 2>&1`.
4. Diffing against the per-decl axiom sets recorded here.

**Limitations:**
- `private` declarations cannot be probed cross-module by name (per
  §4.5).
- The `Solution.lean` instance-stubs at L29/L33 do not have stable names
  (auto-named per Lean's instance numbering); they appear as `sorryAx`
  dependencies inside every `Solution.*` decl rather than as
  individually-probable decls.
- `#print axioms` returns the closure-axiom set, not direct uses. A decl
  may depend on `+LP` transitively through any chain; the audit does not
  identify the *shortest* dependency path.

**Audit cost:** Two probe iterations (~3 minutes each); zero compile-time
overhead added to the project (`_AuditProbe.lean` is throwaway, not a
build target). No source edits.

---

## §7. Manager action items (in priority order)

1. **Correct namespace for `localPullbackAt_holomorphic`** in the project
   record: it is `JacobianChallenge.HolomorphicForms.…`, not
   `JacobianChallenge.TraceDegree.…` (per §1).
2. **Decide endgame priority** between (a) `localPullbackAt_holomorphic`
   discharge (one axiom, 13 dependents), (b) jc5's widen (23 stubs, high
   count, low risk), (c) frontier-sorry discharges in jc0 / Periods turf
   (14 sorries, long pole). All three streams converge on a
   sorry-free + axiom-clean public API; the question is sequencing.
3. **Decide if jc3 should take `analyticOfCurve_injective`** (`AbelJacobi`,
   one sorry, unblocks `ofCurve_inj` anti-hack) as a follow-up — it is
   adjacent to jc3's trace-machinery context but currently outside the
   plan.md scope.
4. **TietzeReduction private-sorry follow-up audit** if completeness of
   the private-decl axiom audit is needed (per §4.5).

---

*End of audit.*
