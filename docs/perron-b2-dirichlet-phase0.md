# Phase 0: pricing the B2 Dirichlet kernel (`stage_dirichlet_harmonic_exists`)

> Companion to `docs/perron-engine-phase1.md` (the engine plan that named B2
> its worst single node), `docs/perron-a2a3-topology-phase0.md` (A2/A3 lane),
> and `docs/perron-b4-conjugate-phase0.md` (jc7's B4 pricing, which files an
> interface request against this node). Tracking #232, Path A, blueprint node
> `lem:stage-dirichlet-harmonic-exists`. Prose-only pricing: no Lean edits,
> no tex edits, no builds. Substrate re-verified in the local checkout on
> 2026-06-11.

## Executive Conclusion

Three findings, in decreasing order of urgency.

**First, the landed B2 statement is refutable as written.** A concrete
counter-instance (§2.1, buildable on `OnePoint ℂ` from the project's own
instances) exploits two gaps at once: `StageBoundaryChartData` does not
require boundary pieces to lie in the frontier, so `agrees_boundary` can be
made to force the "harmonic" solution to equal an everywhere-discontinuous
boundary potential on an *open* subset of the stage; and
`StageDipoleBoundaryControl` carries no continuity field, so such a
potential is a legal A4 instance. No worker should be pointed at the sorry
in `exists_stageDirichletHarmonicSolution` until the statement is repaired;
§2 itemizes the minimal repair list (S1–S7), which interlocks with jc7's
B4 request R2.

**Second, after repair, the honest content is classical and decomposes
cleanly.** The committed route (§3) is not a bespoke dipole Perron family
but a three-way decomposition `u = −G₀ + G_∞ + H[g]`: two Green's
functions with one logarithmic pole each (Perron-natural, pole on the
`sup` side) plus a singularity-free Perron solution for the continuous
boundary data. Each piece is textbook potential theory. Mathlib has *no*
subharmonic API, *no* Dirichlet solvability, *no* Harnack inequality, *no*
harmonic maximum principle, and *no* Poisson boundary-limit theorem
(§1, re-verified) — but it has gained, since the engine plan's survey, the
harmonic mean-value property and two-sided Herglotz-kernel estimates, which
are exactly the leaves from which Harnack and the maximum principle are
short local developments. The route avoids building an
upper-semicontinuous subharmonic theory: a continuous-comparison subclass
(§3.2) suffices for Perron, and its cost is priced rather than shaded.

**Third, the total is engine-scale, as the plan predicted.** Roughly 30–40
one-leaf commits across eleven work packages (§4): a reusable chart-disc
toolbox (maximum principle, Poisson operator, Harnack, removable
singularity — ~15–20 commits, fully farmable) plus stage-side assembly
(envelope, barriers, Green's functions — ~15–20 commits, serial after the
toolbox). The single worst pure-math leaf is the Poisson boundary-limit
theorem (W3d); the single worst spec-gated leaf is the barrier subtree
(W8), which cannot start until A2 supplies a boundary-regularity field
(S7). If the manager weakens B2's boundary clause to maximum-principle
bounds instead of pointwise agreement, W3d and W8 drop out and the price
falls by roughly a third — that trade is the manager's single biggest
lever and is laid out, not presumed, in §5.

On jc7's R2: this pricing **prefers the chartwise
`InnerProductSpace.HarmonicOnNhd` export shape** (the alternative jc7
explicitly allows). Reason in §3.8: every step of the Perron construction
natively proves Mathlib-side harmonicity of chart readings; the
conjugate-witness forms (per-point or neighborhood-uniform) are then one
routine bridge through `exists_analyticOnNhd_ball_re_eq`, whereas
carrying conjugate witnesses through the Perron steps would smear that
bridge across the entire development.

## Target Payload

The open provider is `exists_stageDirichletHarmonicSolution`
(`Jacobian/HolomorphicForms/StageDirichlet.lean:114`, sorry at `:126`),
which must produce `Nonempty (StageDirichletHarmonicSolution X e marked
selected exhaustion profiles boundaryControl)` for **every** instance of
the A1/A2/A4/B1 interfaces, under `[TopologicalSpace X] [T2Space X]
[ChartedSpace ℂ X]` and `e : X ≃ₜ OnePoint ℂ` (note: no `IsManifold`
hypothesis — see S5). The payload structure (`StageDirichlet.lean:53`)
fields, per stage `n`:

- `harmonicPotential n : X → ℝ` — the solution `u n`;
- `harmonicOn_stage` — `StageHarmonicOn` (`:28`): at every
  `x ∈ stage n` with `x ≠ P0, Pinf`, some conjugate `v` with
  `IsHarmonicConjugateAtReal X (u n) v x`
  (`HarmonicConjugate.lean:30`, a single-point `HasFDerivAt` of the
  chart-read `u + iv`);
- `agrees_boundary` — `StageBoundaryAgreement` (`:39`): `Set.EqOn (u n)
  (boundaryControl.boundaryPotential n)` on **every** boundary piece of
  `exhaustion.boundaryData n`;
- `base_normalized` — `u n marked.base = 0`;
- `has_pos_log_profile` / `has_neg_log_profile` —
  `HasLogarithmicSingularityAtReal X P0 (u n) 1` and `… Pinf (u n) (-1)`
  (`HarmonicDipole.lean:25`: the chart-read of `u` minus
  `sign · log‖z − chart P‖` *converges* at the chart image — an exact
  germ constant, not mere boundedness);
- `compactBound` / `boundaryCompactBound` / `boundaryCompactBound_eq` —
  `StageDipoleCompactBound` data (`StageDipoleBoundary.lean:24`; see §2.6
  on how weak this currently is).

Sign orientation, fixed once for the whole document: the `+1` germ at `P0`
means `u → −∞` at `P0`, the `−1` germ at `Pinf` means `u → +∞` at `Pinf`
— i.e. `u` models `log‖f‖` for a stage coordinate `f` with a zero at `P0`
and a pole at `Pinf`, exactly the engine's B5 intent.

Downstream consumers (statement-level, all on the branch): B4's
`exists_stageHarmonicConjugatesOnCuts`
(`StageHarmonicConjugate.lean:129`) consumes the payload wholesale; the
B5 stage-coordinate interface (landed `fc0055e2`) consumes B4. So B2's
field shapes propagate; getting them right now is cheap, later is not.

## 1. Substrate survey

### Project declarations (all 0-sorry unless noted)

Interfaces consumed as hypotheses (never as proved providers — see
anti-circularity):

- A1 `GenusZeroStageMarkedData` (`PerronStageMarkedData.lean:35`) with
  green provider `genusZeroStageMarkedData_nonempty` (`:99`): marked
  `P0/Pinf/base`, pairwise-disjoint open `U0/Uinf/Ubase` inside the
  preferred chart sources.
- A2/A3 `StageBoundaryChartData` (`StageExhaustion.lean:34`),
  `StageBorderedExhaustion` (`:52`), `StageCutSystem` (`:80`) — open
  monotone stages, frontier covered by finitely many chart pieces;
  providers `exists_stageBorderedExhaustion` (`:103`) and
  `exists_stageCutSystem` (`:116`) are open sorries (inputs only).
- A4 `StageDipoleBoundaryControl` (`StageDipoleBoundary.lean:61`) with
  `StageBoundaryChartControl` (`:42`, bounds **one** piece per stage) and
  `StageDipoleCompactBound` (`:24`, an *existential* compact-set bound);
  provider `exists_stageDipoleBoundaryControl` (`:93`) open (input only).
- A4-bridge `StageEventualContainment.lean` — green filter-to-bound
  conversions (`exists_stage_bound`, `exists_contains_and_avoids_bound`,
  uniform finite-family forms).
- B1a `GenusZeroStageDipoleProfiles` (`PerronStageDipoleProfile.lean:63`)
  with green provider (`:87`): canonical chart-pullback `±log` profiles,
  continuous off the marked points (`continuousOn_log_norm_chart_sub`
  `:34`).
- B1c `stageDipoleGluedPotential` (`PerronStageDipolePotential.lean:74`)
  and `StageDipolePotentialData` (`:128`), green provider (`:155`); germ
  congruence `HasLogarithmicSingularityAtReal.congr_on_nhds` (`:38`) —
  used below both constructively and in the §2.1 refutation.
- B1b `PerronStageLogConjugate.lean` — green off-point conjugates for the
  single-log profiles (`log_compose_chart_has_conjugate`,
  `chart_pullback_log_has_conjugate_at_off_P` ± variants): the
  `StageHarmonicOn`-shaped facts on `U0 \ {P0}`, `Uinf \ {Pinf}`.
- Dipole/conjugate library (`HarmonicDipole.lean`,
  `HarmonicConjugate.lean`): `HasLogarithmicSingularityAtReal` (`:25`)
  with `.add_tendsto` (`:163`) and pullback witnesses
  (`log_pullback_at_pos/neg`, `HarmonicConjugate.lean:857/:870`);
  `IsHarmonicConjugateAtReal` (`:30`) with closure lemmas `.add` (`:342`),
  `.neg` (`:292`), `.add_const_const` (`:385`), `.congr_of_eventuallyEq`
  (`:426`); chart-transition holomorphy `chart_transition_contDiffOn`
  (`:1083`, needs `IsManifold`); the full-coverage dipole conjugates
  `chart_pullback_dipole_has_conjugate_at_off_PQ` (`:1313`) and
  `existence_of_dipole_harmonic_off_on_X` (`:1372`).

What the project library does **not** contain: any Dirichlet-type
existence, any maximum principle, any Poisson/mean-value fact, any
removable-singularity fact, any Harnack-type estimate. Everything in §3's
toolbox is new.

### Mathlib verified PRESENT (local checkout, re-verified 2026-06-11)

The engine plan's list still holds; the pin has additionally **gained**
two modules it did not record. Per-item:

- `HarmonicAt` (`Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:39`
  — `ContDiffAt ℝ 2` + Laplacian eventually 0), `HarmonicOnNhd` (`:46`),
  algebra `.add/.sub/.neg/.const_smul` (`:114–:172`),
  `harmonicAt_congr_nhds` (`:61`), `isOpen_setOf_harmonicAt` (`:91`).
- `HarmonicContOnCl` (`…/Harmonic/HarmonicContOnCl.lean:34`).
- `ContDiffAt.harmonicAt` (`…/Harmonic/Constructions.lean:36`),
  `AnalyticAt.harmonicAt` (`:46`), `.harmonicAt_re/_im` (`:52/:58`),
  `.harmonicAt_log_norm` (`:107`).
- Harmonic ⇒ re-of-holomorphic on discs:
  `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`
  (`Mathlib/Analysis/Complex/Harmonic/Analytic.lean:71`), plus
  `HarmonicAt.analyticAt` (`:144`). This single theorem is the bridge on
  which the whole route leans (§3.1, §3.8).
- **NEW since the engine plan** — `Mathlib/Analysis/Complex/Harmonic/
  MeanValue.lean`: `HarmonicOnNhd.circleAverage_eq` (`:27`),
  `HarmonicContOnCl.circleAverage_eq` (`:50`) — the mean-value property.
- **NEW since the engine plan** — `…/Harmonic/Liouville.lean`:
  `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`
  (`:47`). Not consumed below, but evidence the upstream harmonic library
  is actively growing (a revisit trigger, §5).
- Poisson representation: `poissonKernel` (`Mathlib/Analysis/Complex/
  Poisson.lean:54`), `herglotzRieszKernel` (`:36`),
  `poissonKernel_eq_re_herglotzRieszKernel` (`:73`),
  `DiffContOnCl.circleAverage_poissonKernel_smul` (`:245`), and the
  harmonic versions `HarmonicOnNhd.circleAverage_poissonKernel_smul` /
  `HarmonicContOnCl.…` (`…/Complex/Harmonic/Poisson.lean:91/:102`).
- **Two-sided kernel estimates** (the engine plan did not flag these):
  `re_herglotzRieszKernel_le` (`Poisson.lean:101`) and
  `le_re_herglotzRieszKernel` (`:134`) — `(R−r)/(R+r) ≤ Re K ≤
  (R+r)/(R−r)` on the circle. These are precisely the Harnack-inequality
  leaves (§3.1, W4).
- `Real.circleAverage` API (`Mathlib/MeasureTheory/Integral/
  CircleAverage.lean`): `circleAverage_mono` (`:271`),
  `circleAverage_nonneg_of_nonneg` (`:303`), `circleAverage_const`
  (`:244`), `circleAverage_congr_sphere` (`:152`),
  `ContinuousLinearMap.circleAverage_comp_comm` (`:318`).
- Strict-positivity bridge for the strong maximum principle:
  `intervalIntegral.integral_pos_iff_support_of_nonneg_ae`
  (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1281`),
  `integral_eq_zero_iff_of_nonneg_ae` (`:1255`).
- Parametric holomorphy under the integral:
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean:97`), FDeriv
  variants (`:34/:56`) — the W3a leaf.
- Morera-direction tools: `IsConservativeOn` / `IsExactOn` and
  `DifferentiableOn.isExactOn_ball`
  (`Mathlib/Analysis/Complex/HasPrimitives.lean:109/:115/:290`).
- Maximum modulus for holomorphic functions
  (`Mathlib/Analysis/Complex/AbsMax.lean`):
  `norm_le_of_forall_mem_frontier_norm_le` (`:400`),
  `eqOn_of_eqOn_frontier` (`:432`),
  `norm_eqOn_of_isPreconnected_of_isMaxOn` (`:230`).
- `OnePoint ℂ` charted/manifold instances in-project
  (`OnePointCxIsManifold.lean:225`) — used by the §2.1 counter-instance.

### Mathlib verified ABSENT (re-verified 2026-06-11, queries in search log)

- **Subharmonic functions**: zero hits repo-wide for
  `subharmonic`/`Subharmonic`. The engine plan's negative result stands.
- **Dirichlet problem solvability** (any domain, including the disc): the
  only `dirichlet` hits are number-theoretic (characters, series,
  `Fourier/ZMod`, `Gamma/Deligne`). The Poisson modules are
  *representation* theorems — they require the function to already be
  harmonic/differentiable; nothing builds a harmonic function from
  boundary data. No `poissonIntegral`/`PoissonIntegral` operator exists.
- **Harnack** (inequality or principle): zero hits.
- **Maximum principle for harmonic functions**: absent. `AbsMax` is for
  `‖f‖` with `f` holomorphic; no real-harmonic version.
- **Poisson boundary-limit / approximate-identity theorem**: absent.
- **Removable singularity for harmonic functions**: absent
  (`RemovableSingularity.lean` is holomorphic-only).
- **Mean-value converse** (sub-mean or mean ⇒ harmonic): absent; the new
  `MeanValue.lean` is one-directional.
- **Harmonic ∘ holomorphic stability**: absent (only `comp_CLM`/CLE
  linear composition).
- **Weyl's lemma, Green's functions, harmonic measure**: zero hits — the
  Hilbert-space (Dirichlet-principle) alternative route has even less
  substrate than Perron (§5).

## 2. Satisfiability audit of the landed statement

This section must come before the classical argument, because the
argument cannot target the statement as landed. Labels S1–S7 to avoid
collision with jc7's R1–R4 (which are requests *to* other nodes; their R2
is *to* this node and is folded into S2).

### 2.1 (S1) The obligation is refutable as written

`StageBoundaryChartData` requires `boundaryPiece i ⊆ (chart i).source`
and `frontier stage ⊆ ⋃ i, boundaryPiece i` — but **not**
`boundaryPiece i ⊆ frontier stage`. A piece may cover the whole closed
stage. Meanwhile `StageDipoleBoundaryControl` constrains its
`boundaryPotential` only near `P0/Pinf/base` (values, germs, profile
agreement) plus a bound on *one* piece and one existential compact bound —
**no continuity anywhere**. Counter-instance, fully concrete:

- `X := OnePoint ℂ` with the project's charted structure
  (`OnePointCxIsManifold.lean:225`); `e := Homeomorph.refl`.
- Marked data via `genusZeroStageMarkedData_nonempty` with `P0 = 0`,
  `Pinf = ∞`, `base = 1`, and `U0/Uinf/Ubase` shrunk to miss
  `B := closedBall 10 1 ⊆ ℂ`.
- `selected.Index := Empty` (all eventual-containment fields vacuous);
  `stage n := coe '' ball 10 1` for every `n` (open, constant, monotone).
- `boundaryData n`: one chart index, the `ℂ`-coordinate chart (source
  `= coe '' ℂ ⊇ closure (stage n)`), and `boundaryPiece := coe '' B`.
  All A2 fields check: the piece is in the source, and
  `frontier (stage n) = coe '' sphere 10 1 ⊆ coe '' B`.
- `boundaryPotential n := stageDipoleGluedPotential + junk`, where `junk`
  is the indicator of a dense-and-codense subset of `ball 10 1`,
  extended by `0`. Every A4 field checks: the marked neighborhoods and
  `base` miss `B`, so the glue's normalization, both germs
  (via `congr_on_nhds`), and both profile agreements are untouched;
  `boundaryChartControl` holds with bound `1` (the glue vanishes on `B`);
  `compactBound` holds with `compactSet := ∅`.

Now suppose a `StageDirichletHarmonicSolution` existed. `agrees_boundary`
forces `u n = boundaryPotential n` on `coe '' B ⊇ stage n`. Pick
`x ∈ stage n` where `junk` is discontinuous (every point of the ball
qualifies); `x ≠ P0, Pinf`. `StageHarmonicOn` yields `v` and a
`HasFDerivAt` for `z ↦ (u((chart x).symm z) : ℂ) + I·v(…)` at
`chart x x`; `HasFDerivAt` implies `ContinuousAt` there, and taking real
parts, `u ∘ (chart x).symm` is continuous at `chart x x`, hence `u` is
continuous at `x` (chart `left_inv` on the open source). But `u` equals
the glue-plus-junk on a neighborhood of `x`, which is discontinuous at
`x`. Contradiction. So `exists_stageDirichletHarmonicSolution` is
**false**, and its sorry is undischargeable.

**Repair S1**: add `boundaryPiece_subset_frontier : ∀ i, boundaryPiece i ⊆
frontier stage` to `StageBoundaryChartData` (preferred — it matches the
A2 intent and `perron-a2a3-topology-phase0.md`'s construction sketch), or
intersect with `frontier stage` inside `StageBoundaryAgreement`.

### 2.2 (S3) After S1 alone, the boundary clause is vacuous

With pieces inside the frontier and the stage open, the pieces are
disjoint from the stage. Then `agrees_boundary` is dischargeable **by
definition**: set `u n := (anything harmonic inside) on stage n` and
`u n := boundaryPotential n elsewhere`. No field of the payload links the
interior values to the frontier values — there is no continuity-up-to-
boundary requirement. The "Dirichlet problem" in the landed statement has
no analytic force; B3's uniform bounds and any maximum-principle
consumption downstream would then be unprovable from B2.

**Repair S3**: add a continuity field, e.g. `continuousOn_closure : ∀ n,
ContinuousOn (harmonicPotential n) (closure (stage n) \ {marked.P0,
marked.Pinf})`. This is what the honest Perron solution delivers and what
B3/B4 need.

### 2.3 (S2 = jc7's R2) The per-point harmonicity predicate is near-vacuous

jc7's B4 pricing (`perron-b4-conjugate-phase0.md:339`) observed, and this
audit confirms: the landed `StageHarmonicOn` (per-point `∃ v,
IsHarmonicConjugateAtReal X u v x`) is satisfied by **any** `u` whose
chart readings are pointwise real-differentiable — at each `x` choose the
affine `v` whose differential is the CR-rotation of `du` at that single
point. A different `v` per point, no harmonicity anywhere. So the field
neither pins down harmonic functions nor supports conjugate gluing.

**Repair S2**: export neighborhood-uniform harmonicity. Of jc7's two
acceptable shapes, this pricing **prefers chartwise Mathlib
`HarmonicOnNhd`**:

```
harmonicOnNhd_stage : ∀ n, ∀ x ∈ exhaustion.stage n,
  x ≠ marked.P0 → x ≠ marked.Pinf →
  ∃ r > 0, ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
    (chartAt ℂ x).symm '' ball ((chartAt ℂ x) x) r ⊆ exhaustion.stage n ∧
    InnerProductSpace.HarmonicOnNhd
      ((harmonicPotential n) ∘ (chartAt ℂ x).symm)
      (ball ((chartAt ℂ x) x) r)
```

Reason (expanded in §3.8): every Perron step natively proves
Mathlib-harmonicity of chart readings, and jc7's neighborhood-uniform
conjugate shape is then *one* routine bridge via
`exists_analyticOnNhd_ball_re_eq`; the reverse packaging would thread
conjugate witnesses through every lemma of §3. Keep `StageHarmonicOn` as
a derived corollary field if B4 wants both.

### 2.4 (S4) Base normalization over-determines the repaired problem

With S1+S3 granted (honest boundary agreement) and `base ∈ stage n`, the
solution is unique (maximum principle), and its value at `base` is the
harmonic-measure average of the boundary data plus the fixed singular
contributions — generically nonzero. Instance: boundary data `≡ C` large
on the frontier (legal A4 data once `U0/Uinf` are small and miss it)
forces `u n base` arbitrarily large. So `base_normalized` **contradicts**
`agrees_boundary`-with-continuity. Note the interaction: the landed
statement escapes this only through the S3 vacuity (paste anything,
including `0` at `base`). Granting S3 forces granting S4.

**Repair S4**: drop `base_normalized` from B2 and normalize at B5/C1 (the
holomorphic map is scaled there anyway), or restate agreement as
`EqOn (u n) (boundaryPotential n + c n)` for an existential per-stage
constant `c n`. jc7's R4 note (base anchoring is already conditional in
B4) means nothing downstream breaks either way; recommend the first.

### 2.5 (S5) Missing `IsManifold` hypothesis

`exists_stageDirichletHarmonicSolution` carries only `ChartedSpace ℂ X`.
With arbitrary (non-holomorphic) chart transitions, harmonicity of a
chart reading at `chartAt x` is unrelated to harmonicity at
`chartAt x'` for a nearby `x'` — the Perron construction (and any honest
route) transfers local results between preferred charts via
`chart_transition_contDiffOn`, which needs
`[IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ X]`. B1b and the A2/A3
providers already carry it. **Repair S5**: add the instance hypothesis to
B2 (and to the S2 field's consumers).

### 2.6 (S6) The A4 data is not yet Dirichlet data

Two independent weaknesses in `StageDipoleBoundaryControl`, both exposed
by §2.1: (a) no continuity of `boundaryPotential n` on the frontier — add
`ContinuousOn (boundaryPotential n) (frontier (exhaustion.stage n))`; (b)
`boundaryChartControl` bounds **one** piece (`StageBoundaryChartControl`
has a single `index` field) — the Perron family needs a sup bound on the
whole frontier; with (a) and frontier compactness (`X` is compact since
`e : X ≃ₜ OnePoint ℂ`) a global bound is derivable, so granting (a) makes
(b) moot; otherwise quantify the control over all indices. Relatedly,
`StageDipoleCompactBound` is existential (`compactSet := ∅` discharges
it); B2's `compactBound` fields therefore carry no Montel-grade content —
fine for B2, but D2 will need a strengthened uniform-in-`n` form on the
selected compacta (flag to the manager, no repair demanded here).

### 2.7 (S7) Geometry the spec must supply for the boundary clause

Three content-shaping additions, all to A2 (or as B2 hypotheses):

- **S7a (properness)**: nothing forbids `stage n = univ` (frontier `∅`,
  all boundary fields vacuous). Then repaired-B2 demands a harmonic
  dipole on the **closed** surface — which is `log‖·‖` of the global
  meromorphic stage map, i.e. the entire genus-0 engine in one field. B2
  must exclude it: require `stage n ≠ univ` (equivalently
  `(frontier (stage n)).Nonempty` per component; see §3.3).
- **S7b (barrier regularity)**: with pieces that are bare sets, frontier
  points can be irregular (an isolated frontier puncture admits no
  barrier, and the Dirichlet data there is unattainable — `Ω = disc ∖
  {center}` is a legal repaired instance). The classical minimal field:
  every frontier point is the endpoint of a nondegenerate continuum in
  the complement, in chart coordinates. Recommended concrete shape, per
  piece: `exterior_segment : ∀ x ∈ boundaryPiece i, ∃ w ≠ (chart i) x,
  segment ℝ ((chart i) x) w ∩ (chart i) '' ((chart i).source ∩ stage) =
  ∅` (an exterior segment condition; any polyline/polygon payload A2
  prefers implies it). Without S7b, pointwise boundary agreement is
  **false**, not merely hard.
- **S7c (marked containment)**: `P0, Pinf ∈ stage n` (or eventually in
  `n`) with small closed chart discs around each inside
  `stage n ∩ U0` / `stage n ∩ Uinf`. Without it B2 is still satisfiable
  (the germs live off-stage and can be pasted), but the construction
  degenerates and the engine's intent (dipole *inside* the stage) is
  lost. jc7's R1 (marked points *excluded from cut domains*) composes
  with S7c without tension: cuts avoid the marked discs, stages contain
  them.

### Repair summary

| # | To | Field/change | Without it |
|---|----|--------------|-----------|
| S1 | A2 | `boundaryPiece ⊆ frontier` | B2 refutable (§2.1) |
| S2 | B2 | chartwise `HarmonicOnNhd` export (= jc7 R2) | predicate near-vacuous; B4 cannot start |
| S3 | B2 | `ContinuousOn` up to closure off marked | boundary clause vacuous |
| S4 | B2 | drop/shift `base_normalized` | contradicts S3-repaired agreement |
| S5 | B2 | `[IsManifold 𝓘(ℂ,ℂ) ⊤ X]` | no honest route |
| S6 | A4 | boundary-potential continuity (+ all-piece bounds) | A4 admits junk data |
| S7 | A2 | properness, exterior-segment regularity, marked containment | boundary attainment false / content lost |

## 3. The classical argument, step by step

Target: the S1–S7-repaired statement. Fix a stage `Ω := stage n` (open,
proper, `P0, Pinf ∈ Ω` with closed marked chart discs `D̄0 ⊆ Ω ∩ U0`,
`D̄∞ ⊆ Ω ∩ Uinf`), frontier `F := frontier Ω` (compact, S7b-regular),
boundary datum `g := boundaryPotential n` (continuous on `F`, globally
bounded there). All statements are per-component of `Ω`; components not
containing a marked point get the singularity-free solution only, and the
germ fields refer to the components of `P0`/`Pinf` (if `P0, Pinf` are in
distinct components, each component handles its own pole — nothing in the
payload requires them together).

### 3.0 Route decision

Committed route: **decompose, don't improvise.** Define

```
u := −G₀ + G_∞ + H[g]
```

where `G₀ := G_Ω(·, P0)` and `G_∞ := G_Ω(·, Pinf)` are Green's functions
(positive, one `+∞` logarithmic pole each, boundary values `0`) and
`H[g]` is the singularity-free Perron solution for `g`. Each summand is a
*standard* Perron object. The alternative — one bespoke Perron family
with both signed singularities built in — was considered and rejected:
the `−∞` end (`u → −∞` at `P0`) is not `sup`-natural, so the family
would need a uniform upper cap at `P0` whose constant is exactly the
quantity the construction is trying to produce; every textbook treatment
(Green's function + harmonic measure) avoids this, and so should we.
Sign check: `G₀ = −log‖chart · − chart P0‖ + (bounded harmonic)` near
`P0`, so `−G₀` carries the `+1` germ (`u → −∞` at `P0`), and `G_∞`
carries the `−1` germ at `Pinf` (`u → +∞`); `G_∞`, `H[g]` are harmonic
and continuous near `P0` so they perturb the germ constant only
(`HasLogarithmicSingularityAtReal.add_tendsto` shape). ✓ payload signs.

### 3.1 Chart-disc toolbox (Mathlib does real work here)

All on `ℂ`, consumed through preferred charts:

- **(W1) Maximum principle for harmonic functions.** Weak and strong, on
  open connected bounded `U ⊆ ℂ`. Proof: the near-max set is open
  (mean-value `HarmonicOnNhd.circleAverage_eq` + `circleAverage_mono` +
  the strict-positivity bridge `integral_pos_iff_support_of_nonneg_ae`
  applied to `u(c) − u` on circles) and closed (continuity), then
  connectedness; boundary form via compactness of `closure U`. Mathlib's
  new `MeanValue.lean` makes this a short local development; the
  `AbsMax`/exponentiation route is *not* needed (it would require a
  global holomorphic completion that does not exist on non-simply-
  connected `U`).
- **(W2) Harmonic ∘ holomorphic.** `HarmonicAt u (f z₀) → AnalyticAt ℂ f
  z₀ → HarmonicAt (u ∘ f) z₀`: locally `u = Re F`
  (`exists_analyticOnNhd_ball_re_eq`), so `u ∘ f = Re (F ∘ f)`, conclude
  by `AnalyticAt.harmonicAt_re`. This is the conformal-invariance
  backbone; through `chart_transition_contDiffOn` (hence S5) it makes
  "harmonic in one chart" transfer to overlapping preferred charts.
- **(W3) The Poisson operator on a disc.** For `φ` continuous on
  `sphere c R`, define `P[φ](w) := Real.circleAverage (poissonKernel c w
  • φ) c R`. Four sub-leaves:
  (a) *harmonicity in `w` on the ball*: the Herglotz integral `w ↦
  circleAverage (φ • herglotzRieszKernel c w) c R` is holomorphic in `w`
  (integrand holomorphic per `θ`, denominator bounded below by `R − r`
  on compact subballs; `hasDerivAt_integral_of_dominated_loc_of_deriv_le`),
  and `P[φ] = Re` of it (`poissonKernel_eq_re_herglotzRieszKernel`,
  `ContinuousLinearMap.circleAverage_comp_comm`); harmonic by
  `AnalyticAt.harmonicAt_re`.
  (b) *normalization* `P[1] = 1`: instantiate the green representation
  `HarmonicContOnCl.circleAverage_poissonKernel_smul` at `f ≡ 1`.
  (c) *positivity/monotonicity*: kernel `≥ (R−r)/(R+r) > 0` from
  `le_re_herglotzRieszKernel`; with (b) and `circleAverage_mono`,
  `inf φ ≤ P[φ] ≤ sup φ`.
  (d) *boundary limit* `P[φ](w) → φ(z₀)` as `w → z₀ ∈ sphere c R`: the
  approximate-identity estimate — split the circle at distance `δ` from
  `z₀`, near part controlled by (b)+(c)+continuity of `φ`, far part by
  the explicit kernel formula (`poissonKernel_def`: numerator
  `R² − ‖w−c‖² → 0`, denominator `≥ (δ/2)²`). **No Mathlib support; this
  is the worst pure-math leaf.**
  Net effect: W3 = the Dirichlet problem *on a disc*, the cell from which
  Perron builds everything.
- **(W4) Harnack.** For `h ≥ 0` harmonic on a neighborhood of
  `closedBall c R`: `((R−r)/(R+r)) h(c) ≤ h(w) ≤ ((R+r)/(R−r)) h(c)` for
  `‖w−c‖ = r < R` — immediate from the representation
  (`HarmonicOnNhd.circleAverage_poissonKernel_smul`) plus the two-sided
  kernel bounds and `circleAverage_mono`. Corollary (the form Perron
  needs): an increasing sequence of harmonic functions on a disc, bounded
  at one point, converges locally uniformly; the limit is harmonic
  because each `h_k = P[h_k|circle]` and one passes to the limit in the
  integral (uniform convergence on the circle), landing in `P[·]` form —
  harmonic by W3a. This **avoids needing the mean-value converse**
  (absent from Mathlib).

### 3.2 Subharmonicity: the decision

Mathlib has no subharmonic theory, and Perron does not need one. The
family members below are **continuous** functions, and the only
subharmonicity facts used are: (i) max of two members behaves, (ii)
Poisson modification on a chart disc behaves, (iii) members lie below
harmonic functions with matching boundary values (comparison). So define
(W5) the *comparison subclass*: `v` continuous on an open `V ⊆ X` is
`PerronSubOn V` iff for every preferred-chart closed disc `D̄ ⊆ V` and
every `h` harmonic on `D`, continuous on `D̄`, with `v ≤ h` on `∂D`, one
has `v ≤ h` on `D`. API needed: closure under `max` and under Poisson
modification (replace `v` by `P[v|∂D]` inside `D` — uses W3(a–d) for
harmonicity, continuity at the seam, and `v ≤ P[v]` inside via
comparison), transfer along holomorphic charts (W2 + S5), and the
comparison/maximum lemma itself (W1 inside a disc). Harmonic functions
are members; `max(−log‖·−p‖, M)`-type glues are members. Building full
usc subharmonicity (Riesz representation, polar sets, fine topology)
would be an own-subtree of its own and is **not** priced because nothing
below consumes it — that is the answer to the task's "an approach that
needs full subharmonicity must price building it": this approach doesn't.

### 3.3 The Green's function `G_Ω(·, p)` (run twice: `p = P0`, `p = Pinf`)

Let `ℓ_p := log‖chartAt ℂ p · − chartAt ℂ p p‖` (the canonical B1a
profile shape; `profiles.u0/uinf` differ from it by a
continuous-with-limit term via their germ fields, absorbed into
constants). Family on the component `Ω_p` of `p`:

```
𝔉_p := { v : continuous on Ω_p ∖ {p}, PerronSubOn (Ω_p ∖ {p}),
         v ≤ 0 near F (limsup ≤ 0 at every frontier point),
         v + ℓ_p bounded above near p }
```

and `G_p := sup 𝔉_p` pointwise on `Ω_p ∖ {p}`.

- *Nonempty with the right lower profile*: the explicit member
  `v₀ := max(−ℓ_p + log ρ, 0)` extended by `0` outside the chart disc
  `D̄_p` of radius `ρ` (continuous across the seam since both branches
  vanish there; `PerronSubOn` by the max-closure and because `−ℓ_p` is
  harmonic off `p` — B1b-adjacent, via `AnalyticAt.harmonicAt_log_norm`
  composed with W2). `v₀ ≥ −ℓ_p + log ρ` near `p` gives the envelope's
  pole lower bound.
- *Bounded above with the right upper profile*: every `v ∈ 𝔉_p`
  satisfies `v ≤ −ℓ_p + C` on `D_p ∖ {p}` and `v ≤ C'` on `Ω_p ∖ D_p`,
  by the W1 comparison on `Ω_p ∖ (D_p ∪ {p})`-type regions against
  explicit harmonic majorants built from `−ℓ_p` (the standard
  punctured-disc comparison; the puncture is handled by the
  member-dependent cap in the family definition, pushed through W1 on
  shrinking annuli). Hence `G_p` is finite, `0 ≤ G_p ≤ −ℓ_p + C`.
- *Harmonic*: Perron's lemma (W7): at any `x₀`, take a chart disc,
  modify a maximizing sequence (Poisson modification, made increasing by
  `max` with earlier terms), apply W4's increasing-limit corollary; the
  modified limit equals `G_p` at `x₀` and is harmonic on the disc, and a
  second comparison shows it equals `G_p` *throughout* the disc.
- *Pole germ*: `G_p + ℓ_p` is harmonic on `D_p ∖ {p}` and bounded (both
  sides, from the two profile bounds) — by the removable-singularity
  leaf (W6) it extends harmonically across `p`, in particular has a
  limit at `p`. This delivers the exact
  `HasLogarithmicSingularityAtReal` germ, constants and all. W6 itself:
  on a punctured disc, compare `u` with `P[u|∂D_r] ± ε(−ℓ)` cups, let
  `ε → 0` (W1 on annuli), conclude `u = P[u|∂D_r]` extends.
- *Boundary values `0`*: barriers (W8). At `z₀ ∈ F`, the S7b exterior
  segment yields, in the chart, a barrier: rotate/scale so the segment is
  `[0, 1] ⊆ complement`; `b(z) := −Re √z`-type or `arg`-based explicit
  negative harmonic function peaking at `z₀` (built from `Complex.log` /
  `Complex.arg` on the slit plane — the project's slit-rotation toolkit
  in `HarmonicConjugate.lean` is reusable here). Standard barrier
  argument: for `ε > 0`, `εb − (sup-bound) · (barrier scaled)` traps
  every member, giving `limsup_{x→z₀} G_p(x) ≤ ε`; hence `G_p → 0` at
  every frontier point, uniformly on each piece by compactness.

### 3.4 The singularity-free solution `H[g]`

Family `𝔉_g := { v continuous on Ω̄, PerronSubOn Ω, v ≤ g on F }`;
`H[g] := sup 𝔉_g`. Constants `inf_F g` and `sup_F g` bracket the family
(W1), the envelope is harmonic by the same W7 lemma, and boundary
attainment `H[g] → g(z₀)` at each `z₀ ∈ F` uses the W8 barrier plus
continuity of `g` (S6a) — the textbook two-sided barrier estimate. This
is the step that consumes A4's data; with S6a granted, A4's one-piece
bound upgrades to the global `sup_F |g| < ∞` for free (compact frontier).

### 3.5 Assembly and the payload fields

`u := −G₀ + G_∞ + H[g]` (per component, summing only the terms whose
singular point lies in that component):

- `harmonicOnNhd_stage` (S2 shape): each summand is harmonic on
  `Ω ∖ {P0, Pinf}` chartwise; sums via `HarmonicOnNhd.add/.neg/.sub`.
- Germs: §3.3's W6 limits at `P0` (from `−G₀`, sign `+1`) and `Pinf`
  (from `G_∞`, sign `−1`); the other two summands contribute continuous
  perturbations — project lemma `add_tendsto` finishes.
- `agrees_boundary` + S3 continuity: `G`'s vanish at `F`, `H[g] → g`;
  extend `u := g` on `F` (and arbitrarily off `closure Ω`) — now the
  agreement is *earned*, with `ContinuousOn` up to the frontier.
- `base_normalized`: dropped per S4 (or `c n := −u(base)` in the shifted
  formulation).
- `compactBound` fields: honestly, for any compact `K ⊆ Ω ∖ {P0, Pinf}`,
  `|u| ≤ sup_F |g| + (pole caps on ∂D_p) + W6 constants` via W1 on
  `Ω ∖ (D₀ ∪ D_∞)` — one clean lemma (W9 in §4); as *stated* the fields
  accept `compactSet := ∅`, so this is over-delivery flagged for D2.

### 3.6 Per-`n` uniformity

B2 is per-stage; nothing above couples different `n`. The uniform-in-`n`
compact bounds that Montel/D2 need will follow from this construction
*only if* A4's boundary data is uniformly bounded on the selected
compacta-relevant stages — that is B3's job and A4's
`compactBound` upgrade (§2.6), not B2's; priced out of scope here, in
agreement with the engine plan's B2/B3 split.

### 3.7 What each interface field was for (audit trail)

S1/S3/S6 make `agrees_boundary` mean the Dirichlet condition (consumed in
§3.4); S7b is exactly the barrier input (§3.3, §3.4); S7a/S7c make the
Green's families well-posed (§3.3); S5 powers every chart transfer (W2);
S2 is the export shape (§3.8). A4's profile-agreement fields
(`agrees_with_u0_near_P0` etc.) are consumed *only* through the germ
constants in §3.3's profile normalization — they need no strengthening.

### 3.8 Bridge to the project predicates (and the R2 answer)

Everything in §3.1–3.5 lives in Mathlib's `HarmonicAt/HarmonicOnNhd`
world on chart readings — Poisson modification (W3), Harnack limits
(W4), removability (W6), maximum principle (W1) are all stated there.
The project-facing forms then come out of one funnel:
`exists_analyticOnNhd_ball_re_eq` turns a chartwise `HarmonicOnNhd` on a
ball into `F` analytic with `Re F = u`-read; `v := Im F ∘ chart` is a
*single* conjugate witness on the whole ball preimage, and
`IsHarmonicConjugateAtReal X u v y` at every `y` there follows from
`F`'s differentiability plus the project's `.congr_of_eventuallyEq`
(`HarmonicConjugate.lean:426`) — this is simultaneously jc7's
neighborhood-uniform witness and the landed `StageHarmonicOn`, derived,
not primitive. Hence the preference recorded in §2.3: B2 should *export*
chartwise `HarmonicOnNhd` (what the construction proves), and B4's
neighborhood-uniform conjugate form is W10's one routine bridge lemma.

## 4. New analytic work, hard/routine split

Sizing discipline as in `perron-engine-phase1.md` (commit = one
reviewable leaf; "own-subtree" = needs its own task sequence). Two
strata: a **toolbox** (pure `ℂ`-side, zero dependence on the stage
interfaces, fully farmable in parallel, reusable by B3/B4/B5) and the
**stage assembly** (serial after toolbox + repairs).

### Toolbox (farmable now, no interface gating)

| # | Leaf | Class | Size | Key Mathlib leaves |
|---|------|-------|------|--------------------|
| W1 | Harmonic max principle (weak + strong + boundary form) on open connected `U ⊆ ℂ` | routine-to-moderate | 2–3 commits | `HarmonicOnNhd.circleAverage_eq`, `circleAverage_mono`, `integral_pos_iff_support_of_nonneg_ae` |
| W2 | `HarmonicAt (u ∘ f)` from `HarmonicAt u`, `AnalyticAt ℂ f` | routine | 1–2 | `exists_analyticOnNhd_ball_re_eq`, `AnalyticAt.harmonicAt_re` |
| W3a | Poisson operator harmonic in `w` | moderate | 2–3 | `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `poissonKernel_eq_re_herglotzRieszKernel`, `circleAverage_comp_comm` |
| W3b,c | Kernel normalization + positivity/monotonicity | routine | 1 | `HarmonicContOnCl.circleAverage_poissonKernel_smul` at `1`, `le_re_herglotzRieszKernel` |
| W3d | **Poisson boundary limit** (approximate identity) | **hard** | 3–4 | `poissonKernel_def` + W3b,c; no further support |
| W4 | Harnack inequality + increasing-limit corollary | moderate | 2–3 | `re_herglotzRieszKernel_le`/`le_…`, `HarmonicOnNhd.circleAverage_poissonKernel_smul`, W3a |
| W5 | `PerronSubOn` mini-API (def, max, modification, comparison, chart transfer) | moderate | 3–4 | W1–W3; `chart_transition_contDiffOn` for transfer |
| W6 | Bounded-harmonic removable singularity on punctured disc (+ limit corollary) | **hard** | 3–5 | W1 (annuli), W3, `harmonicAt_congr_nhds` |

Toolbox subtotal: **15–22 commits**, of which W3d and W6 are the hard
cores. Every item is independently mergeable with no `sorry` downstream
debt, and W1/W2/W4 are consumed by B3 and B4 regardless of what happens
to B2's statement — they are safe to start before the S-repairs are even
decided.

### Stage assembly (gated: S1–S7 repairs, S5 instance, toolbox)

| # | Leaf | Class | Size | Gates |
|---|------|-------|------|-------|
| W7 | Perron envelope lemma on chart-covered open `V ⊆ X` (modify, increase, W4-limit, locality) | **hard** | 3–4 | W3–W5, S5 |
| W8 | Barriers from S7b + boundary attainment (Green: `→ 0`; `H[g]`: `→ g`) | **hard, spec-gated** | 4–6 | S7b field landed in A2, W1, W5; reuses slit-plane toolkit from `HarmonicConjugate.lean` |
| W9 | Green's function per pole: family, explicit member, two-sided pole profile, W6 germ | **hard** | 3–5 (shared between the two poles) | W5–W8, S7a/c |
| W10 | `H[g]` instantiation + assembly `u = −G₀ + G_∞ + H[g]`, all payload fields incl. S2 export and the `HarmonicOnNhd → IsHarmonicConjugateAtReal` bridge | moderate | 3–4 | everything above, S2–S4, S6 |
| W11 | Honest compact bounds lemma (max principle vs pole caps + frontier sup) | routine-to-moderate | 1–2 | W1, W9 |

Assembly subtotal: **14–21 commits**, serial spine W7 → W8 → W9 → W10,
with W11 farmable off W9.

### Interface repairs (manager-routed, not analytic work)

S1, S6, S7 are A2/A4-side statement edits (jc1's files) — each is a
one-commit statement change plus provider-side fallout owned by the A2/A3
lane; S2–S5 are B2-side (this node's own file). None is analytic work,
but **W8 cannot be tasked until S7b exists** and **no B2 Lean work at all
should be tasked until S1 lands** (the sorry is currently undischargeable).

## 5. Honest conclusion

**Total expected scale: 29–43 commits, hard own-subtree** — the engine
plan's classification of B2 as "the worst single node" is confirmed, not
softened. Roughly half is a reusable potential-theory toolbox with clean
Mathlib leaf support (the pin is *better* than the engine plan recorded:
mean-value property and Harnack-kernel bounds have landed upstream since)
and no interface gating; the other half is stage-side and cannot start
until the statement repairs land.

**The single worst sub-step**: pure math — W3d, the Poisson boundary-limit
theorem (classical approximate-identity analysis with zero Mathlib
support, and every later boundary statement stands on it). Spec-gated —
W8, the barrier subtree, which is *unprovable* (not merely hard) until A2
supplies S7b geometry.

**What would force a strategy revisit:**

1. *Repairs refused.* Without S1 the obligation is refutable and the only
   honest outcome is BLOCKED-on-statement. Without S5 there is no honest
   route. These are not negotiable in substance, only in packaging.
2. *The manager weakens the boundary clause instead.* If B2's
   `agrees_boundary`+S3 is replaced by maximum-principle bounds
   (`inf_F g ≤ u ≤ sup_F g`-shaped fields), then W3d and W8 drop out
   entirely and S7b is not needed: the price falls to roughly 18–28
   commits. The cost is moved, not destroyed — B5/C's noncollapse
   normalization and the final gluing will eventually need *some*
   boundary control — but possibly to a place where weaker statements
   suffice. This is the manager's biggest lever and deserves an explicit
   decision before any W8-lane work is tasked.
3. *Mathlib catches up.* The harmonic library is visibly under active
   development (`MeanValue.lean`, `Liouville.lean` are new). If
   subharmonicity, a disc Dirichlet theorem, or Harnack land upstream,
   re-survey before building W3–W6; each upstream landing deletes a
   toolbox row.
4. *The Hilbert-space alternative stays dead.* The Dirichlet-principle /
   Weyl-lemma route was checked and has strictly less substrate (no
   Weyl lemma, no Sobolev-on-surfaces, no Lax–Milgram-to-PDE bridge in
   the pin); it would only become competitive if Mathlib's PDE side
   outpaces its potential-theory side. Not recommended now.

A successful Phase 1, in order: (i) manager rules on S1–S7 and the
weaken-vs-barrier decision (item 2); (ii) toolbox W1/W2/W4 tasked
immediately (safe under every ruling); (iii) W3, W5, W6 tasked; (iv)
statement repairs land; (v) assembly spine W7–W11. The first Lean commit
against the B2 sorry itself is step (v) — months out, exactly as the
engine plan priced it.

## Anti-circularity audit

- The open spine providers `exists_stageBorderedExhaustion`,
  `exists_stageCutSystem`, `exists_stageDipoleBoundaryControl` are
  consumed **only as hypotheses** (their structure types appear as
  arguments of B2); no step above cites them as proved, and the §2.1
  counter-instance constructs its A2/A4 *instances* by hand, not through
  the providers.
- Nothing routes through B4/B5/Montel outputs (those consume B2, not
  conversely), through the fixed-pole RR chain, or through any
  genus-zero biholomorphism fact.
- No `True`-stub is load-bearing anywhere in §3 (see non-substrate list).
- Every Mathlib citation in §§1,3,4 was verified by name in the local
  checkout (`.lake/packages/mathlib/`) on 2026-06-11; file:line given at
  first use.

## Explicit non-substrate

Present in the tree but cited nowhere above as support:

- `True`-stubs: `HasLogarithmicSingularityAt` (`HarmonicDipole.lean:11`),
  `IsHarmonicOff` (`:304`), `harmonic_conjugate_exists_locally`
  (`HarmonicConjugate.lean:15`), `continuous_cr_to_holomorphic_bridge`
  (`:1437`), and the six `CompactRiemannSurface.lean` stubs already
  disowned by the engine plan.
- `Mathlib/Analysis/Complex/RiemannMapping.lean` — planar-only, engine
  plan's rejection stands.
- `Complex.AbsMax` for the harmonic maximum principle — listed PRESENT
  in §1 and usable by B3 for *holomorphic* readings, but deliberately
  not used for W1 (the exponentiation route fails on non-simply-
  connected domains; W1 goes through the mean value property instead).
- The sorry-dependent stage providers listed in the audit above.

## Search log

- Read on the branch: `StageDirichlet.lean`, `StageExhaustion.lean`,
  `StageDipoleBoundary.lean`, `StageEventualContainment.lean`,
  `PerronStageMarkedData.lean`, `PerronStageDipoleProfile.lean`,
  `PerronStageDipolePotential.lean`, `PerronStageLogConjugate.lean`,
  `StageHarmonicConjugate.lean`, `HarmonicDipole.lean`,
  `HarmonicConjugate.lean` (full), `OnePointCxIsManifold.lean`
  (instances); docs: `perron-engine-phase1.md`,
  `perron-a2a3-topology-phase0.md`, `perron-b4-conjugate-phase0.md`,
  `montel-phase05-stage-construction.md`, `rr-dimension-input-phase0.md`.
- Mathlib local-checkout greps (2026-06-11): `subharmonic` (0 hits);
  `dirichlet` under `Analysis/` (number theory only); `harnack` (0);
  `poissonIntegral|PoissonIntegral|schwarzIntegral` (0); `weyl` under
  `Analysis/` (0); `greenFunction|harmonicMeasure` (0); `morera`
  (`HasPrimitives.lean` only); `circleAverage` (definition + API as
  cited); declaration listings of
  `InnerProductSpace/Harmonic/{Basic,Constructions,HarmonicContOnCl}`,
  `Complex/Harmonic/{Analytic,MeanValue,Poisson,Liouville}`,
  `Complex/{Poisson,AbsMax,HasPrimitives}`,
  `Calculus/ParametricIntervalIntegral`,
  `MeasureTheory/Integral/{CircleAverage,IntervalIntegral/Basic}`.
- Confirmed `RemovableSingularity.lean` is holomorphic-only; confirmed
  no `HarmonicAt.comp` beyond `comp_CLM`/`comp_CLE`.
