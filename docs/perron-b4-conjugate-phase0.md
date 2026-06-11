# Perron B4 Conjugate/Period-Kernel Phase 0 Paper Proof

Tracking: GitHub issue #232, Path A, engine node
`lem:stage-harmonic-conjugate-exists-on-cut`, Lean frontier obligation
`exists_stageHarmonicConjugatesOnCuts` in
`Jacobian/HolomorphicForms/StageHarmonicConjugate.lean`.

This note prices the global harmonic-conjugate / period-killing argument on
the cut stage domains.  It is a planning document only: no Lean declarations
are added or changed, and nothing here claims the B4 obligation is solved.
The open spine providers (`exists_stageBorderedExhaustion`,
`exists_stageCutSystem`, `exists_stageDipoleBoundaryControl`,
`exists_stageDirichletHarmonicSolution`) are consumed as hypotheses
throughout, never as conclusions.

## Scope

Given a B2 stage potential `u n` (harmonic on the cut domain away from the
marked points `P0`, `Pinf`, with `±1` logarithmic profiles there), B4 must
produce a real conjugate `v n` on `cutDomain n` such that `u n + I * v n` is
chart-pullback complex differentiable at every point of the cut domain away
from the marked points — the shape demanded by `StageConjugateOnCut` inside
`StageHarmonicConjugatesOnCuts`.  The document covers: the substrate survey
(project and Mathlib, including the previously unsurveyed
`IsSimplyConnected`-to-analysis corner), the marked-end/cut geometry
analysis, the new analytic work with per-item sizing, and an honest
conclusion.  It stops before B5 (holomorphic stage coordinate) and C
(normalization).

## Substrate: project chart-local conjugate layer

`HarmonicConjugate.lean` (0 sorries) was read declaration by declaration.
Grouped by role:

- **Core predicate.** `IsHarmonicConjugateAtReal X u v x`: there is an
  `f' : ℂ →L[ℂ] ℂ` with `HasFDerivAt` of the chart pullback
  `z ↦ ↑(u ((chartAt ℂ x).symm z)) + I * ↑(v ((chartAt ℂ x).symm z))` at
  `(chartAt ℂ x) x`.  This is complex differentiability of `u + iv` **at a
  single point**, in the chart at that point.  Companion predicate
  `IsHolomorphicInChartReal`; off-singular predicate `IsHarmonicOffReal X P Q
  u` (at every `x ∉ {P, Q}` *some* `v` works at `x` — existential per point).
- **Closure lemmas** (generic, reusable): `.neg`, `.add`,
  `.add_const_const`, `.congr_of_eventuallyEq`.  These are exactly the
  transport lemmas a gluing argument needs ("local conjugate plus a constant
  is still a conjugate", "agree near `x` transfers the predicate").
- **Concrete witnesses on ℂ**: `re_im_at`, `log_arg_at_slitPlane`,
  `log_arg_sub_at_slitPlane`, rotated/normalized variants
  (`log_arg_rotated_normalized_at`, `neg_log_arg_rotated_normalized_at`),
  the slit-rotation coverage lemmas (`slit_two_of_four_helper`,
  `slit_rotation_for_two_nonzero`, `exists_rotation_to_slitPlane`), and the
  full-coverage dipole conjugate `dipole_conjugate_exists_at_off_PQ`
  (for every `x ∉ {P, Q}` in ℂ some `arg`-difference is a conjugate of the
  canonical dipole at `x`).
- **Transfer to `X`**: `chart_pullback_lift_at_basepoint` (ℂ-side conjugate
  pair pulls back through `chartAt ℂ P` to a conjugate pair at `P`),
  `chart_transition_contDiffOn` (transition maps are `ContDiffOn ℂ ⊤` under
  `IsManifold`), `dipole_compose_chart_has_conjugate`,
  `chart_pullback_dipole_has_conjugate_at_off_PQ` (the chart-pullback dipole
  on `X` admits a conjugate at every `x ∉ {P, Q}` with same-chart
  hypotheses), `dipole_pullback_isHarmonicOffReal_on_X`,
  `existence_of_dipole_harmonic_off_on_X`.
- **Known cheats still present**: `harmonic_conjugate_exists_locally` and
  `continuous_cr_to_holomorphic_bridge` conclude `True`-weighted
  existentials; they are not consumed by B4.

`PerronStageLogConjugate.lean` (B1b, 0 sorries) mirrors the dipole path for
single logs: `log_compose_chart_has_conjugate`,
`chart_pullback_log_has_conjugate_at_off_P` (+ `neg` variant),
`canonicalGenusZeroStageDipoleProfiles`, and per-point conjugates for the
B1c glued potential on `U0 \ {P0}` and `Uinf \ {Pinf}`.

**Where the layer stops.** Every result is *at a point*, with a witness `v`
that may change from point to point.  There is: no notion of a conjugate on
a set with a single witness (other than the brand-new B4 target predicate
itself), no uniqueness/constant-difference lemma, no gluing along chains or
paths, and no period statement.  The global story is genuinely absent — B4
is the node that must create it.

## Substrate: interfaces consumed

- `StageConjugateReady X cutDomain` (A3, `StageExhaustion.lean`):
  `IsOpen cutDomain` and `IsSimplyConnected cutDomain`.
- `StageCutSystem` (A3): `cutDomain n`, `cutSet n` inside `stage n`,
  `cutDomain_disjoint_cutSet`, eventual containment of selected compacta in
  cut domains, eventual avoidance of cut sets, `conjugateReady` per stage.
  Note: `StageCutSystem` does **not** currently know the marked data.
- `StageDirichletHarmonicSolution` (B2, `StageDirichlet.lean`):
  `harmonicPotential n` with `harmonicOn_stage` (`StageHarmonicOn`),
  boundary agreement, `base_normalized`, `has_pos_log_profile` /
  `has_neg_log_profile` at `P0` / `Pinf`, compact bounds.
- B4 payload (`StageHarmonicConjugate.lean`): `harmonicConjugate n`,
  `conjugateOnCut` (`StageConjugateOnCut`: one `v` conjugate at every point
  of `cutDomain n` off the marked points), `base_phase_normalized`
  (conditional on `base ∈ cutDomain n`), selected-compact readiness fields,
  compact-bound copies.

The B4 *output* predicate is honest: a single `v` with chart-pullback
differentiability of `u + iv` at every point of an open set forces genuine
chartwise holomorphy (differentiability on an open set upgrades to
analyticity), so `True`-style or per-point-linear cheats cannot discharge
`conjugateOnCut` for a `u` with real log singularities.

## Substrate: Mathlib survey of the simply-connected/analysis corner

All claims below were verified in the local checkout
(`.lake/packages/mathlib`, pin v4.31.0-rc1).  This corner had never been
surveyed for the engine; the findings materially change the B4 plan.

### What exists

- `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`:
  `IsSimplyConnected s` is *defined* as `SimplyConnectedSpace s` (subtype).
  Provides `IsSimplyConnected.simplyConnectedSpace`, `.isPathConnected`,
  `.nonempty`, `SimplyConnectedSpace.paths_homotopic` (any two paths with
  the same endpoints are homotopic), instance
  `SimplyConnectedSpace → PathConnectedSpace`, homeomorphism transfer
  lemmas.
- `Mathlib/Topology/Homotopy/Lifting.lean` — **the load-bearing find**:
  - `IsLocalHomeomorph.monodromy_theorem` (needs `IsSeparatedMap p`): if a
    homotopy of paths lifts pathwise through a separated local
    homeomorphism with fixed starting lift, the endpoint lifts agree.  Its
    docstring *explicitly describes the étale-space-of-germs application*
    ("points are analytic germs … local homeomorphism and a separated
    map").
  - `IsLocalHomeomorph.existsUnique_continuousMap_lifts`
    (`[PathConnectedSpace A] [LocPathConnectedSpace A]` + per-path lift
    existence + endpoint uniqueness): unique global continuous lift.
  - `IsCoveringMap.exists_path_lifts` / `liftPath` / `liftHomotopy` /
    `monodromy`, and
    `IsCoveringMap.existsUnique_continuousMap_lifts`
    `[SimplyConnectedSpace A] [LocPathConnectedSpace A]`.
  - `IsCoveringMapOn.existsUnique_continuousMap_lifts` — the set-restricted
    version, exactly shaped for "covering over `cutDomain`".
- `Mathlib/Analysis/Complex/BranchLogRoot.lean`:
  `Complex.exists_continuousOn_eqOn_exp_comp` — for `X` locally path
  connected, `U` open with `IsSimplyConnected U`, `g` continuous and
  nonvanishing on `U`, there is a continuous `f` with `exp ∘ f = g` on `U`.
  A complete worked example of the covering-lift pattern (uses
  `isCoveringMapOn_exp` from `Mathlib/Analysis/Complex/CoveringMap.lean`).
  `Mathlib/Analysis/Complex/RiemannMapping.lean` then shows the standard
  upgrade pattern from a continuous branch to a differentiable one
  (`exists_injective_not_dense_image_deriv_ne_zero`).
- `Mathlib/Analysis/Complex/HasPrimitives.lean`: Morera-style primitives —
  `IsConservativeOn`, `IsExactOn`, `DifferentiableOn.isExactOn_ball`
  (**balls only**) and `Differentiable.isExactOn_univ` (**univ only**).
- `Mathlib/MeasureTheory/Integral/CurveIntegral/{Basic,Poincare}.lean`:
  curve integrals `∫ᶜ x in γ, ω x` of 1-forms `ω : E → E →L[𝕜] F` along
  `Path a b` **on normed spaces**, with `symm`/`trans`/segment algebra;
  Poincaré lemma for **convex** sets
  (`exists_forall_hasFDerivAt_of_fderiv_symmetric`); homotopy invariance of
  curve integrals of closed forms **only along C² homotopies**
  (`curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable`).
  The file header states verbatim that the simply-connected Poincaré lemma
  is future work, and `Basic.lean` cites the WIP formalization (#24019).
- `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`:
  `HarmonicAt.differentiableAt_complex_partial` /
  `analyticAt_complex_partial` (`z ↦ fderiv ℝ f z 1 − I * fderiv ℝ f z I`
  is holomorphic where `f` is harmonic) and
  `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`
  (**a harmonic function on a ball is the real part of a function analytic
  on that ball** — the canonical ball-local conjugate, built internally by
  integrating the complex partial with `isExactOn_ball`).
- Supporting topology: `ChartedSpace.locPathConnectedSpace`
  (`Mathlib/Geometry/Manifold/ChartedSpace.lean:268` — so
  `LocPathConnectedSpace X` is free from `ChartedSpace ℂ X`),
  `IsOpen.locPathConnectedSpace` for subtypes,
  `IsOpen.is_const_of_fderiv_eq_zero` / `exists_is_const_of_fderiv_eq_zero`
  (constancy from vanishing derivative on preconnected opens, in
  `Mathlib/Analysis/Calculus/MeanValue.lean`),
  `isLocallyConstant_of_fderiv_eq_zero`, the `IsLocallyConstant` API,
  `Filter.Germ` (germs of functions at a filter, with quotient API),
  `lebesgue_number_lemma` (only needed by the fallback route).

### What is missing (honest negatives)

- **No simply-connected primitive theorem**, planar or otherwise: nothing of
  the form "`f` holomorphic on open simply connected `U` ⇒ `f` has a
  primitive on `U`".  Primitives stop at balls/univ; Poincaré stops at
  convex sets; the C⁰-homotopies provided by `IsSimplyConnected` do not meet
  the C²-homotopy hypothesis of the curve-integral invariance theorem, and
  no C⁰→C² homotopy smoothing exists.
- **No harmonic-conjugate-on-simply-connected theorem** (the ball case
  exists, as above; the global case does not).
- **No 1-forms, curve integrals, or primitives on charted spaces /
  manifolds**: the entire `CurveIntegral` development is for normed spaces
  `E`; there is no path integration of the conjugate differential on a
  Riemann surface.
- **No étale-space construction** for sheaves of functions usable here
  (categorical sheaf stalks exist but there is no topological espace étalé
  with an `IsLocalHomeomorph`/`IsCoveringMap` bridge); the
  `monodromy_theorem` docstring describes the pattern but the construction
  is left to the user.
- No `Subharmonic`/Perron API (re-confirming the engine-plan finding).

## The two classical routes, priced

### Route (a): integrate the holomorphic derivative

Classically `v = Im ∫ 2(∂u/∂z) dz`.  Two blockers, one fatal in present
form:

1. On the **surface**, `2∂u/∂z` is not a function — it is chart data whose
   global object is a holomorphic 1-form, and Mathlib has no 1-forms or
   curve integrals on charted spaces.  The cut domain has no global chart
   (`_e` is only topological, and building a global conformal chart is the
   whole uniformization problem), so the planar `CurveIntegral` development
   cannot be applied.  Building manifold-level 1-form path integration with
   homotopy invariance from scratch is a larger project than B4 itself.
2. Even in the **plane**, the simply-connected step is missing: primitives
   exist on balls only, and the curve-integral homotopy invariance needs C²
   homotopies while `IsSimplyConnected` provides C⁰ ones.

Verdict: route (a) is not executable on this Mathlib pin without
out-of-scope infrastructure.  Rejected for B4.  (Revisit trigger: the
simply-connected Poincaré lemma announced in `CurveIntegral/Poincare.lean`
lands in a future Mathlib.)

### Route (b): glue chart-local conjugates, kill monodromy by simple connectivity — RECOMMENDED

The local-to-global mechanism that *is* fully supported by the pin is
covering-space lifting.  Architecture:

1. **Local layer.** At every `x ∈ cutDomain n` (marked points are not in
   the cut domain — see the geometry section), `u n` admits a conjugate
   `v_x` on a *connected open neighborhood* `U_x` (one witness for the
   whole neighborhood; see interface finding F1 below for why this must be
   strengthened in B2).
2. **Constant-difference lemma.** Two conjugates of `u` on a preconnected
   open `U ⊆ X` differ by a real constant: their difference `w` has
   `i·w` equal to a difference of chart-pullback-differentiable functions,
   CR forces the chartwise derivative of `w` to vanish,
   `IsOpen.is_const_of_fderiv_eq_zero` gives chart-local constancy, and
   `IsLocallyConstant` propagates over the preconnected set across charts.
3. **Conjugate-germ covering space.** Let `Ω := cutDomain n` and define
   `E := Σ x : Ω, ConjGerm x`, where `ConjGerm x` is the set of
   `Filter.Germ (𝓝 (x : X)) ℝ` classes of local conjugates of `u n` at
   `x`, topologized by declaring the section images
   `{(y, germ_y v) | y ∈ W}` (for `v` a conjugate on open `W ⊆ U_x`) to be
   a basis.  Projection `p : E → X` (or `E → Ω`).
   - `p` is a local homeomorphism: each section over a connected `W` is an
     open embedding inverse to `p`.
   - `p` is separated: two distinct germs at `x` differ by a nonzero
     constant on a connected neighborhood (step 2), so their basic
     neighborhoods are disjoint.
   - `p` is `IsCoveringMapOn` over `Ω`: over a connected conjugate ball
     `U_x`, every germ at `y ∈ U_x` equals `germ_y (v_x + c)` for a unique
     `c : ℝ` (step 2 again), giving the trivialization
     `p⁻¹(U_x) ≃ U_x × ℝ_discrete`.  Fibers over `Ω` are nonempty by
     step 1.
4. **Period killing = simply-connected lifting.**  `StageConjugateReady`
   gives `IsSimplyConnected Ω`, i.e. definitionally
   `SimplyConnectedSpace Ω`; `LocPathConnectedSpace Ω` follows from
   `ChartedSpace.locPathConnectedSpace` (for `X`) plus
   `IsOpen.locPathConnectedSpace`.  Apply
   `IsCoveringMapOn.existsUnique_continuousMap_lifts` to the inclusion
   `C(Ω, X)` with a base germ `e₀`: the unique continuous lift
   `F : C(Ω, E)` is a global section.  This is precisely where the periods
   die: the deck translations of `E` are the classical periods of the
   conjugate differential, and `paths_homotopic` (simple connectivity)
   plus the monodromy machinery in `Lifting.lean` make the lifted endpoint
   path-independent.  No curve integral is ever formed.
5. **Extraction.** `val : E → ℝ`, `val (x, g) := g.value`-at-`x` (well
   defined on conjugate germs; on each basic section image `val ∘ section =
   v` is continuous, and sections cover `E`).  Set `v n := val ∘ F` on `Ω`,
   extended by `0` elsewhere.  Locally `v n = v_x + c`, so
   `IsHarmonicConjugateAtReal X (u n) (v n) y` at every `y ∈ Ω` via the
   existing closure lemmas `.add_const_const` and `.congr_of_eventuallyEq`.
6. **Normalization and packaging.**  Choose `e₀` over `base` with value `0`
   when `base ∈ Ω` (then `base_phase_normalized` is direct); otherwise any
   anchor (the field is conditional).  The `eventually_compactReady` /
   `compactReadyBound` fields follow from the cut system's
   `eventually_contains_selected` and `cuts_avoid_selected_eventually`
   (`Filter.eventually_atTop` converts between the `∀ᶠ` and `∃ N` forms);
   `compactBound` / `conjugateReady` are definitional copies.

A worked Mathlib precedent for steps 3–5 exists:
`Complex.exists_continuousOn_eqOn_exp_comp` performs the same
lift-extract-restrict dance against `isCoveringMapOn_exp` (with the
covering already in hand).  Our extra cost over that precedent is exactly
the construction of the germ covering (steps 2–3).

**Fallback** if the germ-space topology stalls: hand-rolled chain
increments along paths (subdivide via `lebesgue_number_lemma`, sum local
conjugate increments, prove subdivision- and choice-independence via the
constant-difference lemma, then grid-prove homotopy invariance).  This
reimplements the `Lifting.lean` grid argument and is priced strictly worse
(8–12 commits of delicate compactness bookkeeping); listed only as
contingency.

### Why the exp shortcut does not apply directly

`exists_continuousOn_eqOn_exp_comp` cannot be invoked with `g := exp(u+iv)`
— that presupposes `v`.  No canonical nonvanishing `g` with
`log g = u + iv` exists before B4 concludes.  (B5 may later *use* the exp
covering for its own purposes; that is its interface decision.  Note for
B5/D2: `|exp (u + iv)| = exp u`, so no compact bounds on `v` are ever
needed downstream — the landed B4 payload correctly exports none.)

## Marked-end behavior and cut geometry

The conjugate of a `±1` log pole is `±arg` — multivalued with period
`±2π` around the pole.  Concretely: if `P0` were an *interior* point of an
open set `D` on which a single-valued conjugate `v` of `u` existed off
`P0`, then `f := u + iv` would be chartwise holomorphic on a punctured
disc at `P0` with `Re f − log|z − z₀| → c`; then `exp f` extends over
`z₀` with a simple zero, so `f' = (exp f)'/(exp f)` has residue `1` at
`z₀`, contradicting that `f'` has the primitive `f` on the punctured
disc.  Hence:

**(F2) `exists_stageHarmonicConjugatesOnCuts` is classically false whenever
`marked.P0 ∈ cutDomain n` (or `marked.Pinf ∈ cutDomain n`).**  The
`x ≠ P0`, `x ≠ Pinf` guards in `StageConjugateOnCut` do not save it: the
period obstruction lives on the punctured neighborhood, which the guards
keep inside the demanded region.  Note `IsSimplyConnected cutDomain` does
not help: a disc is simply connected, yet `log‖z‖` has no single-valued
conjugate on the punctured disc.

The classical cut geometry resolves this: the cut set contains an arc
joining `P0` to `Pinf` (or each marked point to the stage frontier), the
marked points lie in the closure of the cut set, and the cut domain is the
stage minus the cuts.  Then the marked points are **not** in the (open)
cut domain — they cannot be, since the cut accumulates at them — every
loop in the cut domain is unable to wind around a single marked point, and
`IsSimplyConnected cutDomain` (with the punctures *outside* the domain) is
exactly the right hypothesis, unweakened.  jc1's
`simplyConnectedEnoughForConjugates` field survives as stated **provided**
the marked points are excluded from the cut domain.

### Brokered interface requests (named precisely)

- **(R1) to A3 / `StageCutSystem`:** add marked-point exclusion.  Since
  `StageCutSystem` does not currently take `marked`, either thread
  `GenusZeroStageMarkedData` into its signature or add a marked-aware
  wrapper consumed by B4, with fields
  `P0_notMem_cutDomain : ∀ n, marked.P0 ∉ cutDomain n` and
  `Pinf_notMem_cutDomain : ∀ n, marked.Pinf ∉ cutDomain n`.
  Without R1, B4 is unprovable by F2.  (No puncturing of the
  `IsSimplyConnected` field is needed once R1 holds.)
- **(R2) to B2 / `StageDirichletHarmonicSolution`:** strengthen
  `StageHarmonicOn` to a neighborhood-uniform witness.  The landed
  per-point form
  `∀ x ∈ stage, x ≠ P0 → x ≠ Pinf → ∃ v, IsHarmonicConjugateAtReal X u v x`
  is satisfied by **any** `u` whose chart readings are real-differentiable,
  harmonic or not: at each `x` take `v` to be the affine function whose
  chart differential is the CR rotation of `du` at the single chart point —
  `HasFDerivAt` at one point follows, with a different `v` per `x`.  So no
  conjugate-gluing argument (indeed no true statement) can start from it.
  Requested field shape:
  `harmonicOnNhd_stage : ∀ x ∈ stage, x ≠ P0 → x ≠ Pinf → ∃ U, IsOpen U ∧
  x ∈ U ∧ U ⊆ stage ∧ ∃ v, ∀ y ∈ U, IsHarmonicConjugateAtReal X u v y`
  (one witness per neighborhood).  Alternative acceptable shape: chartwise
  `InnerProductSpace.HarmonicOnNhd` of the chart readings, from which
  `exists_analyticOnNhd_ball_re_eq` reconstructs the neighborhood witness
  on chart balls (the bridge exists in the pin and is routine).  B2's
  Perron construction produces genuine harmonicity either way; R2 only
  asks that it be *exported* in neighborhood-uniform form.
- **(R3, flag) selected family vs marked points:** R1 plus
  `eventually_contains_selected` forces every selected compactum to avoid
  `P0` and `Pinf`.  The Montel/selected-compact family used by the engine
  must therefore exclude the marked points; convergence of stage maps near
  the marked ends must come from the marked-neighborhood profile data
  (B1b's conjugates on `U0 \ {P0}`, `Uinf \ {Pinf}`) or
  removable-singularity arguments on the B5/C side, not from cut domains.
  This is an architecture constraint the manager should confirm with the
  A-side and the Montel layer.
- **(R4, minor) base anchoring:** nothing guarantees
  `marked.base ∈ cutDomain n`; `base_phase_normalized` is conditional, so
  B4 stays provable, but the normalization is vacuous for stages missing
  the base.  If C1 needs the anchored phase, add eventual base membership
  to the cut system.

## New analytic work, hard/routine split

All items assume R1 and R2 granted.  Sizing follows the
`perron-engine-phase1.md` discipline (commit = one reviewable leaf).

- **W1 (routine, 1–2 commits).** Constant-difference lemma: two conjugates
  of `u` on a preconnected open `U ⊆ X` differ by a constant.  Leaves:
  pointwise derivative-zero from CR (purely imaginary holomorphic
  difference), `IsOpen.is_const_of_fderiv_eq_zero` chartwise,
  `IsLocallyConstant` glue across charts.  The chart-pullback bookkeeping
  is the only friction.
- **W2 (routine, 1 commit).** Neighborhood normalization: from R2's field,
  produce at each cut-domain point a *connected* open (chart-ball
  preimage) with a single conjugate witness; shrinking and
  chart-source-intersection lemmas.
- **W3 (hard, 3–4 commits).** The conjugate-germ space: `ConjGerm` as a
  subtype of `Filter.Germ (𝓝 x) ℝ`, the sigma type `E`, the
  section-image topology (generated-by; basis lemmas), continuity of
  sections, `IsLocalHomeomorph p`.  This is the worst sub-step: a new
  topological space with a bespoke basis, though every ingredient is
  elementary and W1 supplies the only mathematical content.
- **W4 (hard, 2–3 commits).** `IsSeparatedMap p` and
  `IsCoveringMapOn p (cutDomain n)`: disjointness of distinct-constant
  sections, the `U_x × ℝ_discrete` trivialization, fiber nonemptiness from
  W2 (which needs R1 so that the cut domain misses the marked points).
- **W5 (routine, 1 commit).** Instances: `SimplyConnectedSpace ↥(cutDomain
  n)` from `StageConjugateReady` (definitional unfold),
  `LocPathConnectedSpace X` via `ChartedSpace.locPathConnectedSpace`, then
  `IsOpen.locPathConnectedSpace`.
- **W6 (routine/hard seam, 2 commits).** Apply
  `IsCoveringMapOn.existsUnique_continuousMap_lifts` to the inclusion,
  define `val`, prove its continuity from the section cover, extract
  `v n`, and discharge `StageConjugateOnCut` via `.add_const_const` +
  `.congr_of_eventuallyEq`.
- **W7 (routine, 1–2 commits).** Package `StageHarmonicConjugatesOnCuts`:
  base-anchored germ for `base_phase_normalized`, `Filter.eventually_atTop`
  conversion for `compactReadyBound`, definitional copies for
  `conjugateReady_eq_cutSystem` / `compactBound_eq_dirichlet`.

Total: 11–15 commits; two genuinely hard leaves (W3, W4) whose mathematical
content is fully reduced to W1 plus standard topology.  The covering-space
consumption side (path lifting, monodromy, simply-connected lifting) is
**zero new work** — it is all in `Mathlib/Topology/Homotopy/Lifting.lean`.

## Risks and revisit triggers

- **R1/R2 refused or reshaped**: B4 cannot start.  F2 makes R1
  non-negotiable in substance (only its packaging is negotiable); R2 has a
  second acceptable shape (Mathlib `HarmonicOnNhd`) if jc6's B2 pricing
  prefers it.
- **Germ-space topology friction (W3)**: if the bespoke basis fights
  Mathlib's `TopologicalSpace.generateFrom` API, fall back to the concrete
  twisted-product description (`Ω × ℝ` as a set, basic opens
  `{(y, v_x y + c) | y ∈ W}`), which avoids `Filter.Germ` quotients at the
  cost of a choice of `v_x` per point; or, last resort, the hand-rolled
  chain route (priced worse, above).
- **Mathlib catches up**: the simply-connected Poincaré lemma
  (`CurveIntegral/Poincare.lean` header, WIP #24019) or a Riemann-mapping
  completion would reopen route (a) with lower cost; if it lands before W3
  starts, re-price.
- **B5 interface**: B4 hands over only `v n` on the cut domain with
  pointwise conjugacy and the phase anchor.  If B5 chooses the
  integrated-primitive variant instead of `exp (u + I v)`, it needs
  nothing further from B4; if it needs boundary behavior of `v` near the
  cuts, that is new scope (nothing in the landed payload promises it, and
  `|exp(u+iv)| = exp u` suggests it is never needed).

## Conclusion

The B4 period-killing argument is formalizable on the current pin at a
total scale of 11–15 commits, with the worst sub-step being the
construction of the conjugate-germ covering space (W3/W4, 5–7 commits) —
strictly smaller than B2's Perron subtree.  The decisive survey finding is
that Mathlib's `Topology/Homotopy/Lifting.lean` already contains the whole
monodromy/lifting engine (including a simply-connected unique-lifting
theorem shaped for `IsCoveringMapOn`), while the often-assumed analytic
bridge — primitives of holomorphic functions on simply connected opens —
does **not** exist and route (a) is therefore rejected.  Two interface
corrections are prerequisites: marked points must be excluded from the cut
domains (else the obligation is classically false), and B2's harmonicity
field must carry one conjugate witness per neighborhood rather than per
point (else it admits non-harmonic potentials and supports no gluing).
Both are statement-level adjustments to open frontier interfaces, not
reshapes of any proven code.

## Search log

- Project: read decl-by-decl `HarmonicConjugate.lean`,
  `StageExhaustion.lean`, `StageDirichlet.lean`, `StageDipoleBoundary.lean`,
  `StageHarmonicConjugate.lean`, `PerronStageMarkedData.lean` (structure
  fields), decl lists of `PerronStageLogConjugate.lean`,
  `PerronStageDipoleProfile.lean`; `docs/perron-engine-phase1.md`,
  `docs/perron-a2a3-topology-phase0.md`.
- Mathlib greps over the local checkout: `IsSimplyConnected` (3 files:
  `SimplyConnected.lean`, `BranchLogRoot.lean`, `RiemannMapping.lean`);
  `primitive` under `Analysis/Complex` (`HasPrimitives.lean`,
  `Harmonic/Analytic.lean`); `monodromy` (only
  `Topology/Homotopy/Lifting.lean`); `curveIntegral|pathIntegral|
  lineIntegral` (`MeasureTheory/Integral/CurveIntegral/*`);
  `lebesgue_number_lemma`; `is_const_of_fderiv_eq_zero` and neighbors in
  `MeasureTheory…/MeanValue.lean`; `LocPathConnectedSpace` under
  `Geometry` (found `ChartedSpace.locPathConnectedSpace`) and
  `Topology/Connected/LocPathConnected.lean`; `IsCoveringMapOn` in
  `Topology/Covering/Basic.lean`; full reads of `BranchLogRoot.lean`,
  key sections of `Homotopy/Lifting.lean`, `Harmonic/Analytic.lean`,
  `CurveIntegral/Poincare.lean` (header + decl list),
  `HasPrimitives.lean` (decl list), `RiemannMapping.lean` (statements).
- Negative searches re-confirmed from `perron-engine-phase1.md`:
  `Subharmonic`, Perron, Koebe, Caratheodory.
