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

## Live Status (2026-05-07, /loop tick — backend live, queue light)

Aristotle backend is live again (5 IN_PROGRESS jobs on first page,
none in `aristotle_jobs.jsonl` — all FourColor or other-project work
that we ignore per `ref/PROMPT.md` step 2). Cellular-Hurewicz bridge
made big strides on origin/main between the previous tick and this
one — `singularChainElement_boundary_decomposition`,
`PrismChainCombinatorialIdentity`, `cellularBoundarySigned_sq_zero`,
and the `edgeHomologyClass` upgrade all landed sorry-free.

**Submitted this tick (2 live + 1 cancel-and-re-aim):**

| ID | File | Target |
|---|---|---|
| ~~`2ff4fff7`~~ | `Jacobian/Periods/SingularChainElement.lean` | ~~`singularChainElement_boundary_decomposition`~~ — **cancelled**: target already discharged on origin/main (commit `7d141b7`) before this tick's push; cancelled within the same tick per ref/PROMPT.md cancel rule (target sorry no longer exists locally). |
| `2c73f336` | `Jacobian/Periods/Polygon4gEdgeBasisMap.lean` | `edgeBasisMap_injective` — Phase 6.a leaf of the cellular-Hurewicz bridge. The file's docstring explicitly notes this becomes provable once `edgeHomologyClass` is the real homology projection — that upgrade landed in commit `2fc4812`, so the proof is now unblocked. Strategy: `edgeChainCoeff` (dual of `Sigma.ι` at `edgeSimplex g i`) descending to homology via the just-landed `singularChainElement_boundary_decomposition`. |
| `b9fcfdb4` | `Jacobian/Periods/PathIntegralViaCoverWithRefinementInvariant.lean` | `pathIntegralViaCoverWith_refinement_invariant'` — only sorry in file; the in-source strategy comment (lines 319-336) lays out a 4-step refine-to-LCM + chart-change-per-summand proof. All helpers (`pathIntegralViaCoverWith_refine_to_multiple`, `pathIntegralViaChartCorrect_chart_change`, `divFinIcc`) already exist and are sorry-free. |

**Tick C (third /loop check, ~+40 min):** Both packets still
IN_PROGRESS (13% / 5%); no completions to integrate, no upstream
advances. Surveyed remaining production sorries (~80 across 27
files); the bulk are gated on Mathlib gaps (line-bundle / divisor
API, sheaf-cohomology comparison, Stokes on manifolds, partition-of-
unity Poincaré, cellular-vs-singular comparison, branched-cover
local mapping theorem) or on Round-1 `True := by trivial`
placeholder upstream leaves. Submitting BLOCKER-class targets
contradicts the "Aristotle: substantive only" rule; left the queue
at 2 live packets pending real result returns.

**Tick D (fourth /loop check, ~+60 min):** Packet `2c73f336`
(`edgeBasisMap_injective`) returned COMPLETE_WITH_ERRORS but with
a clean 9-line proof and a green local build — **integrated**. The
proof routes via Orzech's property (`OrzechProperty.bijective_of_surjective_endomorphism`)
rather than the suggested chain-level `edgeChainCoeff` extraction,
relying on `edgeBasisMap_surjective` (still sorry, out of scope)
plus the Hurewicz iso (still sorry, planned in C1c). It introduces
no new sorries and shifts dependency cleanly to a sibling leaf.
`b9fcfdb4` (path-integral refinement invariance) still IN_PROGRESS
at 13%.

**Ticks E/F/G (~+80–+120 min):** `b9fcfdb4` stuck at 15% across
three checks; per cancel rule (target sorry still exists locally,
no user instruction) it keeps running. Tick G dispatched a third
packet `cdd76e1a` against `polygon4g_succ_singularH1_finrank_eq`
(rank-computation leaf in `Polygon4gCellular.lean`); enumerated
four strategy hints and flagged the circular dependencies for the
non-direct routes. Likely BLOCKER given Mathlib gaps, but the
previous Orzech result earned the benefit of the doubt — worth one
shot for both a real attempt and useful triage info either way.

**Tick I (~+150 min):** `cdd76e1a` returned with a partial discharge
— **integrated**. The original `_finrank_eq` sorry is gone; in its
place a new sorry'd helper `polygon4g_succ_singularH1_linearEquiv_abelianization`
asserts the Hurewicz iso directly, bypassing the circular
`polygon4g_succ_hurewicz_iso_explicit` ↔ `_freeAb_data` ↔
`_finrank_eq` chain. Net sorry count unchanged but the architectural
obstruction is now expressed as one clean iso-existence statement
instead of a tangle of three. Same shifting-the-sorry pattern as the
2c73f336 Orzech integration. Build green on Polygon4gCellular and
downstream Polygon4gEdgeBasisMap. `b9fcfdb4` still IN_PROGRESS at
16%.

**Tick J (~+170 min):** Dispatched `9bf8be37` exploiting the new
`_linearEquiv_abelianization` helper to discharge the **other two**
sorries in `Polygon4gCellular.lean` (`_isFinite` + `_isTorsionFree`).
This is a genuinely net-2 sorry reduction: both follow trivially
from the iso (`Module.Finite` transports along `LinearEquiv`;
`IsTorsionFree` follows from `Module.Free` of the codomain
`Polygon4gAbelianization g = Fin (2(g+1)) → ℤ`). If it lands, the
file goes from 3 sorries to 1, consolidating the entire
cellular-Hurewicz architectural obstruction onto one named gap.

**Tick K (~+190 min):** `9bf8be37` returned and **integrated** —
first packet this session producing an actual net sorry-count
decrease. Aristotle's discharge used `Module.Finite.equiv` and
`Function.Injective.moduleIsTorsionFree` correctly, but worked
around declaration ordering by introducing a forward-declared
`_aux` sorry (since the iso lemma sat at line ~306 after the
targets at ~260, ~276). On integration this was rewritten to
**reorder the file**: `_linearEquiv_abelianization` moved upward to
precede `_isFinite`, the aux deleted, the targets referencing the
real iso directly. Final state of `Polygon4gCellular.lean`: 1 sorry
on the iso (line 279), `_isFinite` / `_isTorsionFree` / `_finrank_eq`
all sorry-free. Build verified on the file + downstream
`Polygon4gEdgeBasisMap`. The cellular-Hurewicz obstruction is now
consolidated onto exactly one named gap.

**Ticks L-O (~+210–+290 min):** `b9fcfdb4` finally finished after
~5 hours grinding. **Rejected** on integration. The patch builds
and contains a useful sorry-free `hcov_refined` helper for the
Nat-arithmetic of refined covers, BUT it also introduces a new
sorry'd helper `chartPullback_intervalIntegrable_segment` whose
unconditional statement is FALSE in general (Aristotle's own
summary acknowledges: "for general continuous paths, this
derivative may not be integrable"). Sorry-ing a known-false
statement is worse than no progress. Reverted. The genuine fix is
a STATEMENT change — add a `CurveIntegrable` / C¹ hypothesis to
`pathIntegralViaCoverWith_refinement_invariant'` itself — which
Claude does not make autonomously. Routed to brainstorm.

The companion `edgeBasisMap_surjective` (line 114) requires barycentric
subdivision and is explicitly *out of scope* for `2c73f336`.

**Next-tick candidates** (still queued from the 2026-05-05 frontier
list; not submitted this tick to keep write scopes disjoint):

* C4a — `Jacobian/Periods/ChartedFormPullbackNaturality.lean`
  (chart-level chain-rule for path integrals, no Stokes).
* C8a — `Jacobian/HolomorphicForms/Serre/ResidueMap.lean` —
  needs concretisation of `residueMap` first (currently both round-trip
  endpoints are `opaque`, so as-is would BLOCKER).
* C7c — `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` line-264
  sorry-free assembly (gated on the C7a/b helper files existing).

---

## Live Status (2026-05-04, R10 dispatch end-to-end on
`claude/refine-14-r10-proof-GuSaj`)

R10 (Sobolev / elliptic regularity) — the largest classical-analysis
sub-gap (blueprint estimate 4500–6500 LOC) — is dispatched
end-to-end on the spectral-shortcut route, against unmodified
Mathlib v4.28.0.  No Aristotle packets were used for this work; all
edits are local Claude commits.

**Files added (no `sorry`, no `True`-valued bodies):**

| Milestone | File | LOC | Content |
|---|---|---|---|
| M0 (chain K2) | `Jacobian/Analysis/SobolevElliptic/ModelSymbol.lean` | ~180 | Principal symbol of model Laplacian invertible at nonzero ξ |
| M1 substrate | `Jacobian/Analysis/BundledForms/{SmoothFun,Omega0,L2Norm,L2Completion}.lean` | ~600 | Real `L²(M, μ)` Hilbert space with `IsManifoldMeasure μ` typeclass |
| M2 metric | `Jacobian/StageB/RiemannianMetricBundled.lean` | ~120 | Real Riemannian metric class wrapping Mathlib `RiemannianBundle` |
| M2 spectral | `Jacobian/Analysis/SobolevElliptic/AbstractFredholmResolvent.lean` | ~170 | Compact `T` + λ≠0 ⇒ `Eigenspace T λ` finite-dim |
| M3 resolvent | `Jacobian/Analysis/SobolevElliptic/AbstractResolvent.lean` | ~150 | `T := i ∘ i*` self-adjoint, non-neg, compactness preservation |
| M4 plug-in | `Jacobian/Analysis/SobolevElliptic/HeadlinePlugIn.lean` | ~150 | `class HasLaplaceResolvent M μ` → `Module.Finite (RealHarmonic M μ)` |
| M4 witness | `Jacobian/Analysis/SobolevElliptic/RealizabilityWitness.lean` | ~95 | Trivial witness for finite-dim L² (proves realizability) |

**Downstream wiring:** R5/R7/R8 each have a substantive companion
theorem that takes `[HasLaplaceResolvent M μ]` and produces
`Module.Finite ℝ (RealHarmonic M μ)`:
- `Jacobian/Analysis/HodgeDecomposition/Overview.lean` →
  `hodge_harmonic_forms_finite_dim_substantive`
- `Jacobian/Analysis/Dolbeault/Overview.lean` →
  `dolbeault_harmonic_forms_finite_dim_substantive`
- `Jacobian/Analysis/SerreDuality/Overview.lean` →
  `serre_duality_harmonic_finite_dim_substantive`

**Blueprint:** new subsection `subsec:r10-phase-dispatch` in
`tex/sections/12-classical-analysis-gaps.tex` documents the
M0–M4 milestones; chain K2 has Round 3
(`subsubsec:sle-round-3`) of stepwise refinement reaching
`Matrix.PosDef.invertible` and `real_inner_self_pos`.

**Residual analytic gap (single typeclass instance):** non-trivial
`HasLaplaceResolvent` for an infinite-dim L² requires (a) construct
`H¹(M)` (manifold Sobolev, R10-sub-A,B), (b) prove Rellich on a
compact manifold, (c) link the resolvent eigenspace to a classical
ker Δ.  All three are flagged ABSENT in Mathlib v4.28.0; future
work plugs into the framework with no further changes to the
spectral-output side.

**No Aristotle queue conflict:** all R10 work is in the
`Jacobian/Analysis/{SobolevElliptic, BundledForms,
HodgeDecomposition, Dolbeault, SerreDuality}/` and `Jacobian/StageB/`
trees; current Aristotle saturation (Stage A: HolomorphicForms,
Periods, AbelJacobi) writes elsewhere.

---

## Curve-analysis frontier delegation packets (2026-05-05, queued; Aristotle blocked)

Stepwise refinement (per `ref/TOPDOWN.md`) is being driven locally
while the Aristotle queue is unavailable. The packets below are the
*Aristotle-shaped split* of each frontier sorry in the curve-analysis
pass — each packet targets one new helper file with a tightly scoped
named obligation, prefers direct tactics, and includes the Mathlib
gap that blocks final discharge.

When Aristotle is back, dispatch in the order given (lower numbers
first; sibling jobs can go in parallel because their write scopes are
disjoint).

### Packet C1 — `polygon4g_singularH1_basis` (Polygon4gCellular)

**Source sorry:** `hurewicz_singularH1_iso_polygon4g`
(`Jacobian/Periods/Polygon4gCellular.lean:135`).

Top-down split into three named obligations (each in its own file):

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C1a | `Jacobian/Periods/Polygon4gFundamentalGroupAb.lean` | `polygon4g_succ_fundamentalGroup_abelianization_freeZ` — `π₁(Σ_g)^{ab} ≃ ℤ^{2(g+1)}` | Surface group presentation absent |
| C1b | `Jacobian/Periods/HurewiczNatTrans.lean` | `hurewicz_iso_natural` — `H₁(X,ℤ) ≃ π₁(X)^{ab}` for path-connected `X` | Hurewicz natural transformation absent |
| C1c | `Jacobian/Periods/Polygon4gCellular.lean` | `hurewicz_singularH1_iso_polygon4g` — sorry-free assembly composing C1a∘C1b⁻¹ | — |

Each sub-job's allowed write scope is exactly the named file; forbidden
files always include `Jacobian/Challenge.lean`.

### Packet C2 — `singularH1_iso_of_homotopyEquiv_via_prism` (SingularH1Homotopy)

**Source sorry:** `singularH1_iso_of_homotopyEquiv_via_prism`
(`Jacobian/Periods/SingularH1Homotopy.lean:208`).

Already split top-down into named leaves (`SingularChainPrism`,
`singularChain_homotopy_chainHomotopy`, etc.); the residual sorry is the
*assembly through Mathlib's homology functor*. Sub-split:

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C2a | `Jacobian/Periods/SingularH1FunctorMap.lean` | `singularH1Functor_map` — `C(X,Y) → singularH1 X →ₗ[ℤ] singularH1 Y` honestly via the singular-chain functor | Need to compose `singularChainComplexFunctor` with `Hₙ` extraction |
| C2b | `Jacobian/Periods/SingularH1FunctorMapId.lean` | `singularH1Functor_map_id` — identity functoriality | — (follows from C2a) |
| C2c | `Jacobian/Periods/SingularH1FunctorMapComp.lean` | `singularH1Functor_map_comp` — composition functoriality | — |
| C2d | `Jacobian/Periods/SingularH1FunctorMapHomotopy.lean` | homotopic maps induce equal `H₁` (via prism leaves already in `SingularH1Homotopy.lean`) | descent of chain-homotopy to homology |
| C2e | `Jacobian/Periods/SingularH1Homotopy.lean` | `singularH1_iso_of_homotopyEquiv_via_prism` — sorry-free `LinearEquiv` from C2a/b/c/d | — |

### Packet C3 — `IntegralOneCycle_finite_of_cellular`, `_free_of_cellular` (CellularHomologyRS)

**Source sorries:** `Jacobian/Periods/CellularHomologyRS.lean:114, 136`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C3a | `Jacobian/Periods/CellularChainComplex.lean` | `cellularChainComplex` — finite ℤ-chain complex from `FiniteCWStructure` | cellular chain complex on a topological space |
| C3b | `Jacobian/Periods/CellularSingularComparison.lean` | `cellular_eq_singular_homology` — Hatcher Theorem 2.35 | comparison theorem |
| C3c | `Jacobian/Periods/IntegralOneCycleFreeFromPolygon.lean` | `IntegralOneCycle_free_of_cellular` via the polygonal model (route 1) — uses C1c | needs Packet C1 first |
| C3d | `Jacobian/Periods/IntegralOneCycleFinite.lean` | `IntegralOneCycle_finite_of_cellular` via C3b | — |

C3c blocks on C1; C3a/b are independent.

### Packet C4 — `pathIntegralViaCover_pullbackFormsBundledLM` (PullbackNaturality, path level)

**Source sorry:** `Jacobian/Periods/PullbackNaturality.lean:239`.

This is a chain-rule calculation for path integrals, no Stokes. The
existing file already discharges the Path-API special cases
(refl/trans/symm/zero/add/smul/neg/comp). The remaining base case is
chart-level naturality.

| Sub-job | Target file | Statement |
|---|---|---|
| C4a | `Jacobian/Periods/ChartedFormPullbackNaturality.lean` | `chartedFormPullback_pullback_naturality` — at chart level, `pathIntegralInChart c (f^*η) γᵢ = pathIntegralInChart (c ∘ f, ⟨…⟩) η (γᵢ.map hf.continuous)` |
| C4b | `Jacobian/Periods/PathIntegralViaCoverWithPullbackNaturality.lean` | the `_With` variant on a fixed cover-and-partition |
| C4c | `Jacobian/Periods/PullbackNaturality.lean` | un-`With` lift: discharges line 239 from C4b via the existing Classical.choose wrapper |

### Packet C5 — `periodPairing_pullbackFormsBundledLM` (PullbackNaturality, cycle level)

**Source sorry:** `Jacobian/Periods/PullbackNaturality.lean:139`.

Cycle-level Stokes / descent. Blocks on C4 + concretisation of
`opaque periodPairing`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C5a | `Jacobian/Periods/PeriodPairingChainLevel.lean` | `chainFormPairing` and `periodPairing_eq_chainFormPairing_descent` | concretise `periodPairing` |
| C5b | `Jacobian/Periods/CyclePushforwardChainCompat.lean` | `cyclePushforward` agrees with chain-level pushforward | — (functoriality bookkeeping) |
| C5c | `Jacobian/Periods/PullbackNaturality.lean` | line-139 sorry-free assembly from C4c + C5a + C5b | — |

### Packet C6 — `basisAnalyticPullbackBundle_*_dualPullback` (PullbackBasis HEq diamond)

**Source sorries:** `Jacobian/TraceDegree/PullbackBasis.lean:180, 269`.

Structural fix only. The opaque `basisAnalyticPullbackBundle` is
realised by `Classical.choice` from the zero-valued `Inhabited`
witness, so cross-instance identities cannot be proved without a
concrete construction. The fix is to replace the opaque bundle with
a definition built from a concrete `pullbackFormsMap`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C6a | `Jacobian/HolomorphicForms/PullbackFormsMapConcrete.lean` | `pullbackFormsMap` — concrete `H⁰(Y, Ω¹) →ₗ[ℂ] H⁰(X, Ω¹)` | concrete pullback of holomorphic 1-forms |
| C6b | `Jacobian/TraceDegree/BasisAnalyticPullbackConcrete.lean` | replacement for `opaque basisAnalyticPullbackBundle` built from C6a | — |
| C6c | `Jacobian/TraceDegree/PullbackBasis.lean` | discharge lines 180 and 269 via C6b's defining equations | — |

C6 is sibling to the analogous `PushforwardBasis` blocker
(`pushforwardTraceLift_comp_spec_apply_at`); a real Mathlib
`pullbackFormsMap` would unblock both.

### Packet C7 — `period_congruence_distinct_implies_genus_zero` (AnalyticOfCurveBasis)

**Source sorry:** `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean:264`.

The file's docstring (lines 187–232) already proposes a 3-way split:

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C7a | `Jacobian/AbelJacobi/AbelTheoremExistence.lean` | `abelJacobi_image_zero_implies_principal` — Abel's theorem (existence) | divisor theory + Pic⁰ |
| C7b | `Jacobian/AbelJacobi/RiemannHurwitzDegOne.lean` | `degree_one_meromorphic_implies_genus_zero` — Riemann-Hurwitz at degree 1 | degree of holomorphic maps + genus-0 classification |
| C7c | `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` | line-264 sorry-free assembly from C7a + C7b + `analyticGenus_eq_topologicalGenus` | — |

Per the file's note this split is "worth executing once the divisor
theory layer or even a placeholder `Divisor X` / `IsPrincipal d` API
exists in the project." Until then, either keep the consolidated form
or commit to introducing the placeholder API in C7a's file.

### Packet C8 — RR/Serre cluster (24 sorries / 11 files)

These are all pieces of classical Riemann-Roch / residue / Serre
duality. The cluster sorries break down as follows; each is its own
Aristotle packet (one file → one or two declarations) and each is
blocked on the same upstream Mathlib gap (divisor / line-bundle /
Čech cohomology / residue machinery).

| Sub-job | File | Decls | Bottom-up content |
|---|---|---|---|
| C8a | `Jacobian/HolomorphicForms/Serre/ResidueMap.lean` | `residueMap_left_inv`, `residueMap_right_inv` | residue ↔ integration map iso |
| C8b | `Jacobian/HolomorphicForms/Serre/RiemannRochHighFromSerre.lean` | (2 decls) | Serre-duality → RR high-degree |
| C8c | `Jacobian/HolomorphicForms/Serre/RiemannRochUmbrellaPieces.lean` | (1 decl) | RR umbrella |
| C8d | `Jacobian/HolomorphicForms/RiemannRoch.lean` | `genusZero_exists_nonconstant_mem_L_point`, `_poleDivisor_eq_point_…` | RR `ℓ(P)=2` for genus 0 |
| C8e | `Jacobian/HolomorphicForms/RiemannRochLowDegree.lean` | (1 decl) | RR low-degree case |
| C8f | `Jacobian/HolomorphicForms/EulerCharLineBundle.lean` | (2 decls) | Euler char of a line bundle |
| C8g | `Jacobian/HolomorphicForms/MeromorphicDegree.lean` | (2 decls) | degree of a meromorphic function |
| C8h | `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` | (2 decls) | de Rham → Dolbeault comparison |
| C8i | `Jacobian/HolomorphicForms/ChartCoeffExtractionRecon.lean` | (1 decl) | smoothness of chart coefficient extraction |
| C8j | `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` | (3 decls) | RS-level glue |
| C8k | `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | (6 decls) | genus-0 ⇒ `≅ ℂℙ¹` |

Total surface area: 24 sorries / 11 files. Most files are 1–2
sorries each (only `GenusZeroClassification` exceeds with 6).

Each C8x packet's split-into-helpers will be filled in as the cluster
is iterated; the splits live in the target file's docstring rather
than this index.

### Iteration cadence (while Aristotle is blocked)

`ref/TOPDOWN.md` defines a "round" as one stepwise refinement that
either reduces the sorry count *or* keeps it constant while replacing
one big sorry by smaller, better-named children. The local schedule
is:

* **C1** — 10 rounds of refinement on Polygon4gCellular before moving on.
* **C2** — 10 rounds on SingularH1Homotopy.
* **C3** — 10 rounds on CellularHomologyRS (both leaves).
* **C4 / C5** — 10 rounds each on PullbackNaturality (path / cycle).
* **C6** — 10 rounds on PullbackBasis (HEq diamond).
* **C7** — 10 rounds on AnalyticOfCurveBasis.
* **C8** — 10 rounds on the RR/Serre cluster (rotating across files).

Each round must end with a passing narrow `lake build` of the touched
module(s).

---

## Live Status (2026-05-02, roadmap-driven saturation tick)

Roadmap-driven saturation wave per `ref/plans/roadmap.org`. 14 packets
submitted across W1 P1/P2/P3; 15th rejected with "too many requests"
(cap hit). 1 pre-existing packet (`f74d0ed8`) carries over.

**Submitted this tick (14):**

| ID | File | Target |
|---|---|---|
| `2799e6e5` | HolomorphicForms/GenusZeroClassification.lean | line 442 (sub-obligation 1) |
| `0366d364` | HolomorphicForms/GenusZeroClassification.lean | line 494 (sub-obligation 2) |
| `ce81878d` | HolomorphicForms/GenusZeroClassification.lean | line 886 (subsingleton) |
| `1c513243` | Periods/PullbackNaturality.lean | line 139 `periodPairing_pullbackFormsBundledLM` |
| `c42f5c52` | Periods/PullbackNaturality.lean | line 239 `pathIntegralViaCover_pullbackFormsBundledLM` |
| `78190419` | HolomorphicForms/CompactRiemannSurface.lean | line 161 (fiberNorm continuity) |
| `f98d8709` | HolomorphicForms/CompactRiemannSurface.lean | line 229 (Cauchy completeness) |
| `ea5f8d3c` | HolomorphicForms/CompactRiemannSurface.lean | line 656 (Montel closed-ball totally bounded) |
| `bdaae2fc` | Periods/PeriodFunctional.lean | line 260 `hodge_form_riemannBilinear` |
| `574477c0` | Periods/PeriodFunctional.lean | line 275 `hodge_form_posDef` |
| `fff296dc` | Periods/PeriodFunctional.lean | line 306 `period_functionals_via_hodge` |
| `9d200ee7` | HolomorphicForms/CanonicalDivisor.lean | line 101 (canonical degree = 2g - 2) |
| `6519d1a1` | HolomorphicForms/EulerCharLineBundle.lean | line 123 (RR / Euler char) |
| `3f20f469` | HolomorphicForms/RiemannRochHighDegree.lean | line 83 (high-degree RR) |

**Skipped from this wave (gated):** `analyticOfCurve_injective`
(AbelJacobi line 280 — needs cloud-Claude scoping pass per
`ref/plans/roadmap.org`); the Stage-A-blocked sorries in PeriodFunctional
(`h1_has_even_basis`, `h1_free`, `analyticGenus_eq_topologicalGenus`,
`periodSubgroup_eq_zspan_of_basis`); SerreDualityRS line 139 (rejected at
the cap — retry next tick).

Many of the deeper frontier-sorries (Hodge bilinear/positivity, Serre
duality, RR, Euler char) are likely BLOCKER returns; per memory the
BLOCKER-only diffs route to brainstorm rather than integrate. The
attackable subset is GenusZeroClassification 442/494/886, the two
PullbackNaturality cycle/path naturality lemmas, and the three
CompactRiemannSurface fiberNorm/completeness/Montel sub-steps.

## Live Status (2026-04-29 17:01 EDT, prior tick — kept for context)

- **ref/PROMPT.md §3 rule: every production sorry has a 1:1 Aristotle job.**
- **Open production sorries:** 17 (unchanged).
- **Aristotle integrations to date: 129**.
- **Backend state (first page of `aristotle list`):** 6 QUEUED
  (f3a8e713, 6f6f015d, 9c222f2d, 3683ef39, 6547fde4, 86bef3e0),
  3 COMPLETE on first page (921772f5 integrated, a0bddfd5 no-op,
  4d0d28d6 rejected this tick — stale baseline). 1 CANCELED
  (362e259f).
- **Sub-agents:** local HEq-field fix attempt on PullbackBasis
  reverted this tick — triggered the instance diamond per
  `diamond-problem.txt` analysis. Working tree clean. `sorry-prompt.md`
  rewritten with the diamond-aware approach (`noncomputable def`
  + `Eq.mpr`/`▸` instead of `subst`) for off-host dispatch on
  `basisAnalyticPushforwardBundle_id_traceLift`. Codex still racing
  `genus_zero_homeomorph_onePointCx` in its own worktree.

### This tick

Local-only work (Aristotle backend frozen — no IN_PROGRESS jobs on
first page, no new completions to integrate):

- **Committed prior-tick docstring** on
  `basisAnalyticPushforwardBundle_comp_traceLift` (8fc61ab):
  ~50-line blocker analysis mirroring `_id_traceLift`'s docstring.
  No code change; verified by `lake build` (83s).
- **TOPDOWN bundle-primitive refactor on PullbackBasis** (71a5eaf):
  - Lifted `basisDualPullback_id_apply` (per-vector sorry) into
    `basisAnalyticPullbackBundle_id_dualPullback` (bundle field
    AddMonoidHom-equality, NEW sorry).
  - Lifted `basisDualPullback_comp` (per-vector sorry) into
    `basisAnalyticPullbackBundle_comp_dualPullback` (bundle field
    AddMonoidHom-equality, NEW sorry).
  - Per-vector / per-coord forms (`basisDualPullback_id`,
    `basisDualPullback_id_apply`, `basisDualPullback_comp_top`,
    `basisDualPullback_comp`) are now sorry-free assemblies via
    `unfold + rw + rfl` and `AddMonoidHom.comp_apply`.
  - Net 0 sorries; mirrors PushforwardBasis pattern
    (af653549 + a8778c20 + a1ce4200).
  - Verified: `lake build Jacobian.TraceDegree.PullbackBasis`
    (176s, exit 0).
- **Submitted 2 new packets** for the new bundle-primitive sorries:
  `6547fde4` (`_id_dualPullback`), `86bef3e0` (`_comp_dualPullback`).

### Active our-packets after this tick

Visible on first page of `aristotle list`:

| ID | File | Target | Status |
|---|---|---|---|
| `f3a8e713` | PushforwardBasis | `_comp_traceLift` (bundle) | QUEUED |
| `6f6f015d` | PushforwardBasis | `_id_traceLift` (bundle) | QUEUED |
| `9c222f2d` | PeriodFunctional | `period_vectors_linearIndependent_of_symplectic` | QUEUED |
| `362e259f` | PushforwardBasis | `pushforwardTraceLift_comp` (stale, target sorry-free) | QUEUED |
| `3683ef39` | PushforwardBasis | `_id_apply_at` (stale, target sorry-free) | QUEUED |
| `4d0d28d6` | PullbackBasis | `basisDualPullback_comp` (stale after 71a5eaf) | QUEUED |
| `6547fde4` | PullbackBasis | `_id_dualPullback` (NEW) | SUBMITTED |
| `86bef3e0` | PullbackBasis | `_comp_dualPullback` (NEW) | SUBMITTED |

Older packets covering CompactRiemannSurface, GenusZeroClassification,
PeriodFunctional `periodSubgroup_isZLattice`, and AnalyticOfCurveBasis
sorries are paginated below the first page. Per `aristotle_jobs.jsonl`,
the open sorries are all covered.

### Stale packets (target sorry sorry-free / renamed; left running)

`362e259f` `3683ef39` `4d0d28d6` (this tick) plus earlier
`bbe527bb` `c7feba63` `b4029f72` `c910ac80` `27c56154` `f280ecc6`
`271cc21e` `6c796045` `3d5f379e` `c6c4c612` `d8fd495f` `2bd5f151`
`b7799fc9` `5f052643` `8585f085` `0a5f74a8` `6b2f47f1` `03715a4d`
`05100f76`.

### Sub-agents launched this tick (background, worktree-isolated)

Per ref/PROMPT.md §3 — racing the two newest-submitted QUEUED Aristotle
packets:

- `ad96003a19385a71c` — racing `6547fde4`
  (`basisAnalyticPullbackBundle_id_dualPullback`)
- `a5ded3e9db49ff1f7` — racing `86bef3e0`
  (`basisAnalyticPullbackBundle_comp_dualPullback`)

Both target the same file but disjoint declarations. Each runs in its
own git worktree; integration is by cherry-pick of the targeted file
edit when (and only when) the agent's local `lake build` passes.

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
