# Blueprint Chain Audit: Jacobian-Only Route

Date: 2026-05-18.

## Scope

This audit inspected `tex/sections/12-classical-analysis-gaps.tex`,
`Jacobian/Blueprint/Generated.lean`, `sorries.jsonl`, and the current
`Jacobian/Solution.lean` route.  The key convention is:

> Generated declarations of the form `def foo : Prop := True` are roadmap
> nodes only. They are not proof reductions and should not be treated as
> evidence that the corresponding mathematics has been formalized.

The production route does not import `Jacobian.Blueprint.Generated` except
through the blueprint umbrella.  `Jacobian/Solution.lean` uses named project
declarations in `HolomorphicForms`, `Periods`, `AbelJacobi`, and
`TraceDegree`.

## Chain Counts

Inspected chain prefixes: 13.  Inspected numbered TeX lemma blocks: 249.
Generated `Prop := True` hooks with these prefixes: 125 total, or 117 if
counting only the strict requested regex `prefix_r[0-9]+`.

| Prefix | TeX steps | Generated hooks | Endpoint kind | Classification |
|---|---:|---:|---|---|
| `rvl` | 15 | 11 | broad PL vertex-link roadmap | roadmap-only |
| `pgm` | 15 | 14 | broad polygonal model / Euler topology | roadmap-only |
| `tbh` | 15 | 13 | broad Tietze-Brahana topology | roadmap-only |
| `trf` | 15 | 10 | trace of holomorphic forms | frontier-assumption-ok |
| `pdp` | 18 | 12 | real basis-pullback bridge plus generated subnodes | shortcut/rephrase |
| `pn` | 19 | 14 | period-pairing naturality route | shortcut/rephrase |
| `pcr` | 19 | 6 | path-integral chart chain rule route | shortcut/rephrase |
| `hod` | 57 | 19 | broad Hodge decomposition roadmap | roadmap-only, with narrower live frontiers |
| `hdf` | 15 | 11 | broad Hodge/de Rham finite generation | roadmap-only |
| `hdr` | 15 | 0 | broad Hom-rank algebra roadmap | roadmap-only |
| `dis` | 15 | 2 | broad de Rham integration roadmap | roadmap-only, with narrower live frontiers |
| `dpp` | 15 | 8 | broad Dolbeault/Pompeiu roadmap | roadmap-only |
| `srt` | 16 | 5 | broad residue theorem roadmap | roadmap-only |

`trf`, `pn`, `pcr`, and `pdp` are the only inspected chains whose topic is
directly on the current trace/push-pull route.  Even there, the generated
subnodes are not proofs; the live route should be tracked by the named Lean
declarations listed below.

## Live Route Blockers

The highest-priority blockers for `Jacobian/Solution.lean` are named Lean
declarations, not the broad numbered chains.

| Area | Lean declarations | Current status | Treatment |
|---|---|---|---|
| Trace-pullback identity | `basisAnalyticPullbackDegreeSpec_frontier`, `analyticPushforward_analyticPullback_spec`, `traceFormsBundled_apply_fun_regular`, `traceFormsBundled_zero` | frontier/sorries remain | Keep as frontier; prove the form-level trace and trace-pullback identity directly. |
| Period lattice and compact torus | `holomorphicFormBridge`, `riemann_classical_real_LI_input`, `hodge_form_posDef_on_periods_ORIGINAL`, `periodSubgroup_isZLattice`, `exists_compact_periodFundamentalDomain` | mixed opaque/frontier/sorry-free assemblies | Keep narrow frontier statements; do not expand into full `hod`/`hdf`/`hdr`. |
| Period naturality | `periodPairing_pullbackFormsBundledLM`, `periodPairing_pullbackFormsBundledLM_via_pathLevel`, `pathIntegralViaCover_pullbackFormsBundledLM` | live named route; broad subchains include generated hooks | Rephrase around these declarations and their real supporting packets. |
| Pullback descent | `transfer_functional_mem_periodSubgroup`, `pullbackTraceLift_preserves_lattice_raw`, `basisAnalyticPullbackBundle_eq_pullbackFormsMap` | live; one transfer-map frontier remains | Prove transfer/naturality directly; keep `pdp` as a small bridge, not a 17-step proof project. |
| Abel-Jacobi separation | `nonconstant_single_pole_implies_genus_zero`, `degree_one_meromorphicMap_implies_analyticGenus_zero`, `period_congruence_distinct_implies_genus_zero`, `pathIntegralFunctional_separates_points` | public frontier theorems plus route-data versions | Prefer route-data variants or explicit frontier assumptions. |
| Genus-zero classification | `genus_zero_homeomorph_onePointCx`, `exists_contMDiff_homeomorph_to_onePointCx`, harmonic/dipole lemmas | serious PDE/uniformization frontier | Keep as frontier unless the project chooses the PDE route. |
| Montel / finite-dimensional forms | `holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps`, `holomorphicOneForm_arzela_ascoli_refine23`, `compactRiemannSurface_holomorphicOneFormMontelData_frontier` | live analytic input | Prove or keep a named Montel frontier; avoid full unrelated topology chains. |

## Orphaned Chains

The LaTeX file now has `\subsection{Orphans: background roadmap chains not on
the active Jacobian route}`.  The following chains were moved there:

- Broad topology chains: `rvl`, `tbh`, `pgm`.
- Broad de Rham/Hodge/homology chains: `dis`, `hod`, `hdf`, `hdr`.
- Broad Dolbeault/residue-theorem chains: `dpp`, `srt`.

They are retained for label stability and possible future foundational work,
but they should not be assigned as current Jacobian blockers.

The live S21-S23 chains `pn`, `pcr`, and `pdp` remain in the active section
because they describe current period naturality and basis-aligned descent
interfaces.  Their generated subhooks are still roadmap nodes only.

## Jacobian-Only Plan

1. Prove or explicitly preserve the trace-pullback frontier.
   Work at `traceFormsBundled` and `basisAnalyticPullbackDegreeSpec_frontier`;
   downstream `Solution.pushforward_pullback` already has the right shape.

2. Replace broad period-lattice background with narrow frontiers.
   Focus on `periodSubgroup_isZLattice`, `exists_compact_periodFundamentalDomain`,
   and the concrete bilinear/nondegeneracy inputs they actually use.

3. Close period naturality by named declarations.
   Use `periodPairing_pullbackFormsBundledLM` and
   `pathIntegralViaCover_pullbackFormsBundledLM` as the target surface, not the
   full `dis`/`srt`/`dpp` roadmap.

4. Keep Abel-Jacobi separation honest.
   Route-data versions already isolate the meromorphic-map data.  The public
   frontiers `nonconstant_single_pole_implies_genus_zero` and
   `degree_one_meromorphicMap_implies_analyticGenus_zero` should be proved
   directly or retained as named assumptions; do not hide them behind generated
   hooks.

5. Treat genus-zero uniformization and Montel as explicit analytic frontiers.
   They are live only through named declarations in `HolomorphicForms`, not
   through the broad Hodge/Dolbeault topology chains.

## Verification Snapshot

`python3 scripts/list-sorries.py --no-build` reported 72 current sorry
locations.  `python3 scripts/audit-sorries.py sorries.jsonl` reported
1227 nodes, 1415 upstream edges, 1415 downstream edges, no cycles, and
`Audit passed`.

