# Worker jc5 — Plan: Chapter 06 (Issue #240)

## Objective
Discharge or narrowly split `h1_basis_of_compact_riemann_surfaceU` against the current upstream `H1BasisU.lean` shape.

## Strategy
1. **stageB_analytic_eq_topologicalGenusU**: Provide the proof for this sorry using `compactRiemannSurface_homeomorph_ulift_polygon4g X`, `polygon4g_singularH1U_iso_freeZ`, and `IntegralOneCycleULinearEquivOfHomeo`. Use `finrank_eq_card_basis` to show that the analytical and topological genus match.
2. **stageA_surface_CW_basisU**: Keep this sorry as the topological target frontier to be resolved via the `jc4` cellular substrate.
3. Refresh the `sorries.jsonl` graph to track the newly surfaced providers.
