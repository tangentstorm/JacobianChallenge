# Worker jc5 — Plan: Chapter 06 (Issue #240 Transport Providers)

## Objective
Discharge the transport providers surfaced by `stageB_analytic_eq_topologicalGenusU` to finalize the equivalence machinery for #240.

## Strategy
1. **IntegralOneCycleULinearEquivOfHomeo**: Use the functoriality of `singularHomologyFunctor` and `TopCat.isoOfHomeo` to show that homeomorphic spaces have isomorphic `IntegralOneCycleU` modules.
2. Coordinate with `jc2`/`jc4` regarding `compactRiemannSurface_homeomorph_ulift_polygon4g` and `polygon4g_singularH1U_iso_freeZ` so they are not proved in parallel.
3. Keep `stageA_surface_CW_basisU` as the remaining frontier pending the cellular substrate.
