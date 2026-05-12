# Formalization Plan: simplex_affine_map_continuous (ID 1466)

## Overview
This task involves formalizing the continuity of the affine characteristic map for a simplex in a simplicial complex. This is a foundational step in the cellular-to-singular homology comparison.

## Target
- **Symbol:** `simplex_affine_map_continuous`
- **File:** `Jacobian/StageA/CellularSingular.lean`

## Mathematical Context (TeX Blueprint)
For a finite abstract simplicial complex $K$ with realization $V$, we define a chain map $\Phi_n: C^{\mathrm{cell}}_n(K) \to C^{\mathrm{sing}}_n(V)$. This map sends an $n$-simplex $\sigma$ to its characteristic map $\sigma: \Delta^n \to V$.
The characteristic map is an affine interpolation between the vertices of the simplex in the geometric realization.

## Instructions
1.  **Correct the Scaffolding (CRITICAL):** The current `relativeSkeletalH` and `Geometric K` types are placeholders (aliases for `V`). You must ensure `simplex_affine_map` is defined on a type that actually carries an affine structure (e.g., `BarycentricRealisation K` or similar).
2.  **Define the Map:** Implement `simplex_affine_map` as the affine map from the standard $n$-simplex $\Delta^n$ to the image of the $n$-simplex in the realization.
3.  **Prove Continuity:** Use Mathlib's topology and linear algebra tools to prove the map is continuous. This typically involves showing it's a restriction of a linear map or using barycentric coordinate properties.
4.  **Standard Mathlib:** Use `Mathlib.Analysis.Convex.Simplex` and `Mathlib.Geometry.Manifold.ChartedSpace` if applicable.

## ANTI-CHEAT CLAUSE
- You must **NOT** change the definitions of the mathematical objects provided in the scaffolding to make the proof trivial (e.g., do not make the map constant).
- You must **NOT** rely on placeholder type aliases (like `PUnit`) to discharge the goal.
- If you find a definition is mathematically insufficient for a real proof, fix the definition substantively or report the issue.
