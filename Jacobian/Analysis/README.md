# `Jacobian/Analysis/` — the major classical-analysis gaps

This directory packages the red-border umbrellas in the project's
blueprint dep graph.  Each sub-directory is an **independent build
target** with its own headline statement and named sub-leaves
(real-typed `sorry` propositions, not `True := trivial` placeholders),
plus a classical-proof + Lean-plan + plain-English description in
`tex/sections/12-classical-analysis-gaps.tex`.

| Node | Headline | Build target | LOC est. (incl. shared) |
|---|---|---|---|
| R1 | Radó's triangulation | `Jacobian.Analysis.Rado` | 2000–2700 |
| R2 | Tietze normal form | `Jacobian.Analysis.Tietze` | 900–1100 |
| R3 | Polygonal-model theorem | `Jacobian.Analysis.PolygonalModel` | 1500–2000 |
| R4 | De Rham theorem | `Jacobian.Analysis.DeRham` | 1500–2000 (modulo R9) |
| R5 | Hodge decomposition | `Jacobian.Analysis.HodgeDecomposition` | 1700–2500 (modulo R9, R10) |
| R6 | Hodge / de Rham rank | `Jacobian.Analysis.HodgeDeRham` | 1100–1400 |
| R7 | Dolbeault isomorphism | `Jacobian.Analysis.Dolbeault` | 1300–1700 (modulo R9, R10) |
| R8 | Serre duality on a Riemann surface | `Jacobian.Analysis.SerreDuality` | 3300–4300 |
| R9 | Bundled differential forms `Ω^k(M)` | `Jacobian.Analysis.BundledForms` | 800–1200 |
| R10 | Sobolev / elliptic regularity | `Jacobian.Analysis.SobolevElliptic` | 4500–6500 |

**Total** (with shared sub-gap deduplication): **18000–25000 LOC**.

R9 and R10 are *recursive sub-gaps* surfaced inside R4/R5/R7 that have
been promoted to top-level dep-graph nodes:

* **R9** (bundled `Ω^k(M)`) is the foundational sub-gap shared by R4,
  R5, and R7.  Promoted from "R4-sub-A".
* **R10** (Sobolev / elliptic regularity) is the single largest
  sub-gap in the entire tree.  On the critical path for R5 and
  (transitively) R7 + R8.  Promoted from "R5-sub-B".

## Layout

```
Jacobian/Analysis.lean                    -- umbrella, imports all ten
Jacobian/Analysis/<Node>.lean             -- per-node umbrella
Jacobian/Analysis/<Node>/Overview.lean    -- headline + sub-leaf real-typed sorry theorems
Jacobian/Analysis/<Node>/README.md        -- per-node master plan
```

## Independent builds

```bash
lake build Jacobian.Analysis.Rado
lake build Jacobian.Analysis.Tietze
lake build Jacobian.Analysis.PolygonalModel
lake build Jacobian.Analysis.DeRham
lake build Jacobian.Analysis.HodgeDecomposition
lake build Jacobian.Analysis.HodgeDeRham
lake build Jacobian.Analysis.Dolbeault
lake build Jacobian.Analysis.SerreDuality
lake build Jacobian.Analysis.BundledForms
lake build Jacobian.Analysis.SobolevElliptic
```

## Relationship to existing scaffolds

This directory does **not** replace existing project-side
scaffolding.  Each Overview.lean **imports** the relevant scaffolds
and forwards / re-states the headline + sub-leaves on top of them.
Bottom-up sketches live at:

* R1, R2: `Jacobian/StageA/{SimplicialComplex, RadoTheorem,
  SpanningTree, PrismOperator, Hurewicz, EdgeWordTietze,
  CellularSingular}.lean`
* R3: `Jacobian/Periods/{Polygon4g*, EdgeWord, SurfaceClassification,
  TietzeReduction, Polygon4gCellular,
  H1EvenBasisViaSurfaceClassification}.lean`
* R4: `Jacobian/StageB/{DifferentialForms, DeRhamComplex,
  DeRhamComparison}.lean`
* R5: `Jacobian/StageB/{LaplaceBeltrami, HarmonicForms,
  KahlerStructure}.lean`
* R6: `Jacobian/Periods/{HodgeDeRham,
  AnalyticGenusEqTopologicalGenus, IntegralOneCycle}.lean`
* R7: `Jacobian/HolomorphicForms/Serre/Dolbeault.lean`,
  `Jacobian/StageB/{KahlerStructure, CoherentSheaves}.lean`
* R8: `Jacobian/HolomorphicForms/Serre/*.lean` (32 files),
  `Jacobian/StageB/SerreDuality.lean`,
  `Jacobian/HolomorphicForms/SerreDualityRS.lean`,
  `Jacobian/HolomorphicForms/SheafCohomologyRS.lean`
* R9: `Jacobian/StageB/DifferentialForms.lean` (the project-side
  stub `Omega`, `exteriorDerivative`, `wedge`, `pullback`,
  `integrate`, `stokes_closed_manifold`)
* R10: `Jacobian/StageB/{LaplaceBeltrami, HarmonicForms}.lean`
  (the project-side stubs for `RiemannianMetric`, `hodgeStar`,
  `codifferential`, `laplaceBeltrami`, `Harmonic`, `greenOperator`)

The role of `Jacobian/Analysis/<Node>/Overview.lean` is to give each
gap a stable umbrella in a single named place, where every sub-leaf
is stated as a real-typed proposition with `sorry` for the proof.
This way, future Aristotle / cloud-worker tasks can target named
obligations and downstream code can `import Jacobian.Analysis.<Node>`
and depend on these declarations as if they were Mathlib lemmas
(modulo the `sorry`).

## Recursive sub-gaps

Each node lists 3–5 recursive sub-gaps surfaced when its proof is
expanded.  See the per-node `Overview.lean` for the named list, and
`tex/sections/12-classical-analysis-gaps.tex` Section
`gap-summary` for the consolidated estimate.
