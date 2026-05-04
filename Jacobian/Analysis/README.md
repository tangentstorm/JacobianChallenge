# `Jacobian/Analysis/` — the eight major classical-analysis gaps

This directory packages the eight red-border umbrellas in the
project's blueprint dep graph.  Each sub-directory is an
**independent build target** with its own headline statement and
named sub-leaves, plus a classical-proof + Lean-plan + plain-English
description in `tex/sections/12-classical-analysis-gaps.tex`.

| Node | Headline | Build target | LOC est. (incl. shared) |
|---|---|---|---|
| R1 | Radó's triangulation | `Jacobian.Analysis.Rado` | 2000–2700 |
| R2 | Tietze normal form | `Jacobian.Analysis.Tietze` | 900–1100 |
| R3 | Polygonal-model theorem | `Jacobian.Analysis.PolygonalModel` | 1500–2000 |
| R4 | De Rham theorem | `Jacobian.Analysis.DeRham` | 2500–3500 |
| R5 | Hodge decomposition | `Jacobian.Analysis.HodgeDecomposition` | 5500–8500 |
| R6 | Hodge / de Rham rank | `Jacobian.Analysis.HodgeDeRham` | 1100–1400 |
| R7 | Dolbeault isomorphism | `Jacobian.Analysis.Dolbeault` | 2200–2900 |
| R8 | Serre duality on a Riemann surface | `Jacobian.Analysis.SerreDuality` | 3300–4300 |

**Total** (with shared sub-gap deduplication): 15000–22000 LOC.

## Layout

```
Jacobian/Analysis.lean                    -- umbrella, imports all eight
Jacobian/Analysis/<Node>.lean             -- per-node umbrella
Jacobian/Analysis/<Node>/Overview.lean    -- headline + sub-leaf placeholders
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
```

Each currently builds in <1s as `True` placeholders.

## Relationship to existing scaffolds

This directory does **not** replace existing project-side
scaffolding.  Bottom-up sketches live at:

* R1, R2: `Jacobian/StageA/{SimplicialComplex, RadoTheorem,
  SpanningTree, PrismOperator, Hurewicz, EdgeWordTietze,
  CellularSingular}.lean`
* R3: `Jacobian/Periods/{Polygon4g*, SurfaceClassification,
  TietzeReduction, Polygon4gCellular,
  H1EvenBasisViaSurfaceClassification}.lean`
* R4: `Jacobian/StageB/{DifferentialForms, DeRhamComplex,
  DeRhamComparison}.lean`
* R5: `Jacobian/StageB/{LaplaceBeltrami, HarmonicForms,
  KahlerStructure}.lean`
* R6: `Jacobian/Periods/{HodgeDeRham,
  AnalyticGenusEqTopologicalGenus}.lean`
* R7: `Jacobian/HolomorphicForms/Serre/Dolbeault.lean`,
  `Jacobian/StageB/{KahlerStructure, CoherentSheaves}.lean`
* R8: `Jacobian/HolomorphicForms/Serre/*.lean` (32 files),
  `Jacobian/StageB/SerreDuality.lean`

The role of `Jacobian/Analysis/<Node>/Overview.lean` is to give each
gap a stable umbrella in a single named place, with `True`
placeholders for the per-phase sub-leaves, so future Aristotle /
cloud-worker tasks can target named obligations without first
descending into the bottom-up sketches.

## Recursive sub-gaps

Each node lists 3–5 recursive sub-gaps surfaced when its proof is
expanded.  See the per-node `Overview.lean` for the named list, and
`tex/sections/12-classical-analysis-gaps.tex` Section
`gap-summary` for the consolidated estimate.
