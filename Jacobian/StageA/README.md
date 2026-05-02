# Stage A — Bottom-up infrastructure sketch

This directory contains stub sketches of the **bottom-up** Lean
infrastructure that Stage A of the polygonal-model proof needs.

## Files

| File | Topic | LOC | Mathlib gap |
|---|---|---|---|
| `SimplicialComplex.lean` | Abstract simplicial complexes, geometric realisation, pseudomanifold conditions, barycentric subdivision | ~180 | Total absence |
| `RadoTheorem.lean` | Radó's triangulability of compact 2-manifolds | ~150 | Total absence |
| `SpanningTree.lean` | Spanning-tree existence on finite connected `SimpleGraph` | ~90 | Partial — `SimpleGraph.IsTree` exists, existence theorem missing |
| `PrismOperator.lean` | Chain-level prism construction giving homotopy-invariance of singular homology | ~125 | Total absence |
| `Hurewicz.lean` | Hurewicz isomorphism `H₁(X, ℤ) ≅ π₁(X)^{ab}` | ~120 | Total absence |
| `EdgeWordTietze.lean` | Brahana–Seifert–Threlfall reduction of edge words | ~155 | Total absence |
| `CellularSingular.lean` | Cellular vs singular `H₁` comparison | ~130 | Total absence |

Each file is a **sketch** — every theorem is `sorry`, but the
statement-level shape, the named obligations, and the
proof-route documentation are committed to. A full Lean implementation
of the bottom-up content would be ~3000-5000 LOC (these stubs are
~950 LOC, exhibiting ~120 typed declarations).

## Wiring

These files **do not** import or wire into the existing helper modules
(`Jacobian/Periods/SurfaceClassification.lean`, `RadoTriangulation.lean`,
…). They live in parallel as a **bottom-up roadmap**: each obligation
in the existing helper modules will, when discharged, cite one or more
results from these Stage A files.

## Status

`lake build Jacobian.StageA.<File>` builds for each file (with
sorries).
