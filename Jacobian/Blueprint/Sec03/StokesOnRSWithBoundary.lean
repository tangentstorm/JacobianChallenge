/-! # Blueprint stubs: sub-leaves of `thm:stokes-on-rs-with-boundary`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

The umbrella theorem `thm:stokes-on-rs-with-boundary` is classified
**DECOMPOSE** in `ref/scope-out.md`. The full eight-leaf decomposition,
harvested from a ChatGPT planning pass, is in
`ref/plans/stokes-on-rs-with-boundary.md`. Only the two leaves classified
**SHORT** by that plan are stubbed in this file; each is a `True`-valued
placeholder whose docstring records the eventual mathematical statement
and the Mathlib infrastructure it will need to land on top of.

The remaining six leaves (#3, #4 — HARD; #5, #6, #8 — MEDIUM; #7 — HARD)
are tracked in the `Future leaves` section at the bottom of this file as
prose only; they need their own files / cloud workers and are
deliberately not yet declared as Lean symbols, to avoid premature name
commitments.

This file is intentionally Mathlib-free: every placeholder lives in core
Lean so the build cost is negligible and downstream consumers can import
the names without dragging in heavy manifold infrastructure before the
real proofs land.
-/

namespace JacobianChallenge.Blueprint.Sec03

/-- **Sub-leaf #1 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: a 2-dimensional smooth manifold with corners is a
second-countable Hausdorff topological space `M` equipped with an atlas
of charts into the model corner space `(ℝ≥0)²`, with smooth transition
maps. This is the structure carried by a 4g-gon fundamental polygon
before edge identifications.

Eventual Lean signature, once the corner-modeled manifold API stabilises:
```
def manifoldWithCorners2D
    (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Prop
```
where `EuclideanHalfSpace`/`modelWithCornersEuclideanQuadrant` come from
`Mathlib.Geometry.Manifold.Instances.Real` and the corner extension
landed in `Mathlib.Geometry.Manifold.WithCorners`.

Placeholder body: `True`. The plan estimates ≤20 LOC once the surrounding
manifold typeclasses are in scope. -/
theorem manifold_with_corners_2d : True := trivial

/-- **Sub-leaf #2 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: for a 2D manifold with corners `M`, the boundary
`∂M` is the set of points whose chart image lies in the boundary of
`(ℝ≥0)²`, and inherits the structure of a 1-manifold with corners
(edges + vertices). For the 4g-gon model this is the union of the 4g
oriented edges meeting at vertices.

Eventual Lean signature, layered on `manifold_with_corners_2d`:
```
def boundary1D
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Set M
```
with the induced 1-manifold-with-corners structure exported as a separate
instance/lemma. Mathlib's partial `Mathlib/Geometry/Manifold/Boundary`
should supply the underlying set; the corner refinement (vertex set as
codimension-2 stratum) is the new content this leaf provides.

Placeholder body: `True`. The plan estimates ≤20 LOC, single helper. -/
theorem boundary_1d : True := trivial

/-! ## Future leaves (not yet stubbed)

The remaining six sub-leaves of `thm:stokes-on-rs-with-boundary` are not
TRIVIAL/SHORT and are out of scope for this stub file. They are recorded
here for traceability:

- **#3 `integrateTwoForm` — HARD.** Define `∫_M ω` for a 2-form via
  partition of unity + chart pullback to ℝ² + Lebesgue integral.
  Blocked on `ABSENT` Mathlib status for "Integration of differential
  forms".
- **#4 `integrateOneFormBoundary` — HARD.** Define `∫_{∂M} ω` as a sum
  over oriented edges (piecewise smooth curves) with corner
  compatibility. Depends on #2.
- **#5 `stokes_local_euclidean` — MEDIUM.** Stokes on rectangles /
  polygons in ℝ² via Green's theorem; pure real analysis, no manifold
  layer.
- **#6 `stokes_chart` — MEDIUM.** Pull back to a single ℝ² chart, apply
  #5, push forward. Depends on #3, #5.
- **#7 `stokes_partition_unity` — HARD.** Glue local results via
  partition of unity; verify boundary terms sum correctly. Depends on
  #3, #4, #6.
- **#8 `stokes_on_rs_with_boundary` — MEDIUM.** Specialise #7 to a
  compact oriented 2D manifold with corners (e.g. the 4g-gon model);
  simplify support hypotheses using compactness.

Each future leaf should land in its own `Sec03/Stokes*.lean` file under
this same namespace, following the per-leaf-file convention used by
`Sec01` and `Sec02`. The total LOC estimate from the harvested plan is
~1800. -/

end JacobianChallenge.Blueprint.Sec03
