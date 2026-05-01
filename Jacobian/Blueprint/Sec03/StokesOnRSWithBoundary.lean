import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # Blueprint stubs: sub-leaves of `thm:stokes-on-rs-with-boundary`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

The umbrella theorem `thm:stokes-on-rs-with-boundary` is classified
**DECOMPOSE** in `ref/scope-out.md`. The full eight-leaf decomposition,
harvested from a ChatGPT planning pass, is in
`ref/plans/stokes-on-rs-with-boundary.md`. This file gives every leaf a
concrete Lean handle:

* leaves **#1 / #2** (SHORT): `True`-valued placeholders — the real
  signatures are too tangled with the corner-modelled boundary API to
  pin down at this stage and will be revisited in a follow-up.
* leaves **#3 / #4** (HARD): concrete `noncomputable def`s with
  manifold-with-corners hypotheses and a placeholder body `0`. These
  pin down the call shape (`integrateTwoForm M ω : ℝ` and
  `integrateOneFormBoundary M ω : ℝ`) so #5–#8 can already speak about
  them.
* leaves **#5 / #6 / #7 / #8** (MEDIUM / HARD): concrete `theorem`
  statements whose conclusions are equalities of the
  `integrateTwoForm` / `integrateOneFormBoundary` functionals (or, for
  #5, an honest Green's-theorem equality of nested interval integrals
  in `ℝ²`); proofs are `sorry` and assigned to follow-up workers.

The `*Aux` form types `TwoFormAux M := M → ℝ` and
`OneFormAux M := M → ℝ` are deliberate placeholders: Mathlib v4.28.0's
inventory entry "Integration of differential forms" is **ABSENT**, so
committing to a real differential-form type today would lock the whole
decomposition behind an unresolved upstream question. Once the
manifold-side exterior-derivative + integration API lands, every
declaration here gets a like-for-like signature replacement (same name,
same arity, real form types).

Imports are deliberately narrow per integrator policy — no
`import Mathlib`. The current set is exactly the manifold-with-corners
model (`WithCorners` + `Instances.Real`) and the real-analysis kernel
(`IntervalIntegral.Basic` + `FDeriv.Basic`) that #5 needs to state
Green's theorem.
-/

namespace JacobianChallenge.Blueprint.Sec03

open scoped Manifold

/-! ## Auxiliary placeholder form types

Both are `M → ℝ` while the real differential-form API is unavailable.
Downstream signatures use these names so the eventual type swap is
mechanical. -/

/-- Placeholder for a 2-form on `M`: scalar density representation. -/
abbrev TwoFormAux (M : Type*) : Type _ := M → ℝ

/-- Placeholder for a 1-form on `M`: scalar coefficient representation. -/
abbrev OneFormAux (M : Type*) : Type _ := M → ℝ

/-- Placeholder predicate "the 2-form `η` is the exterior derivative of
the 1-form `ω`". Trivially `True` while the real exterior-derivative API
is unavailable; carried as a hypothesis on Stokes-shaped statements so
the eventual swap-in lemma has a stable name. -/
def IsExteriorDerivativeAux {M : Type*} (_ω : OneFormAux M)
    (_η : TwoFormAux M) : Prop := True

/-! ## Sub-leaf #1 (SHORT) — preserved from the previous stub commit. -/

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
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Prop
```

Placeholder body: `True`. -/
theorem manifold_with_corners_2d : True := trivial

/-- **Sub-leaf #2 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: for a 2D manifold with corners `M`, the boundary
`∂M` is the set of points whose chart image lies in the boundary of
`(ℝ≥0)²`, and inherits the structure of a 1-manifold with corners.

Eventual Lean signature, layered on `manifold_with_corners_2d`:
```
def boundary1D
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Set M
```

Placeholder body: `True`. -/
theorem boundary_1d : True := trivial

/-! ## Sub-leaf #3 (HARD) — integration of a 2-form. -/

/-- **Sub-leaf #3 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_M ω` of a 2-form `ω` on a compact 2-manifold with
corners. The eventual definition uses a smooth partition of unity
subordinate to a finite atlas, pulls each summand back to a chart in
`(ℝ≥0)²`, and Lebesgue-integrates against the standard 2D volume form.

Currently a placeholder returning `0`. The signature is the production
call shape — `integrateTwoForm M ω : ℝ` — so #5–#8 can already speak
about it. -/
noncomputable def integrateTwoForm
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : TwoFormAux M) : ℝ := 0

/-! ## Sub-leaf #4 (HARD) — boundary integral of a 1-form. -/

/-- **Sub-leaf #4 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_{∂M} ω` of a 1-form `ω` along the oriented boundary of a
compact 2-manifold with corners. The eventual definition decomposes
`∂M` into oriented edges (piecewise smooth curves meeting at corners)
and sums the line integrals, using the outward-normal-first convention
to fix the boundary orientation.

Currently a placeholder returning `0`. Depends on sub-leaf #2 for the
underlying boundary structure. -/
noncomputable def integrateOneFormBoundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) : ℝ := 0

/-! ## Sub-leaf #5 (MEDIUM) — Green's theorem on a rectangle. -/

/-- **Sub-leaf #5 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Green's theorem on the axis-aligned rectangle `[a, b] × [c, d] ⊂ ℝ²`:
for `C¹` scalar fields `P, Q : ℝ × ℝ → ℝ`,

```
∮_{∂R} (P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y).
```

The boundary integral is written explicitly as the sum of the four edge
integrals (with the standard counter-clockwise orientation on the
rectangle), and the partial derivatives are read off the Fréchet
derivative `fderiv ℝ` evaluated at the basis vectors `(1, 0)` and
`(0, 1)` of `ℝ × ℝ`.

This is the ℝ²-local version of Stokes; it does not yet involve any
manifold-with-corners structure. Proof is deferred — the standard
calculus argument is via Fubini + `intervalIntegral.integral_deriv_eq_sub`
on each axis-parallel slice. -/
theorem stokes_local_euclidean
    (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hP : ContDiff ℝ 1 P) (_hQ : ContDiff ℝ 1 Q) :
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
  sorry

/-! ## Sub-leaf #6 (MEDIUM) — Stokes in a single chart. -/

/-- **Sub-leaf #6 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Single-chart Stokes: when the 1-form `ω` has support inside the domain
of a single corner chart, the global Stokes identity
`∫_M dω = ∫_{∂M} ω` reduces to the ℝ²-local statement
(`stokes_local_euclidean`) after pull-back through the chart and
push-forward of the result.

The chart-localisation hypothesis is recorded as the placeholder
`_hsupp : True` while the support API for `OneFormAux` is unavailable;
the eventual replacement is `tsupport ω ⊆ chartAt _ p.source` for some
`p : M`.

Proof is deferred (depends on #3 and #5 plus a chart-pullback
compatibility lemma for the placeholder form types). -/
theorem stokes_chart
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω)
    (_hsupp : True) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  sorry

/-! ## Sub-leaf #7 (HARD) — globalisation via partition of unity. -/

/-- **Sub-leaf #7 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

Global Stokes via partition of unity: for any smooth 1-form `ω` on a
compact 2-manifold with corners `M` (no support hypothesis — every form
is automatically compactly supported by compactness of `M`), the
identity `∫_M dω = ∫_{∂M} ω` holds.

Proof outline (deferred): pick a finite atlas, take a smooth partition
of unity `{ρ_i}` subordinate to it, write
`ω = Σ_i ρ_i ω` and `dω = Σ_i d(ρ_i ω)`, apply `stokes_chart` to each
chart-localised summand, and sum. Boundary terms cancel on interior
chart overlaps and add up on the global `∂M`. -/
theorem stokes_partition_unity
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  sorry

/-! ## Sub-leaf #8 (MEDIUM) — Stokes on a Riemann surface with boundary. -/

/-- **Sub-leaf #8 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

The umbrella conclusion: on a compact oriented 2-manifold with corners
`M` carrying a Riemann-surface structure on its interior (e.g. the
4g-gon fundamental polygon model of a closed Riemann surface, before
edge identifications), Stokes' theorem holds:

```
∫_{∂M} ω = ∫_M dω.
```

This specialises `stokes_partition_unity` to the Riemann-surface
setting; the only content beyond #7 is rewriting the equation in the
classical "boundary on the left" form and discharging the support
hypothesis using compactness.

Proof is deferred and assigned to follow-up workers; it is expected to
be a one-liner once #7 lands. -/
theorem stokes_on_rs_with_boundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω) :
    integrateOneFormBoundary M ω = integrateTwoForm M dω := by
  sorry

end JacobianChallenge.Blueprint.Sec03
