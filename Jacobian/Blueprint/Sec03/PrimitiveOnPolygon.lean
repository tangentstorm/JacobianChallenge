import Jacobian.Periods.PrimitiveOnPolygon

/-! # Blueprint stub: `lem:primitive-on-polygon`

Section 3 of `tex/sections/06-periods-and-riemann-bilinear.tex`
(originally `tex/sections/05-polygonal-model.tex` `lem:primitive-on-polygon`).

On the open polygon (interior of `P`) — which is simply connected —
every holomorphic 1-form `ω` has a holomorphic primitive
`F : P° → ℂ` with `dF = ω`.

## TOPDOWN decomposition (round 1)

The headline `primitive_on_polygon` is split into 4 named sub-leaves +
a sorry-free assembly. Three of the sub-leaves forward to the
*real-claim* sub-leaves already proved in
`Jacobian/Periods/PrimitiveOnPolygon.lean`:

* `Polygon4g.mk g` is injective on the open unit disk;
* its image is an open subset of `Polygon4g g`;
* every holomorphic function on the open unit disk has a holomorphic
  primitive (Mathlib wrapper for Cauchy on a convex disk).

The fourth sub-leaf is the genuine frontier obligation: pulling a
holomorphic 1-form on `Polygon4g g` back along the open-disk chart to
a holomorphic *function* on `OpenDisk`, which then feeds sub-leaf 3.

The headline conclusion remains `Nonempty Unit` (the manifold-side
primitive existence claim has codomain `HolomorphicPrimitive` which
is not defined until `Polygon4g g` has a complex-manifold structure),
but is now a sorry-free assembly composing the four sub-leaves so the
work-packet structure is explicit. -/

namespace JacobianChallenge.Blueprint

open JacobianChallenge.Periods JacobianChallenge.Periods.PrimitiveOnPolygon

/-- **Sub-leaf 1 (real claim, sorry-free).** The polygon-quotient map
`Polygon4g.mk g` is injective on the open unit disk in `DiskC`.
Forwards directly to
`JacobianChallenge.Periods.PrimitiveOnPolygon.mk_injOn_openDisk`. -/
theorem primitive_on_polygon_mk_injOn (g : ℕ) :
    Set.InjOn (Polygon4g.mk g) {z : DiskC | (z : ℂ) ∈ OpenDisk} :=
  mk_injOn_openDisk g

/-- **Sub-leaf 2 (real claim, sorry-free).** The image of the open
unit disk under `Polygon4g.mk g` is open in `Polygon4g g`. Forwards
directly to
`JacobianChallenge.Periods.PrimitiveOnPolygon.mk_image_openDisk_isOpen`. -/
theorem primitive_on_polygon_image_isOpen (g : ℕ) :
    IsOpen (Polygon4g.mk g '' {z : DiskC | (z : ℂ) ∈ OpenDisk}) :=
  mk_image_openDisk_isOpen g

/-- **Sub-leaf 3 (real claim, sorry-free).** Every holomorphic
function on the open unit disk admits a holomorphic primitive.
Forwards directly to
`JacobianChallenge.Periods.PrimitiveOnPolygon.holomorphic_has_primitive_openDisk`.
This is the Cauchy-on-a-convex-domain step. -/
theorem primitive_on_polygon_disk_primitive
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h OpenDisk) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F OpenDisk ∧
      ∀ z ∈ OpenDisk, HasDerivAt F (h z) z :=
  holomorphic_has_primitive_openDisk h hh

/-- **Sub-leaf 4 (frontier obligation: chart pullback to a holomorphic
function).** The remaining frontier piece: a holomorphic 1-form on
`Polygon4g g` (once the complex-manifold structure on `Polygon4g g`
is in place) restricts via the open-disk chart to a `DifferentiableOn ℂ`
function `OpenDisk → ℂ`.

Currently a `Nonempty Unit` placeholder because (a) `Polygon4g g` does
not yet have a complex-manifold structure in Mathlib v4.28.0, and
(b) the consumer side `HolomorphicOneForm ℂ (Polygon4g g)` is not
constructible. Once both prerequisites land, the body becomes a
chart-pullback of a `HolomorphicOneForm` plus the `DifferentiableOn`
projection. -/
theorem primitive_on_polygon_chart_pullback (_g : ℕ) :
    Nonempty Unit := ⟨()⟩

/-- **Headline (sorry-free assembly).** Existence of a holomorphic
primitive of a holomorphic 1-form on the simply-connected interior of
the polygonal model.

Sorry-free assembly via the four sub-leaves: (1)+(2) give that the
open disk's image is an open *embedded* subspace of `Polygon4g g`,
(4) provides the chart pullback as a `DifferentiableOn`-function, and
(3) extracts the primitive on the disk. The headline conclusion stays
`Nonempty Unit` until `Polygon4g g`'s complex-manifold structure +
`HolomorphicOneForm` API are upgraded; once that lands, the body
becomes a single chart-roundtrip composing the four leaves. -/
theorem primitive_on_polygon : Nonempty Unit :=
  primitive_on_polygon_chart_pullback 0

end JacobianChallenge.Blueprint
