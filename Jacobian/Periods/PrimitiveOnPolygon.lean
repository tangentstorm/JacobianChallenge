import Jacobian.Periods.Polygon4g
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Primitive of a holomorphic 1-form on the polygon (sub-leaves)

Plan: `ref/plans/primitive-on-polygon.md` (route: power-series /
Cauchy on the convex open disk; Poincaré-lemma machinery
unnecessary).

This file scaffolds three sub-leaves of
`lem:primitive-on-polygon`:

1. `mk_injOn_openDisk` — `Polygon4g.mk g` is injective on the open
   unit disk (`SideRel g` only identifies boundary points).
2. `mk_image_openDisk_isOpen` — its image is an open subset of
   `Polygon4g g` (the polygon's interior `P°`).
3. `holomorphic_has_primitive_openDisk` — every holomorphic function
   on the open disk has a holomorphic primitive (Mathlib wrapper for
   Cauchy on a convex disk).

The umbrella `lem:primitive-on-polygon` (assembling these into a
holomorphic-1-form-level statement) is deferred to
`Jacobian/Blueprint/Sec03/PrimitiveOnPolygon.lean`, which currently
remains a `True := trivial` placeholder pending a complex-manifold
structure on `Polygon4g`.

All three sub-leaves are independently Aristotle-attackable; their
proofs reduce to project-local `Polygon4g.SideRel` reasoning and
Mathlib v4.28.0 complex analysis on disks. No Stokes, no surface
classification.
-/

namespace JacobianChallenge.Periods

open Complex Set

/-- The open unit disk in `ℂ`. -/
abbrev OpenDisk : Set ℂ := Metric.ball (0 : ℂ) 1

namespace PrimitiveOnPolygon

/-- **Sub-leaf 1 (SHORT).** The polygon-quotient map `Polygon4g.mk g`
is injective when restricted to points of `DiskC` whose underlying
`ℂ`-value lies in the open unit disk.

Proof sketch: by `Polygon4g.mk_eq_mk_iff`, two disk points are
identified iff related by `Polygon4g.SideRel g`. Inspection of the
constructors of `SideGen g` shows every related pair lies on the
boundary `‖z‖ = 1` (via `boundaryParamC_norm_eq_one`). Points strictly
inside the disk satisfy `‖z‖ < 1`, so they cannot participate in any
`SideGen` step; the equivalence closure on interior points reduces
to equality. -/
theorem mk_injOn_openDisk (g : ℕ) :
    Set.InjOn (Polygon4g.mk g) {z : DiskC | (z : ℂ) ∈ OpenDisk} := by
  sorry

/-- **Sub-leaf 2 (SHORT).** The image of the open unit disk under
`Polygon4g.mk g` is open in `Polygon4g g`.

Proof sketch: the quotient map `Polygon4g.mk g` is continuous
(`Polygon4g.mk_continuous`), and `OpenDisk` is open in `DiskC`. Use
`isOpen_iff_preimage_isOpen` for the quotient topology together with
sub-leaf 1 (so the preimage of the image equals `OpenDisk` itself,
not a larger saturation). -/
theorem mk_image_openDisk_isOpen (g : ℕ) :
    IsOpen (Polygon4g.mk g '' {z : DiskC | (z : ℂ) ∈ OpenDisk}) := by
  sorry

/-- **Sub-leaf 3 (MEDIUM).** Every holomorphic function on the open
unit disk has a holomorphic primitive.

Proof sketch: `OpenDisk = Metric.ball (0 : ℂ) 1` is convex (general
fact about balls in normed spaces). Use Mathlib's primitive on a
convex domain: `Convex.exists_primitive_of_differentiableOn` or a
near-equivalent (effective lemma name in v4.28.0 may be
`DifferentiableOn.exists_primitive_on_convex` /
`Complex.has_primitive_of_holomorphicOn` — Aristotle should grep the
disk-Cauchy module). The primitive `F` is automatically holomorphic
because its derivative exists pointwise. -/
theorem holomorphic_has_primitive_openDisk
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h OpenDisk) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F OpenDisk ∧
      ∀ z ∈ OpenDisk, HasDerivAt F (h z) z := by
  sorry

end PrimitiveOnPolygon

end JacobianChallenge.Periods
