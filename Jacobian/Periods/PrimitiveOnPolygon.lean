import Jacobian.Periods.Polygon4g
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.HasPrimitives

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
   on the open unit disk has a holomorphic primitive (Mathlib wrapper for
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

/-! ### Helper lemmas: `SideGen` only relates boundary points -/

namespace Polygon4g

/-- Every left-hand side of a `SideGen` identification has norm 1
(i.e. lies on the boundary of the unit disk). -/
private lemma SideGen.norm_left {g : ℕ} {z w : DiskC}
    (h : SideGen g z w) : ‖(z : ℂ)‖ = 1 := by
  cases h with
  | a_pair i t _ => exact boundaryParamC_norm_eq_one g (4 * i.val) t
  | b_pair i t _ => exact boundaryParamC_norm_eq_one g (4 * i.val + 1) t

/-- Every right-hand side of a `SideGen` identification has norm 1. -/
private lemma SideGen.norm_right {g : ℕ} {z w : DiskC}
    (h : SideGen g z w) : ‖(w : ℂ)‖ = 1 := by
  cases h with
  | a_pair i t _ => exact boundaryParamC_norm_eq_one g (4 * i.val + 2) (1 - t)
  | b_pair i t _ => exact boundaryParamC_norm_eq_one g (4 * i.val + 3) (1 - t)

/-- If `z` or `w` lies strictly inside the open disk (`‖·‖ < 1`),
then `EqvGen (SideGen g) z w` forces `z = w`. The equivalence closure
cannot cross the boundary because every generating pair has both
points on the boundary. -/
private lemma eqvGen_sideGen_eq_of_norm_lt {g : ℕ} {z w : DiskC}
    (h : Relation.EqvGen (SideGen g) z w)
    (hor : ‖(z : ℂ)‖ < 1 ∨ ‖(w : ℂ)‖ < 1) : z = w := by
  induction h with
  | rel a b hr =>
    exact absurd (by rcases hor with ha | hb
                     · exact absurd hr.norm_left (ne_of_lt ha)
                     · exact absurd hr.norm_right (ne_of_lt hb)) id
  | refl _ => rfl
  | symm _ _ _ ih => exact (ih hor.symm).symm
  | trans _ _ _ _ _ ih1 ih2 =>
    rcases hor with hz | hw
    · have hab := ih1 (Or.inl hz)
      exact hab ▸ ih2 (Or.inl (hab ▸ hz))
    · have hbc := ih2 (Or.inr hw)
      exact (ih1 (Or.inr (hbc ▸ hw))) ▸ hbc

end Polygon4g

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
  intro z hz w _hw hmk
  rw [Polygon4g.mk_eq_mk_iff] at hmk
  exact Polygon4g.eqvGen_sideGen_eq_of_norm_lt hmk
    (Or.inl (by simp [OpenDisk, Metric.mem_ball, dist_zero_right] at hz; exact hz))

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
  obtain ⟨F, hF⟩ := hh.isExactOn_ball
  exact ⟨F, fun z hz => (hF z hz).differentiableAt.differentiableWithinAt, hF⟩

end PrimitiveOnPolygon

end JacobianChallenge.Periods
