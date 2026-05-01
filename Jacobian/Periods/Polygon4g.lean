import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Logic.Relation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions

/-!
# Standard fundamental polygon `Polygon4g`

For each genus `g : ℕ`, this file constructs the topological space
`Polygon4g g`, obtained from the closed unit disk in `ℂ` by
identifying its boundary in the standard 4g-gon side-pairing pattern

  `a₁b₁a₁⁻¹b₁⁻¹ ⋯ aₘbₘaₘ⁻¹bₘ⁻¹`

(four consecutive boundary arcs per "handle" `i ∈ Fin g`, identified
in pairs with reversal).

This is the codomain of the polygonal-model homeomorphism for compact
connected oriented genus-`g` Riemann surfaces (sec03 of the project
blueprint, `thm:polygonal-model`).

## Design

* `DiskC` — closed unit disk in `ℂ` as a subtype.
* `boundaryParam g i t` — the `i`-th of `4g` boundary arcs at
  parameter `t ∈ [0,1]`, lifted to `DiskC`. The arc maps to the disk
  boundary at angle `2π·(i + t)/(4g)`.
* `Polygon4g.SideGen g` — the *generating* relation pairing arcs
  `4i ↔ 4i+2` (a-cycle) and `4i+1 ↔ 4i+3` (b-cycle), each with
  parameter reversal `t ↔ 1-t`, for every `i ∈ Fin g`.
* `Polygon4g.SideRel g` — the equivalence closure of `SideGen g`.
* `Polygon4g g` — `DiskC / SideRel g`, with the induced quotient
  topology.

## Genus-0 caveat

For `g = 0` the formula in `boundaryParamC` divides by zero, but Lean
defines `(0 : ℂ)⁻¹ = 0`, so the value is well-defined garbage (the
origin of `ℂ`). The relation `SideGen 0` has no inhabitants (the
constructors require `i < 0`), so `SideRel 0` collapses to equality
and `Polygon4g 0` is the closed disk. The genuine genus-0 polygonal
model is the sphere, but the period-lattice chain in sec03 only uses
`Polygon4g g` for `g ≥ 1`, so we do not implement the `g = 0` branch
correctly.

## Future work

* `Polygon4g.compactSpace`, `Polygon4g.t2Space`,
  `Polygon4g.connectedSpace` — basic topological properties inherited
  from the disk via the quotient map (deferred).
* `polygon4g_interior_simply_connected` — needed by
  `lem:primitive-on-polygon` (deferred).
-/

namespace JacobianChallenge.Periods

open Complex Set

/-- Closed unit disk in `ℂ`. The carrier of `Polygon4g` before
quotienting. -/
abbrev DiskC : Type := Metric.closedBall (0 : ℂ) 1

/-- The angle (in radians) corresponding to the `i`-th of `4g`
boundary arcs at parameter `t ∈ [0,1]`. Concretely
`2π·(i + t)/(4g)`, treated as a real number. -/
noncomputable def boundaryAngle (g : ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * ((i : ℝ) + t) / (4 * (g : ℝ))

/-- The boundary parameter as a complex number on the unit circle:
`exp(I · boundaryAngle g i t)`. For `g = 0` the angle divides by
zero (Lean: `0`), giving `exp(0) = 1`. -/
noncomputable def boundaryParamC (g : ℕ) (i : ℕ) (t : ℝ) : ℂ :=
  exp (((boundaryAngle g i t : ℂ)) * I)

lemma boundaryParamC_norm_eq_one (g : ℕ) (i : ℕ) (t : ℝ) :
    ‖boundaryParamC g i t‖ = 1 := by
  unfold boundaryParamC
  exact Complex.norm_exp_ofReal_mul_I (boundaryAngle g i t)

lemma boundaryParamC_mem_disk (g : ℕ) (i : ℕ) (t : ℝ) :
    boundaryParamC g i t ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, boundaryParamC_norm_eq_one]

/-- The boundary parameter as an element of the closed disk. -/
noncomputable def boundaryParam (g : ℕ) (i : ℕ) (t : ℝ) : DiskC :=
  ⟨boundaryParamC g i t, boundaryParamC_mem_disk g i t⟩

namespace Polygon4g

/-- Generating relation for the side-pairing on the boundary of the
closed unit disk. For every `i ∈ Fin g` and `t ∈ [0,1]`:

* the `a-cycle` identifies arc `4i` (forward at `t`) with arc `4i+2`
  (reversed at `1-t`);
* the `b-cycle` identifies arc `4i+1` (forward at `t`) with arc
  `4i+3` (reversed at `1-t`).

Restricting the index `i` to `Fin g` ensures the relation is empty
when `g = 0`. -/
inductive SideGen (g : ℕ) : DiskC → DiskC → Prop
  | a_pair (i : Fin g) (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
      SideGen g
        (boundaryParam g (4 * i.val) t)
        (boundaryParam g (4 * i.val + 2) (1 - t))
  | b_pair (i : Fin g) (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
      SideGen g
        (boundaryParam g (4 * i.val + 1) t)
        (boundaryParam g (4 * i.val + 3) (1 - t))

/-- The reflexive-symmetric-transitive closure of `SideGen g`. -/
def SideRel (g : ℕ) : DiskC → DiskC → Prop :=
  Relation.EqvGen (SideGen g)

lemma SideRel.equivalence (g : ℕ) : Equivalence (SideRel g) :=
  Relation.EqvGen.is_equivalence (SideGen g)

/-- Side-pairing as a setoid on the closed unit disk. -/
def sideSetoid (g : ℕ) : Setoid DiskC where
  r := SideRel g
  iseqv := SideRel.equivalence g

end Polygon4g

/-- The standard fundamental polygon `Polygon4g g`: the closed unit
disk in `ℂ` modulo the side-pairing identifications

  `a₁b₁a₁⁻¹b₁⁻¹ ⋯ aₘbₘaₘ⁻¹bₘ⁻¹`.

Equipped with the quotient topology induced from the subspace
topology on the closed disk. -/
def Polygon4g (g : ℕ) : Type :=
  Quotient (Polygon4g.sideSetoid g)

namespace Polygon4g

instance instTopologicalSpace (g : ℕ) : TopologicalSpace (Polygon4g g) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- Quotient map from the closed disk to the polygon. -/
def mk (g : ℕ) : DiskC → Polygon4g g :=
  Quotient.mk (sideSetoid g)

@[simp] lemma mk_eq_mk_iff (g : ℕ) (z w : DiskC) :
    mk g z = mk g w ↔ SideRel g z w :=
  Quotient.eq

lemma mk_continuous (g : ℕ) : Continuous (mk g) :=
  continuous_quotient_mk'

/-- For `g ≥ 1`, the four basic side-identification equations.
Stated as `mk`-equality of arc endpoints/parameters. -/
lemma mk_a_pair (g : ℕ) (i : Fin g) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mk g (boundaryParam g (4 * i.val) t)
      = mk g (boundaryParam g (4 * i.val + 2) (1 - t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideGen.a_pair i t ht))

lemma mk_b_pair (g : ℕ) (i : Fin g) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mk g (boundaryParam g (4 * i.val + 1) t)
      = mk g (boundaryParam g (4 * i.val + 3) (1 - t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideGen.b_pair i t ht))

end Polygon4g

end JacobianChallenge.Periods
