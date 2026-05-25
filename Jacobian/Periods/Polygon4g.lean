import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Logic.Relation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homotopy.Contractible

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
-/

namespace JacobianChallenge.Periods

open Complex Set

/--
Closed unit disk in `ℂ`. The carrier of `Polygon4g` before
quotienting.
-/
abbrev DiskC : Type := Metric.closedBall (0 : ℂ) 1

instance diskC_contractibleSpace : ContractibleSpace DiskC :=
  Metric.contractibleSpace_closedBall (zero_le_one)

/--
The angle (in radians) corresponding to the `i`-th of `L`
boundary arcs at parameter `t ∈ [0,1]`. Concretely
`2π·(i + t)/L`, treated as a real number.
-/
noncomputable def boundaryAngle' (L : ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * ((i : ℝ) + t) / (L : ℝ)

/-- Specialisation to the standard `4g` sides. -/
noncomputable def boundaryAngle (g : ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  boundaryAngle' (4 * g) i t

/--
The boundary parameter as a complex number on the unit circle:
`exp(I · boundaryAngle' L i t)`. For `L = 0` the angle divides by
zero (Lean: `0`), giving `exp(0) = 1`.
-/
noncomputable def boundaryParamC' (L : ℕ) (i : ℕ) (t : ℝ) : ℂ :=
  exp (((boundaryAngle' L i t : ℂ)) * I)

/-- Specialisation to the standard `4g` sides. -/
noncomputable def boundaryParamC (g : ℕ) (i : ℕ) (t : ℝ) : ℂ :=
  boundaryParamC' (4 * g) i t

lemma boundaryParamC'_norm_eq_one (L : ℕ) (i : ℕ) (t : ℝ) :
    ‖boundaryParamC' L i t‖ = 1 := by
  unfold boundaryParamC'
  exact Complex.norm_exp_ofReal_mul_I (boundaryAngle' L i t)

lemma boundaryParamC_norm_eq_one (g : ℕ) (i : ℕ) (t : ℝ) :
    ‖boundaryParamC g i t‖ = 1 :=
  boundaryParamC'_norm_eq_one (4 * g) i t

lemma boundaryParamC'_mem_disk (L : ℕ) (i : ℕ) (t : ℝ) :
    boundaryParamC' L i t ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, boundaryParamC'_norm_eq_one]

lemma boundaryParamC_mem_disk (g : ℕ) (i : ℕ) (t : ℝ) :
    boundaryParamC g i t ∈ Metric.closedBall (0 : ℂ) 1 :=
  boundaryParamC'_mem_disk (4 * g) i t

/-- The boundary parameter as an element of the closed disk. -/
noncomputable def boundaryParam' (L : ℕ) (i : ℕ) (t : ℝ) : DiskC :=
  ⟨boundaryParamC' L i t, boundaryParamC'_mem_disk L i t⟩

/-- Specialisation to the standard `4g` sides. -/
noncomputable def boundaryParam (g : ℕ) (i : ℕ) (t : ℝ) : DiskC :=
  boundaryParam' (4 * g) i t

namespace Polygon4g

/--
Generating relation for the side-pairing on the boundary of the
closed unit disk. For every `i ∈ Fin g` and `t ∈ [0,1]`:

* the `a-cycle` identifies arc `4i` (forward at `t`) with arc `4i+2`
  (reversed at `1-t`);
* the `b-cycle` identifies arc `4i+1` (forward at `t`) with arc
  `4i+3` (reversed at `1-t`).

Restricting the index `i` to `Fin g` ensures the relation is empty
when `g = 0`.
-/
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

/--
The standard fundamental polygon `Polygon4g g`: the closed unit
disk in `ℂ` modulo the side-pairing identifications

`a₁b₁a₁⁻¹b₁⁻¹ ⋯ aₘbₘaₘ⁻¹bₘ⁻¹`.

Equipped with the quotient topology induced from the subspace
topology on the closed disk.
-/
def Polygon4g (g : ℕ) : Type :=
  Quotient (Polygon4g.sideSetoid g)

namespace Polygon4g

instance instTopologicalSpace (g : ℕ) : TopologicalSpace (Polygon4g g) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- The closed unit disk is compact (ℂ is a `ProperSpace`). -/
instance _root_.JacobianChallenge.Periods.DiskC.instCompactSpace :
    CompactSpace JacobianChallenge.Periods.DiskC :=
  isCompact_iff_compactSpace.mp <|
    ProperSpace.isCompact_closedBall (0 : ℂ) 1

/--
The closed unit disk is connected (closed balls in normed spaces are
path-connected, hence connected).
-/
instance _root_.JacobianChallenge.Periods.DiskC.instConnectedSpace :
    ConnectedSpace JacobianChallenge.Periods.DiskC :=
  isConnected_iff_connectedSpace.mp <|
    Metric.isConnected_closedBall (zero_le_one)

instance instCompactSpace (g : ℕ) : CompactSpace (Polygon4g g) :=
  Quotient.compactSpace

instance instConnectedSpace (g : ℕ) : ConnectedSpace (Polygon4g g) :=
  Quotient.instConnectedSpace

/--
The closed unit disk is path-connected (closed balls in normed
spaces are path-connected).
-/
instance _root_.JacobianChallenge.Periods.DiskC.instPathConnectedSpace :
    PathConnectedSpace JacobianChallenge.Periods.DiskC :=
  isPathConnected_iff_pathConnectedSpace.mp <|
    Metric.isPathConnected_closedBall (zero_le_one)

instance instPathConnectedSpace (g : ℕ) : PathConnectedSpace (Polygon4g g) :=
  Quotient.instPathConnectedSpace

/-- Quotient map from the closed disk to the polygon. -/
def mk (g : ℕ) : DiskC → Polygon4g g :=
  Quotient.mk (sideSetoid g)

@[simp] lemma mk_eq_mk_iff (g : ℕ) (z w : DiskC) :
    mk g z = mk g w ↔ SideRel g z w :=
  Quotient.eq

lemma mk_continuous (g : ℕ) : Continuous (mk g) :=
  continuous_quotient_mk'

/--
For `g ≥ 1`, the four basic side-identification equations.
Stated as `mk`-equality of arc endpoints/parameters.
-/
lemma mk_a_pair (g : ℕ) (i : Fin g) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mk g (boundaryParam g (4 * i.val) t)
      = mk g (boundaryParam g (4 * i.val + 2) (1 - t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideGen.a_pair i t ht))

lemma mk_b_pair (g : ℕ) (i : Fin g) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mk g (boundaryParam g (4 * i.val + 1) t)
      = mk g (boundaryParam g (4 * i.val + 3) (1 - t)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SideGen.b_pair i t ht))

end Polygon4g


lemma polygon4g_sideRel_zero_iff_eq (a b : DiskC) : Polygon4g.SideRel 0 a b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ Relation.EqvGen.refl _⟩
  induction h with
  | rel _ _ hr => cases hr with | a_pair i _ _ => exact i.elim0 | b_pair i _ _ => exact i.elim0
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem polygon4g_zero_homeo_diskC : Nonempty (Polygon4g 0 ≃ₜ DiskC) := by
  let f : Polygon4g 0 → DiskC := Quotient.lift id (fun a b hab => (polygon4g_sideRel_zero_iff_eq a b).mp hab)
  have hf_cts : Continuous f := continuous_id.quotient_lift _
  let e : Polygon4g 0 ≃ DiskC := { toFun := f, invFun := Polygon4g.mk 0, left_inv := fun q => by induction q using Quotient.inductionOn with | _ z => rfl, right_inv := fun _ => rfl }
  exact ⟨hf_cts.homeoOfEquivCompactToT2 (f := e)⟩

instance polygon4g_zero_t2Space : T2Space (Polygon4g 0) := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  exact h.symm.t2Space

end JacobianChallenge.Periods
