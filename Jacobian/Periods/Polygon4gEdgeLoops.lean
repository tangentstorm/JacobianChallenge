import Jacobian.Periods.Polygon4g
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.UnitInterval

/-!
# Concrete edge loops on the standard polygon `Polygon4g (g+1)`

For each `i : Fin (2 * (g + 1))`, the i-th edge class of the standard
genus-`(g+1)` polygon is represented by a concrete continuous loop
`unitInterval → Polygon4g (g + 1)` obtained by composing the boundary
parametrisation with the quotient map.

The standard 4(g+1)-gon has its `4(g+1)` boundary arcs paired as

`arc 4j ↔ arc 4j+2` (a-pair, reversed),
  `arc 4j+1 ↔ arc 4j+3` (b-pair, reversed),

for `j : Fin (g+1)`. The 2(g+1) distinct edge classes can be indexed by
`i : Fin (2*(g+1))` where `i = 2j` selects the a-edge of pair `j` and
`i = 2j+1` selects the b-edge of pair `j`. The corresponding boundary
arc index is `arcIdx i = 4 * (i / 2) + (i % 2)`.

These loops are **closed** in `Polygon4g (g+1)` because the side-pairings
identify all `4(g+1)` polygon vertices to a single point in the
quotient (transitive closure of the side-pairing identifications takes
every vertex to vertex 0). This file provides the construction; the
loop-closure property is recorded by callers as needed.

## Status

This is supporting infrastructure for the cellular Hurewicz route in
`Jacobian.Periods.Polygon4gCellular`. It is **not** consumed by the
current iso reassembly (which goes through the structure theorem for
finite-type torsion-free `ℤ`-modules); it is provided so that future
work refining the three sub-leaves there into edge-cycle-based
statements can use these concrete loops directly without re-deriving
continuity.
-/

namespace JacobianChallenge.Periods

open Complex Set unitInterval

/--
The index of the boundary arc representing the `i`-th edge class of
the genus-`(g+1)` polygon. For `i : Fin (2*(g+1))`, `i = 2j` selects
arc `4j` (the a-edge of pair `j`) and `i = 2j+1` selects arc `4j+1`
(the b-edge of pair `j`).
-/
def edgeArcIdx (g : ℕ) (i : Fin (2 * (g + 1))) : ℕ :=
  4 * (i.val / 2) + (i.val % 2)

lemma boundaryAngle_continuous (g i : ℕ) :
    Continuous (boundaryAngle g i) := by
  unfold boundaryAngle boundaryAngle'
  fun_prop

lemma boundaryParamC_continuous (g i : ℕ) :
    Continuous (boundaryParamC g i) := by
  unfold boundaryParamC
  refine continuous_exp.comp ?_
  refine .mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (boundaryAngle_continuous g i)

lemma boundaryParam_continuous (g i : ℕ) :
    Continuous (boundaryParam g i) := by
  unfold boundaryParam
  exact (boundaryParamC_continuous g i).subtype_mk _

/--
The `i`-th edge loop on the genus-`(g+1)` polygon, parameterised by
the unit interval `[0,1]`. As a map into `Polygon4g (g+1)` (the disk
quotient), the start and end points coincide because all polygon
vertices are identified by the side-pairings.
-/
noncomputable def edgeContMap (g : ℕ) (i : Fin (2 * (g + 1))) :
    C(unitInterval, Polygon4g (g + 1)) where
  toFun := fun t =>
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) t.val)
  continuous_toFun := by
    refine (Polygon4g.mk_continuous _).comp ?_
    refine (boundaryParam_continuous _ _).comp ?_
    exact continuous_subtype_val

@[simp] lemma edgeContMap_apply (g : ℕ) (i : Fin (2 * (g + 1))) (t : unitInterval) :
    edgeContMap g i t =
      Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) t.val) :=
  rfl

end JacobianChallenge.Periods
