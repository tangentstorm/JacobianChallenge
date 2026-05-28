import Jacobian.Periods.CellularChainComplex
import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse



/-!
# Project-side Hurewicz and cellular-to-singular bridge

This file names the comparison theorem missing from Mathlib v4.28.0:
cellular homology agrees with singular homology for the cellular model
of the fundamental polygon.  It is deliberately stated at the narrow
surface needed by the Jacobian project.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory CategoryTheory.Limits SimplexCategory Opposite
open Simplicial


def Polygon4gAbelianization (g : ℕ) : Type :=
  Fin (2 * (g + 1)) → ℤ

instance polygon4gAbelianization_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gAbelianization g) := by
  unfold Polygon4gAbelianization
  infer_instance

instance polygon4gAbelianization_module (g : ℕ) :
    Module ℤ (Polygon4gAbelianization g) := by
  unfold Polygon4gAbelianization
  infer_instance

instance polygon4gAbelianization_module_free (g : ℕ) :
    Module.Free ℤ (Polygon4gAbelianization g) := by
  unfold Polygon4gAbelianization
  infer_instance

instance polygon4gAbelianization_module_finite (g : ℕ) :
    Module.Finite ℤ (Polygon4gAbelianization g) := by
  unfold Polygon4gAbelianization
  infer_instance

/--
The singular datum attached to the unique zero-cell of the standard
polygonal cell structure.
-/
structure Polygon4gCellularSingularZeroCellData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  /-- The singular zero-simplex is the unique cellular vertex. -/
  vertex : Polygon4g g
  /-- It is the vertex recorded by the cellular model. -/
  vertex_eq_model : vertex = C.vertex

/-- **Comparison leaf 1a.** Construct the singular zero-cell datum. -/
theorem polygon4g_cellular_singular_zero_cell_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularZeroCellData g C) :=
  ⟨{ vertex := C.vertex, vertex_eq_model := rfl }⟩

/--
The singular edge-path data attached to the `2g` oriented one-cells
of the standard polygonal cell structure.
-/
structure Polygon4gCellularSingularOneCellData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  /-- The singular representatives of the oriented one-cells. -/
  edgePath : Fin (2 * g) → Path C.vertex C.vertex
  /-- They are the one-cell loops recorded by the cellular model. -/
  edgePath_eq_model : edgePath = C.oneCellPath

/--
**Comparison leaf 1b.** Construct the singular one-cell edge-path
data.
-/
theorem polygon4g_cellular_singular_one_cell_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularOneCellData g C) :=
  ⟨{ edgePath := C.oneCellPath, edgePath_eq_model := rfl }⟩

/-- The singular disk characteristic-map datum for the unique two-cell. -/
structure Polygon4gCellularSingularTwoCellCharacteristicData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  /-- The singular characteristic map of the two-cell. -/
  characteristic : ContinuousMap C.disk.diskSource.carrier (Polygon4g g)
  /-- It is the quotient map from the closed disk (via the homeomorph). -/
  characteristic_eq_mk :
    ∀ z, characteristic z = Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z)

/--
**Comparison leaf 1c(i).** Construct the singular characteristic
map data for the unique two-cell.
-/
theorem polygon4g_cellular_singular_two_cell_characteristic_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularTwoCellCharacteristicData g C) :=
  ⟨{
    characteristic := C.twoCellCharacteristic
    characteristic_eq_mk := C.twoCellCharacteristic_eq_mk
  }⟩

/--
The boundary parametrisation of the singular two-cell by the
standard surface word `∏ᵢ [aᵢ,bᵢ]`.
-/
structure Polygon4gCellularSingularTwoCellBoundaryWordData
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_characteristic : Polygon4gCellularSingularTwoCellCharacteristicData g C) where
  /-- The word read on the boundary of the characteristic disk. -/
  boundaryWord : EdgeWord g
  /-- It is the boundary word recorded by the cellular model. -/
  boundaryWord_eq_model : boundaryWord = C.boundaryWord
  /-- The boundary word is the standard product of commutators. -/
  boundaryWord_standard : boundaryWord.IsStandardForm
  /-- The boundary word induces the same quotient relation as `Polygon4g`. -/
  boundaryWord_sidePairing :
    EdgeWord.sidePairingRel g boundaryWord = Polygon4g.SideRel g
  /-- The boundary word has zero abelianised cellular boundary. -/
  boundaryWord_abelianizedBoundary :
    edgeWordAbelianizedBoundary boundaryWord = 0

/--
**Comparison leaf 1c(ii).** Construct the boundary-word
parametrisation for the singular two-cell.
-/
theorem polygon4g_cellular_singular_two_cell_boundary_word_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (characteristic : Polygon4gCellularSingularTwoCellCharacteristicData g C) :
    Nonempty (Polygon4gCellularSingularTwoCellBoundaryWordData g C characteristic) :=
  ⟨{
    boundaryWord := C.boundaryWord
    boundaryWord_eq_model := rfl
    boundaryWord_standard := h_boundary.2.1
    boundaryWord_sidePairing := h_boundary.2.2.1
    boundaryWord_abelianizedBoundary := h_boundary.2.2.2
  }⟩

/--
The singular two-cell datum: the quotient disk characteristic map
and its boundary parametrisation by the surface word.
-/
structure Polygon4gCellularSingularTwoCellData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  characteristic : Polygon4gCellularSingularTwoCellCharacteristicData g C
  boundaryWord : Polygon4gCellularSingularTwoCellBoundaryWordData g C characteristic

/--
**Comparison assembly 1c.** Construct the singular two-cell disk and
attaching-map data from characteristic-map and boundary-word leaves.
-/
theorem polygon4g_cellular_singular_two_cell_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularTwoCellData g C) :=
by
  obtain ⟨characteristic⟩ :=
    polygon4g_cellular_singular_two_cell_characteristic_data g C _h_boundary
  obtain ⟨boundaryWord⟩ :=
    polygon4g_cellular_singular_two_cell_boundary_word_data
      g C _h_boundary characteristic
  exact ⟨{ characteristic, boundaryWord }⟩

/--
The comparison data between the cellular chain complex of the
standard polygon model and singular chains on the quotient surface.

Bottom-up route: define the characteristic-map pushforward on cells,
or specialise the usual cellular filtration construction to the finite
CW complex with one zero-cell, `2g` one-cells, and one two-cell.
-/
structure Polygon4gCellularSingularComparisonData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  zeroCell : Polygon4gCellularSingularZeroCellData g C
  oneCells : Polygon4gCellularSingularOneCellData g C
  twoCell : Polygon4gCellularSingularTwoCellData g C

/--
**Comparison assembly 1.** Existence of the cellular-to-singular
comparison data for the standard polygonal cell structure, assembled
from the zero-cell, one-cell, and two-cell data leaves.
-/
theorem polygon4g_cellular_singular_comparison_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularComparisonData g C) :=
by
  obtain ⟨zeroCell⟩ := polygon4g_cellular_singular_zero_cell_data g C _h_boundary
  obtain ⟨oneCells⟩ := polygon4g_cellular_singular_one_cell_data g C _h_boundary
  obtain ⟨twoCell⟩ := polygon4g_cellular_singular_two_cell_data g C _h_boundary
  exact ⟨{ zeroCell, oneCells, twoCell }⟩

/--
The cellular zero-chain module for the standard polygon model:
free rank one on the unique vertex.
-/
abbrev Polygon4gCellularC0 (_g : ℕ) : Type :=
  Unit → ℤ

/--
The cellular two-chain module for the standard polygon model:
free rank one on the unique two-cell.
-/
abbrev Polygon4gCellularC2 (_g : ℕ) : Type :=
  Unit → ℤ

instance polygon4gCellularC0_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularC0 g) := by
  unfold Polygon4gCellularC0
  infer_instance

instance polygon4gCellularC0_module (g : ℕ) :
    Module ℤ (Polygon4gCellularC0 g) := by
  unfold Polygon4gCellularC0
  infer_instance

instance polygon4gCellularC2_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularC2 g) := by
  unfold Polygon4gCellularC2
  infer_instance

instance polygon4gCellularC2_module (g : ℕ) :
    Module ℤ (Polygon4gCellularC2 g) := by
  unfold Polygon4gCellularC2
  infer_instance

/-- The unique cellular zero-cell generator. -/
def polygon4gCellularC0Vertex {g : ℕ} : Polygon4gCellularC0 g :=
  fun _ => 1

/-- The unique cellular two-cell generator. -/
def polygon4gCellularC2Face {g : ℕ} : Polygon4gCellularC2 g :=
  fun _ => 1

/--
Project-side singular zero-chains on `Polygon4g g`: finitely
supported integral sums of points.
-/
abbrev Polygon4gSingularC0 (g : ℕ) : Type :=
  Polygon4g g →₀ ℤ

/--
Project-side singular one-chains for the polygon comparison, wrapped
around the coefficients of the recorded edge paths.  The wrapper prevents
the associated-graded comparison from reducing to a reflexive equivalence
between aliases.
-/
structure Polygon4gSingularC1
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_D : Polygon4gCellularSingularComparisonData g C) where
  coeff : Fin (2 * g) → ℤ

namespace Polygon4gSingularC1

variable {g : ℕ} {C : Polygon4gCellularModel g}
variable {D : Polygon4gCellularSingularComparisonData g C}

@[ext]
lemma ext {x y : Polygon4gSingularC1 g C D} (h : x.coeff = y.coeff) : x = y := by
  cases x
  cases y
  simp at h
  simp [h]

instance : Add (Polygon4gSingularC1 g C D) :=
  ⟨fun x y => ⟨x.coeff + y.coeff⟩⟩

instance : Zero (Polygon4gSingularC1 g C D) :=
  ⟨⟨0⟩⟩

instance : Neg (Polygon4gSingularC1 g C D) :=
  ⟨fun x => ⟨-x.coeff⟩⟩

instance : Sub (Polygon4gSingularC1 g C D) :=
  ⟨fun x y => ⟨x.coeff - y.coeff⟩⟩

instance : SMul ℤ (Polygon4gSingularC1 g C D) :=
  ⟨fun n x => ⟨n • x.coeff⟩⟩

instance : SMul ℕ (Polygon4gSingularC1 g C D) :=
  ⟨fun n x => ⟨n • x.coeff⟩⟩

instance : AddCommGroup (Polygon4gSingularC1 g C D) :=
  Function.Injective.addCommGroup coeff (fun _ _ h => ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℤ (Polygon4gSingularC1 g C D) :=
  Function.Injective.module ℤ ⟨⟨fun x => x.coeff, rfl⟩, fun _ _ => rfl⟩
    (fun _ _ h => ext h) (fun _ _ => rfl)

@[simp] lemma add_coeff (x y : Polygon4gSingularC1 g C D) (e : Fin (2 * g)) :
    (x + y).coeff e = x.coeff e + y.coeff e :=
  rfl

@[simp] lemma smul_coeff (n : ℤ) (x : Polygon4gSingularC1 g C D) (e : Fin (2 * g)) :
    (n • x).coeff e = n * x.coeff e :=
  rfl

/--
Realize the project-side singular one-chain wrapper as an actual
Mathlib singular 1-chain by summing the concrete polygon edge chains with
the recorded coefficients.
-/
noncomputable def toConcreteEdgeChain
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D →ₗ[ℤ]
      SingularChainCoproduct (Polygon4g g) 1 where
  toFun := fun c =>
    ∑ e : Fin (2 * g), c.coeff e • edgeChainOnGenus g e
  map_add' := by
    intro x y
    simp only [add_coeff]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [add_zsmul]
  map_smul' := by
    intro n x
    simp only [smul_coeff, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [mul_zsmul]
    exact (Int.cast_smul_eq_zsmul (R := ℤ) n
      (x.coeff e • edgeChainOnGenus g e)).symm

/--
The concrete edge-chain realization of a single project-side edge
generator is the corresponding singular edge chain.
-/
theorem toConcreteEdgeChain_single
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) (e : Fin (2 * g)) :
    toConcreteEdgeChain g C D ⟨Pi.single e 1⟩ = edgeChainOnGenus g e := by
  unfold toConcreteEdgeChain
  simp [Pi.single_apply]

/-- The singular chain complex of `Polygon4g g`. -/
noncomputable abbrev polygonChainComplexOnGenus (g : ℕ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g g))

/-- The singular chain complex of a space, with integral coefficients. -/
noncomputable abbrev singularChainComplexZ (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- The shape relation `(down ℕ).next 1 = 0` used by `cyclesMk`. -/
private lemma next_one_eq_zero_on_genus :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/--
The shape relation `(down ℕ).next 1 = 0` used by degree-one
singular-cycle representatives.
-/
private lemma next_one_eq_zero :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/--
Every singular `H₁` class has a singular one-cycle representative.

This is only homological algebra plumbing: `homologyπ` is an epimorphism
from cycles to homology in `ModuleCat`, hence surjective on underlying
modules, and `iCycles` identifies the chosen cycle object element with
an actual chain killed by `d₁`.
-/
theorem singularH1_exists_cycle_repr
    (X : Type) [TopologicalSpace X]
    (y : singularH1 X) :
    ∃ z : SingularChainCoproduct X 1,
    ∃ hz : (singularChainComplexZ X).d 1 0 z = 0,
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ X).homologyπ 1))
        ((singularChainComplexZ X).cyclesMk z 0 next_one_eq_zero hz) = y := by
  let K := singularChainComplexZ X
  have hπ_surj :
      Function.Surjective
        ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) := by
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ_surj y
  let z : SingularChainCoproduct X 1 :=
    ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) x
  have hz : K.d 1 0 z = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
        (((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) x) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, K.iCycles_d]
    simp
  refine ⟨z, hz, ?_⟩
  have hcycles :
      K.cyclesMk z 0 next_one_eq_zero hz = x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    simpa [K, z, singularChainComplexZ] using
      (K.i_cyclesMk z 0 next_one_eq_zero hz)
  simpa [K, hcycles] using hx

/--
The concrete realization of every project-side singular one-chain is
a Mathlib singular one-cycle, because it is a finite integral linear
combination of the concrete edge cycles.
-/
theorem toConcreteEdgeChain_isCycle
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C)
    (c : Polygon4gSingularC1 g C D) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g g))).d 1 0
        (toConcreteEdgeChain g C D c :
          SingularChainCoproduct (Polygon4g g) 1) = 0 := by
  unfold toConcreteEdgeChain
  change (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g g))).d 1 0
      (∑ e : Fin (2 * g), c.coeff e • edgeChainOnGenus g e :
        SingularChainCoproduct (Polygon4g g) 1) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [map_zsmul, edgeChainOnGenus_isCycle]
  exact zsmul_zero (c.coeff e)

/--
Project-side singular edge chains determine actual Mathlib
singular `H₁` by taking their concrete singular-chain realization,
proving it is a cycle, and applying `homologyπ`.
-/
noncomputable def toSingularH1Class
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D → singularH1 (Polygon4g g) :=
  fun c =>
    ((forget₂ (ModuleCat ℤ) Ab).map ((polygonChainComplexOnGenus g).homologyπ 1))
      ((polygonChainComplexOnGenus g).cyclesMk
        (toConcreteEdgeChain g C D c) 0 next_one_eq_zero_on_genus
        (by simpa [polygonChainComplexOnGenus] using toConcreteEdgeChain_isCycle g C D c))

/--
On a single project-side edge generator, the canonical map to
Mathlib `H₁` is represented by the corresponding concrete edge chain.
-/
theorem toSingularH1_single
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) (e : Fin (2 * g)) :
    toSingularH1Class g C D ⟨Pi.single e 1⟩ =
      ((forget₂ (ModuleCat ℤ) Ab).map ((polygonChainComplexOnGenus g).homologyπ 1))
        ((polygonChainComplexOnGenus g).cyclesMk
          (edgeChainOnGenus g e) 0 next_one_eq_zero_on_genus
          (by simpa [polygonChainComplexOnGenus] using edgeChainOnGenus_isCycle g e)) := by
  simp [toSingularH1Class, toConcreteEdgeChain_single]

/--
Linearized version of `toSingularH1Class`: a project-side singular
one-chain is sent to the finite integral linear combination of the
actual singular `H₁` classes of its edge generators.
-/
noncomputable def coeffLinearMap
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D →ₗ[ℤ] (Fin (2 * g) → ℤ) where
  toFun := fun c => c.coeff
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro n x
    rfl

/--
Linearized version of `toSingularH1Class`: a project-side singular
one-chain is sent to the finite integral linear combination of the
actual singular `H₁` classes of its edge generators.
-/
noncomputable def toSingularH1LinearMap
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D →ₗ[ℤ] singularH1 (Polygon4g g) :=
  (∑ e : Fin (2 * g),
      (LinearMap.toSpanSingleton ℤ _
        (toSingularH1Class g C D ⟨Pi.single e 1⟩)).comp
        (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (2 * g) => ℤ) e)).comp
    (coeffLinearMap g C D)

end Polygon4gSingularC1

/-- The singular chain complex of a space, with integral coefficients. -/
noncomputable abbrev singularChainComplexZ (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  Polygon4gSingularC1.singularChainComplexZ X

/-- Every singular `H₁` class has a singular one-cycle representative. -/
theorem singularH1_exists_cycle_repr
    (X : Type) [TopologicalSpace X]
    (y : singularH1 X) :
    ∃ z : SingularChainCoproduct X 1,
    ∃ hz : (singularChainComplexZ X).d 1 0 z = 0,
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ X).homologyπ 1))
        ((singularChainComplexZ X).cyclesMk z 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz) = y :=
  Polygon4gSingularC1.singularH1_exists_cycle_repr X y

/-- The homology class of a specified singular one-cycle. -/
noncomputable def singularH1ClassOfCycle
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0) :
    singularH1 X :=
  ((forget₂ (ModuleCat ℤ) Ab).map
    ((singularChainComplexZ X).homologyπ 1))
    ((singularChainComplexZ X).cyclesMk z 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)

/--
Two singular one-cycles represent the same `H₁` class when their
difference is the boundary of an explicit singular two-chain.
-/
theorem singularH1ClassOfCycle_eq_of_boundary
    {X : Type} [TopologicalSpace X]
    {z z' : SingularChainCoproduct X 1}
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hz' : (singularChainComplexZ X).d 1 0 z' = 0)
    (B : SingularChainCoproduct X 2)
    (hB : (singularChainComplexZ X).d 2 1 B = z - z') :
    singularH1ClassOfCycle X z hz =
      singularH1ClassOfCycle X z' hz' := by
  let K := singularChainComplexZ X
  let cz :=
    K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz
  let cz' :=
    K.cyclesMk z' 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz'
  have hcycles :
      cz - cz' = ((forget₂ (ModuleCat ℤ) Ab).map (K.toCycles 2 1)) B := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    change
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) (cz - cz') =
        ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
          (((forget₂ (ModuleCat ℤ) Ab).map (K.toCycles 2 1)) B)
    rw [map_sub]
    rw [K.i_cyclesMk, K.i_cyclesMk]
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_i]
    exact hB.symm
  unfold singularH1ClassOfCycle
  change ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) cz =
    ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) cz'
  have hzero :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) (cz - cz') = 0 := by
    rw [hcycles]
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/--
The homology class of the sum of two singular one-cycles is the sum
of their homology classes.
-/
theorem singularH1ClassOfCycle_add
    {X : Type} [TopologicalSpace X]
    (z z' : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hz' : (singularChainComplexZ X).d 1 0 z' = 0)
    (hadd : (singularChainComplexZ X).d 1 0 (z + z') = 0) :
    singularH1ClassOfCycle X (z + z') hadd =
      singularH1ClassOfCycle X z hz + singularH1ClassOfCycle X z' hz' := by
  let K := singularChainComplexZ X
  unfold singularH1ClassOfCycle
  have hcycles :
      K.cyclesMk (z + z') 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hadd =
        K.cyclesMk z 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz +
          K.cyclesMk z' 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz' := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    change
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk (z + z') 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hadd) =
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk z 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz +
        K.cyclesMk z' 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz')
    rw [map_add, K.i_cyclesMk, K.i_cyclesMk, K.i_cyclesMk]
  rw [hcycles, map_add]

/-- The quotient map `DiskC → Polygon4g g` as a continuous map. -/
noncomputable def polygon4gMkContinuousMap (g : ℕ) :
    C(DiskC, Polygon4g g) :=
  ⟨Polygon4g.mk g, Polygon4g.mk_continuous g⟩

/--
Functoriality of the exposed singular-chain basis element: the
singular chain map induced by a continuous map sends a generator to the
generator of the composed singular simplex.
-/
theorem singularChainElement_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f n)
        (singularChainElement σ) =
      singularChainElement (f.comp σ) := by
  rw [show singularChainElement σ =
      (singChain_basis σ).hom (1 : ℤ) by rfl]
  rw [show singularChainElement (f.comp σ) =
      (singChain_basis (f.comp σ)).hom (1 : ℤ) by rfl]
  have h := singChain_map_basis f n σ
  have hh := congrArg ModuleCat.Hom.hom h
  exact congrArg (fun F => F (1 : ℤ)) hh

/--
Naturality of `singularH1ClassOfCycle` for the project-level
`singularH1_inducedLinearMap`, stated at the exposed chain level.
-/
theorem singularH1_inducedLinearMap_classOfCycle
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hmapz :
      (singularChainComplexZ Y).d 1 0
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 1) z) = 0) :
    singularH1_inducedLinearMap f (singularH1ClassOfCycle X z hz) =
      singularH1ClassOfCycle Y
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 1) z) hmapz := by
  let KX := singularChainComplexZ X
  let KY := singularChainComplexZ Y
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
  change
    ((forget₂ (ModuleCat ℤ) Ab).map (HomologicalComplex.homologyMap F 1))
      (((forget₂ (ModuleCat ℤ) Ab).map (KX.homologyπ 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.homologyπ 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.homologyπ_naturality]
  rw [ConcreteCategory.forget₂_comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (KY.iCycles 1)).1 inferInstance
  change
    ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
      (((forget₂ (ModuleCat ℤ) Ab).map (HomologicalComplex.cyclesMap F 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.forget₂_comp_apply]
  change
    ModuleCat.Hom.hom (F.f 1)
      (((forget₂ (ModuleCat ℤ) Ab).map (KX.iCycles 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [KX.i_cyclesMk, KY.i_cyclesMk]

/-- Constant singular zero-simplex at a point. -/
noncomputable def pointSingularSimplex
    (X : Type) [TopologicalSpace X] (x : X) :
    C(stdSimplex ℝ (Fin 1), X) :=
  ⟨fun _ => x, continuous_const⟩

/-- Singular zero-chain represented by a point. -/
noncomputable def pointChain
    (X : Type) [TopologicalSpace X] (x : X) :
    SingularChainCoproduct X 0 :=
  singularChainElement (pointSingularSimplex X x)

lemma singularSimplexFace_path_zero
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    singularSimplexFace (γ.comp stdSimplexToUnitInterval) 0 =
      pointSingularSimplex X (γ 1) := by
  ext s
  haveI : Subsingleton (stdSimplex ℝ (Fin 1)) := inferInstance
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) := this
  have hs : s = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  rw [hs]
  simp [singularSimplexFace, stdSimplexFaceMap, pointSingularSimplex,
    stdSimplexToUnitInterval]

lemma singularSimplexFace_path_one
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    singularSimplexFace (γ.comp stdSimplexToUnitInterval) 1 =
      pointSingularSimplex X (γ 0) := by
  ext s
  haveI : Subsingleton (stdSimplex ℝ (Fin 1)) := inferInstance
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) := this
  have hs : s = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  rw [hs]
  simp [singularSimplexFace, stdSimplexFaceMap, pointSingularSimplex,
    stdSimplexToUnitInterval]

/-- Boundary of a path-shaped singular one-simplex. -/
theorem singularChainElement_boundary_path
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    (singularChainComplexZ X).d 1 0
        (singularChainElement (γ.comp stdSimplexToUnitInterval) :
          SingularChainCoproduct X 1) =
      pointChain X (γ 1) - pointChain X (γ 0) := by
  rw [singularChainElement_boundary_decomposition X 0
        (γ.comp stdSimplexToUnitInterval)]
  rw [Fin.sum_univ_two]
  rw [singularSimplexFace_path_zero X γ, singularSimplexFace_path_one X γ]
  simp [pointChain, pow_zero, pow_one, one_smul, sub_eq_add_neg]

/--
The inverse parametrisation from the unit interval to the standard
one-simplex.
-/
noncomputable def unitIntervalToStdSimplex :
    C(unitInterval, stdSimplex ℝ (Fin 2)) :=
  ⟨stdSimplexHomeomorphUnitInterval.symm,
    stdSimplexHomeomorphUnitInterval.symm.continuous⟩

@[simp] lemma unitIntervalToStdSimplex_zero :
    unitIntervalToStdSimplex (0 : unitInterval) = stdSimplexVertex 0 := by
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [unitIntervalToStdSimplex]

@[simp] lemma unitIntervalToStdSimplex_one :
    unitIntervalToStdSimplex (1 : unitInterval) = stdSimplexVertex 1 := by
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [unitIntervalToStdSimplex]

lemma singularOneSimplex_asPath_comp
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    (σ.comp unitIntervalToStdSimplex).comp stdSimplexToUnitInterval = σ := by
  ext s
  simp [unitIntervalToStdSimplex, stdSimplexToUnitInterval]

/--
Boundary of an arbitrary singular one-simplex, expressed by its two
standard vertices.
-/
theorem singularChainElement_boundary_one_simplex
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    (singularChainComplexZ X).d 1 0
        (singularChainElement σ : SingularChainCoproduct X 1) =
      pointChain X (σ (stdSimplexVertex 1)) -
        pointChain X (σ (stdSimplexVertex 0)) := by
  rw [← singularOneSimplex_asPath_comp X σ]
  rw [singularChainElement_boundary_path X (σ.comp unitIntervalToStdSimplex)]
  simp [unitIntervalToStdSimplex, stdSimplexToUnitInterval]

/-- Chain-map image of a point zero-chain. -/
theorem pointChain_map
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0)
      (pointChain X x) =
        pointChain Y (f x) := by
  simpa [pointChain, pointSingularSimplex] using
    singularChainElement_map f 0 (pointSingularSimplex X x)

/-- Orientation for a primitive boundary-edge repair step. -/
inductive BoundaryArcOrientation where
  | forward
  | reverse
  deriving DecidableEq

namespace BoundaryArcOrientation

/-- The integral sign represented by an oriented boundary edge. -/
def sign : BoundaryArcOrientation → ℤ
  | forward => 1
  | reverse => -1

/-- Reverse an oriented boundary edge. -/
def flip : BoundaryArcOrientation → BoundaryArcOrientation
  | forward => reverse
  | reverse => forward

lemma sign_eq (o : BoundaryArcOrientation) : sign o = 1 ∨ sign o = -1 := by
  cases o <;> simp [sign]

lemma sign_flip (o : BoundaryArcOrientation) :
    sign (flip o) = - sign o := by
  cases o <;> simp [sign, flip]

end BoundaryArcOrientation

/-- Reversal of the unit interval. -/
noncomputable def unitIntervalReverse : C(unitInterval, unitInterval) where
  toFun := fun t =>
    ⟨1 - t.1, by
      exact ⟨sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_const.sub continuous_subtype_val) _

@[simp] lemma unitIntervalReverse_zero :
    unitIntervalReverse 0 = (1 : unitInterval) := by
  ext
  norm_num [unitIntervalReverse]

@[simp] lemma unitIntervalReverse_one :
    unitIntervalReverse 1 = (0 : unitInterval) := by
  ext
  norm_num [unitIntervalReverse]

/--
The parameter along a partial oriented boundary arc.  The
`startParam` and `endParam` fields are closed-interval points, so this
can represent arbitrary side-interior endpoints, not only full side
endpoints.
-/
noncomputable def boundaryArcOrientedAffineParam
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) : ℝ :=
  match orientation with
  | BoundaryArcOrientation.forward =>
      (1 - t.1) * startParam.1 + t.1 * endParam.1
  | BoundaryArcOrientation.reverse =>
      (1 - t.1) * endParam.1 + t.1 * startParam.1

lemma boundaryArcOrientedAffineParam_flip_reverse
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) :
    boundaryArcOrientedAffineParam (BoundaryArcOrientation.flip orientation)
        startParam endParam t =
      boundaryArcOrientedAffineParam orientation startParam endParam
        (unitIntervalReverse t) := by
  cases orientation <;>
    simp [boundaryArcOrientedAffineParam, BoundaryArcOrientation.flip,
      unitIntervalReverse]
  · ring_nf
  · ring_nf

lemma boundaryArcOrientedAffineParam_swap_reverse
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) :
    boundaryArcOrientedAffineParam orientation endParam startParam t =
      boundaryArcOrientedAffineParam orientation startParam endParam
        (unitIntervalReverse t) := by
  cases orientation <;>
    simp [boundaryArcOrientedAffineParam, unitIntervalReverse]
  · ring_nf
  · ring_nf

/--
A boundary-arc path in the closed disk, with orientation and a
concrete boundary parametrisation witness.  The side arc may be only a
partial boundary side, and `arcIndex` may be either the canonical
edge-basis side or its paired opposite side.
-/
structure Polygon4gBoundaryArcStep (g : ℕ) where
  source : DiskC
  target : DiskC
  edgeIndex : Fin (2 * (g + 1))
  arcIndex : ℕ
  arcIndex_represents_edge :
    arcIndex = edgeArcIdx g edgeIndex ∨
      arcIndex = edgeArcIdx g edgeIndex + 2
  orientation : BoundaryArcOrientation
  startParam : Set.Icc (0 : ℝ) 1
  endParam : Set.Icc (0 : ℝ) 1
  path : C(unitInterval, DiskC)
  source_eq : path 0 = source
  target_eq : path 1 = target
  path_param :
    ∀ t : unitInterval,
      path t = boundaryParam (g + 1) arcIndex
        (boundaryArcOrientedAffineParam orientation startParam endParam t)

/--
Reverse a boundary-arc step, swapping endpoints and interval
parameters.  The stored edge orientation is left unchanged: the path
itself is reversed, so the signed singular chain has the negated
boundary needed by endpoint repair symmetry.
-/
noncomputable def Polygon4gBoundaryArcStep.reverse
    {g : ℕ} (step : Polygon4gBoundaryArcStep g) :
    Polygon4gBoundaryArcStep g where
  source := step.target
  target := step.source
  edgeIndex := step.edgeIndex
  arcIndex := step.arcIndex
  arcIndex_represents_edge := step.arcIndex_represents_edge
  orientation := step.orientation
  startParam := step.endParam
  endParam := step.startParam
  path := step.path.comp unitIntervalReverse
  source_eq := by
    simp [ContinuousMap.comp_apply, step.target_eq]
  target_eq := by
    simp [ContinuousMap.comp_apply, step.source_eq]
  path_param := by
    intro t
    rw [ContinuousMap.comp_apply, step.path_param]
    exact congrArg (boundaryParam (g + 1) step.arcIndex)
      (boundaryArcOrientedAffineParam_swap_reverse
        step.orientation step.startParam step.endParam t).symm

/-- A finite list of boundary arcs connects two disk endpoints. -/
inductive Polygon4gBoundaryArcListConnects (g : ℕ) :
    DiskC → DiskC → List (Polygon4gBoundaryArcStep g) → Prop
  | nil (p : DiskC) : Polygon4gBoundaryArcListConnects g p p []
  | cons {p q r : DiskC} {step : Polygon4gBoundaryArcStep g}
      {steps : List (Polygon4gBoundaryArcStep g)}
      (hsource : step.source = p)
      (htarget : step.target = q)
      (hrest : Polygon4gBoundaryArcListConnects g q r steps) :
      Polygon4gBoundaryArcListConnects g p r (step :: steps)

/--
Concatenating two connected boundary-arc lists gives a connected
boundary-arc list.
-/
theorem Polygon4gBoundaryArcListConnects.append
    {g : ℕ} {p q r : DiskC}
    {steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)}
    (h₁ : Polygon4gBoundaryArcListConnects g p q steps₁)
    (h₂ : Polygon4gBoundaryArcListConnects g q r steps₂) :
    Polygon4gBoundaryArcListConnects g p r (steps₁ ++ steps₂) := by
  induction h₁ with
  | nil p =>
      simpa using h₂
  | cons hsource htarget hrest ih =>
      exact Polygon4gBoundaryArcListConnects.cons hsource htarget (ih h₂)

/--
Reverse a list of boundary-arc steps in the order needed for a
path reversal.
-/
noncomputable def polygon4gBoundaryArcStepsReverse
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    List (Polygon4gBoundaryArcStep g) :=
  steps.reverse.map Polygon4gBoundaryArcStep.reverse

/--
A connected boundary-arc list remains connected after reversing all
steps and their order.
-/
theorem Polygon4gBoundaryArcListConnects.reverse
    {g : ℕ} {p q : DiskC} {steps : List (Polygon4gBoundaryArcStep g)}
    (h : Polygon4gBoundaryArcListConnects g p q steps) :
    Polygon4gBoundaryArcListConnects g q p
      (polygon4gBoundaryArcStepsReverse steps) := by
  induction h with
  | nil p =>
      simp [polygon4gBoundaryArcStepsReverse,
        Polygon4gBoundaryArcListConnects.nil]
  | cons hsource htarget hrest ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append]
      refine Polygon4gBoundaryArcListConnects.append ih ?_
      exact Polygon4gBoundaryArcListConnects.cons htarget hsource
        (Polygon4gBoundaryArcListConnects.nil _)

/-- The projected singular one-chain of a disk boundary-arc step. -/
noncomputable def polygon4gBoundaryArcStepProjectedChain
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
  singularChainElement
    ((polygon4gMkContinuousMap (g + 1)).comp
      (step.path.comp stdSimplexToUnitInterval))

/--
The disk-side singular one-chain of a list of boundary-arc steps,
with the recorded orientations.
-/
noncomputable def polygon4gBoundaryArcStepsDiskChain
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    SingularChainCoproduct DiskC 1 :=
  (steps.map fun step =>
    step.orientation.sign • singularChainElement
      (step.path.comp stdSimplexToUnitInterval)).sum

/-- Disk-side chains of boundary-arc lists respect append. -/
theorem polygon4gBoundaryArcStepsDiskChain_append
    {g : ℕ} (steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)) :
    polygon4gBoundaryArcStepsDiskChain (steps₁ ++ steps₂) =
      polygon4gBoundaryArcStepsDiskChain steps₁ +
        polygon4gBoundaryArcStepsDiskChain steps₂ := by
  simp [polygon4gBoundaryArcStepsDiskChain, List.map_append]

/--
The projected singular chain of a list of boundary-arc steps, with
the recorded orientations.
-/
noncomputable def polygon4gBoundaryArcStepsProjectedChain
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
  (steps.map fun step =>
    step.orientation.sign • polygon4gBoundaryArcStepProjectedChain g step).sum

/-- Projected chains of boundary-arc lists respect append. -/
theorem polygon4gBoundaryArcStepsProjectedChain_append
    (g : ℕ) (steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)) :
    polygon4gBoundaryArcStepsProjectedChain g (steps₁ ++ steps₂) =
      polygon4gBoundaryArcStepsProjectedChain g steps₁ +
        polygon4gBoundaryArcStepsProjectedChain g steps₂ := by
  simp [polygon4gBoundaryArcStepsProjectedChain, List.map_append]

/--
The disk boundary of a reversed single boundary-arc generator is the
negative of the original disk boundary.
-/
theorem polygon4gBoundaryArcStep_reverse_disk_boundary
    {g : ℕ} (step : Polygon4gBoundaryArcStep g) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          [Polygon4gBoundaryArcStep.reverse step]) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain [step]) := by
  simp [polygon4gBoundaryArcStepsDiskChain, map_zsmul]
  rw [singularChainElement_boundary_path DiskC
    (Polygon4gBoundaryArcStep.reverse step).path]
  rw [singularChainElement_boundary_path DiskC step.path]
  simp [Polygon4gBoundaryArcStep.reverse, ContinuousMap.comp_apply,
    step.source_eq, step.target_eq]
  rcases BoundaryArcOrientation.sign_eq step.orientation with hsign | hsign
  · rw [hsign]
    simp
  · rw [hsign]
    simp

/--
The projected boundary of a reversed single boundary-arc generator
is the negative of the original projected boundary.
-/
theorem polygon4gBoundaryArcStep_reverse_projected_boundary
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          [Polygon4gBoundaryArcStep.reverse step]) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g [step]) := by
  simp [polygon4gBoundaryArcStepsProjectedChain,
    polygon4gBoundaryArcStepProjectedChain, map_zsmul]
  rw [show (polygon4gMkContinuousMap (g + 1)).comp
      ((Polygon4gBoundaryArcStep.reverse step).path.comp stdSimplexToUnitInterval) =
        ((polygon4gMkContinuousMap (g + 1)).comp
          (Polygon4gBoundaryArcStep.reverse step).path).comp
            stdSimplexToUnitInterval by
      rw [ContinuousMap.comp_assoc]]
  rw [show (polygon4gMkContinuousMap (g + 1)).comp
      (step.path.comp stdSimplexToUnitInterval) =
        ((polygon4gMkContinuousMap (g + 1)).comp step.path).comp
          stdSimplexToUnitInterval by
      rw [ContinuousMap.comp_assoc]]
  rw [singularChainElement_boundary_path (Polygon4g (g + 1))
    ((polygon4gMkContinuousMap (g + 1)).comp
      (Polygon4gBoundaryArcStep.reverse step).path)]
  rw [singularChainElement_boundary_path (Polygon4g (g + 1))
    ((polygon4gMkContinuousMap (g + 1)).comp step.path)]
  simp [Polygon4gBoundaryArcStep.reverse, ContinuousMap.comp_apply,
    step.source_eq, step.target_eq]
  rcases BoundaryArcOrientation.sign_eq step.orientation with hsign | hsign
  · rw [hsign]
    simp
  · rw [hsign]
    simp

/-- Reversing a boundary-arc list negates its disk-side boundary. -/
theorem polygon4gBoundaryArcStepsReverse_disk_boundary
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain steps) := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsDiskChain]
  | cons step steps ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsDiskChain_append, map_add]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [ih]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hstep := polygon4gBoundaryArcStep_reverse_disk_boundary step
      rw [hstep]
      have hcons :
          polygon4gBoundaryArcStepsDiskChain (step :: steps) =
            polygon4gBoundaryArcStepsDiskChain [step] +
              polygon4gBoundaryArcStepsDiskChain steps := by
        simp [polygon4gBoundaryArcStepsDiskChain]
      rw [hcons, map_add]
      abel

/-- Reversing a boundary-arc list negates its projected boundary. -/
theorem polygon4gBoundaryArcStepsReverse_projected_boundary
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g steps) := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsProjectedChain_append, map_add]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [ih]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hstep := polygon4gBoundaryArcStep_reverse_projected_boundary g step
      rw [hstep]
      have hcons :
          polygon4gBoundaryArcStepsProjectedChain g (step :: steps) =
            polygon4gBoundaryArcStepsProjectedChain g [step] +
              polygon4gBoundaryArcStepsProjectedChain g steps := by
        simp [polygon4gBoundaryArcStepsProjectedChain]
      rw [hcons, map_add]
      abel

/--
Remaining one-step local prism leaf: a projected boundary-arc
simplex and its reversed reparametrization bound a singular two-chain.
The list-level statement below is just finite additivity.
-/
theorem polygon4gBoundaryArcStep_reverse_projected_homotopy
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            [Polygon4gBoundaryArcStep.reverse step] +
          polygon4gBoundaryArcStepsProjectedChain g [step] := by
  -- Missing singular-prism computation for one projected path simplex
  -- and its reversed reparametrization.
  sorry

/--
Reversing a finite list of projected boundary-arc chains is
homologous to negation, by summing the one-step reverse prisms.
-/
theorem polygon4gBoundaryArcStepsReverse_projected_homotopy
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            (polygon4gBoundaryArcStepsReverse steps) +
          polygon4gBoundaryArcStepsProjectedChain g steps := by
  induction steps with
  | nil =>
      refine ⟨0, ?_⟩
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      obtain ⟨Bsteps, hBsteps⟩ := ih
      obtain ⟨Bstep, hBstep⟩ :=
        polygon4gBoundaryArcStep_reverse_projected_homotopy g step
      refine ⟨Bsteps + Bstep, ?_⟩
      rw [map_add, hBsteps, hBstep]
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsProjectedChain_append]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hcons :
          polygon4gBoundaryArcStepsProjectedChain g (step :: steps) =
            polygon4gBoundaryArcStepsProjectedChain g [step] +
              polygon4gBoundaryArcStepsProjectedChain g steps := by
        simp [polygon4gBoundaryArcStepsProjectedChain]
      rw [hcons]
      abel

/--
The list-level chain identities needed to reverse endpoint repair
data.  Boundary reversal is exact, while the comparison between a
singular one-simplex and its reversed reparametrization is supplied by
the standard prism homotopy.
-/
theorem polygon4gBoundaryArcStepsReverse_repair_identities
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain steps) ∧
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g steps) ∧
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            (polygon4gBoundaryArcStepsReverse steps) +
          polygon4gBoundaryArcStepsProjectedChain g steps := by
  exact ⟨polygon4gBoundaryArcStepsReverse_disk_boundary steps,
    polygon4gBoundaryArcStepsReverse_projected_boundary g steps,
    polygon4gBoundaryArcStepsReverse_projected_homotopy g steps⟩



structure SingularOneSimplexSubdivisionData
    (n : ℕ)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))) where
  n_pos : 0 < n
  first_endpoint :
    subSimplex ⟨0, n_pos⟩ (stdSimplexVertex 0) = stdSimplexVertex 0
  last_endpoint :
    subSimplex ⟨n - 1, Nat.sub_lt n_pos zero_lt_one⟩
        (stdSimplexVertex 1) =
      stdSimplexVertex 1
  adjacent_endpoints :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      subSimplex i (stdSimplexVertex 1) =
        subSimplex j (stdSimplexVertex 0)

/--
Finite local lifting data for a singular one-simplex in the polygon
quotient.  This records an actual finite subdivision by sub-simplices:
each piece has a disk lift, adjacent lifted endpoints are related by
`SideRel`, and the subdivided projected chain is homologous to the
original simplex chain.
-/
structure Polygon4gSingularSimplexDiskLiftData
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) where
  n : ℕ
  n_pos : 0 < n
  subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))
  subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex
  lift : Fin n → C(stdSimplex ℝ (Fin 2), DiskC)
  projects_on_piece :
    ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      Polygon4g.mk (g + 1) (lift i s) = σ (subSimplex i s)
  adjacent_endpoint_rel :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      Polygon4g.SideRel (g + 1)
        (lift i (stdSimplexVertex 1))
        (lift j (stdSimplexVertex 0))
  subdividedChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  subdividedChain_eq :
    subdividedChain =
      ∑ i : Fin n,
        singularChainElement ((polygon4gMkContinuousMap (g + 1)).comp (lift i))
  subdivisionBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  subdivision_homology :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 subdivisionBoundary =
      subdividedChain - singularChainElement σ

/--
Finite local-lift data for a polygon quotient path, before the
pure singular-chain subdivision homology is attached.  This is the
topological part of `polygon4g_singularSimplex_subdivision_lifts_to_disk`:
subdivide the interval into finitely many pieces admitting disk lifts,
and record that adjacent lifted endpoints differ by the polygon side
relation.
-/
structure Polygon4gQuotientPathFiniteLiftSubdivision
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) where
  n : ℕ
  n_pos : 0 < n
  subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))
  subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex
  lift : Fin n → C(stdSimplex ℝ (Fin 2), DiskC)
  projects_on_piece :
    ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      Polygon4g.mk (g + 1) (lift i s) = σ (subSimplex i s)
  adjacent_endpoint_rel :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      Polygon4g.SideRel (g + 1)
        (lift i (stdSimplexVertex 1))
        (lift j (stdSimplexVertex 0))

/--
Local topology leaf: every polygon quotient singular one-simplex has
a finite subdivision by pieces that lift to the closed disk, with
adjacent lifted endpoints related by `SideRel`.
-/
theorem polygon4g_quotient_path_finite_lift_subdivision
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) :
    Nonempty (Polygon4gQuotientPathFiniteLiftSubdivision g σ) := by
  -- Missing topology: compactness of the interval plus quotient charts
  -- admitting local disk lifts.
  sorry

/--
Singular-chain subdivision prism leaf for one-simplices in canonical
restricted-piece form.  The finite family of maps is exactly
`σ ∘ subSimplex i`; the wrapper below handles propositionally equal
families.
-/
theorem singular_one_simplex_subdivision_prism_homologous
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X))
    (n : ℕ) (_n_pos : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (_subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex) :
    ∃ subdivisionBoundary : SingularChainCoproduct X 2,
      (singularChainComplexZ X).d 2 1 subdivisionBoundary =
        (∑ i : Fin n,
          singularChainElement (σ.comp (subSimplex i))) -
            singularChainElement σ := by
  -- Missing singular-chain prism construction for a valid ordered
  -- subdivision of one simplex.
  sorry

/--
Singular-chain subdivision algebra for one-simplices.  Given the
projected pieces of a finite subdivision, their sum is homologous to
the original singular simplex by an explicit singular two-chain.
-/
theorem singular_one_simplex_subdivision_homologous
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X))
    (n : ℕ) (_n_pos : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (_subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex)
    (τ : Fin n → C(stdSimplex ℝ (Fin 2), X))
    (_hτ : ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      τ i s = σ (subSimplex i s)) :
    ∃ subdivisionBoundary : SingularChainCoproduct X 2,
      (singularChainComplexZ X).d 2 1 subdivisionBoundary =
        (∑ i : Fin n, singularChainElement (τ i)) - singularChainElement σ := by
  obtain ⟨subdivisionBoundary, hsubdivision⟩ :=
    singular_one_simplex_subdivision_prism_homologous
      X σ n _n_pos subSimplex _subdivision_valid
  refine ⟨subdivisionBoundary, ?_⟩
  rw [hsubdivision]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  congr 1
  ext s
  exact (_hτ i s).symm

/--
A singular one-simplex in the quotient polygon admits a finite disk
lifting package.  This is the subdivision/lifting leaf of the polygon
spanning proof.
-/
theorem polygon4g_singularSimplex_subdivision_lifts_to_disk
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) :
    Nonempty (Polygon4gSingularSimplexDiskLiftData g σ) := by
  obtain ⟨lifted⟩ := polygon4g_quotient_path_finite_lift_subdivision g σ
  let projectedPiece : Fin lifted.n →
      C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1)) :=
    fun i => (polygon4gMkContinuousMap (g + 1)).comp (lifted.lift i)
  have hpiece :
      ∀ (i : Fin lifted.n) (s : stdSimplex ℝ (Fin 2)),
        projectedPiece i s = σ (lifted.subSimplex i s) := by
    intro i s
    exact lifted.projects_on_piece i s
  obtain ⟨subdivisionBoundary, hsubdivision⟩ :=
    singular_one_simplex_subdivision_homologous
      (Polygon4g (g + 1)) σ lifted.n lifted.n_pos
      lifted.subSimplex lifted.subdivision_valid projectedPiece hpiece
  refine ⟨{
    n := lifted.n
    n_pos := lifted.n_pos
    subSimplex := lifted.subSimplex
    subdivision_valid := lifted.subdivision_valid
    lift := lifted.lift
    projects_on_piece := lifted.projects_on_piece
    adjacent_endpoint_rel := lifted.adjacent_endpoint_rel
    subdividedChain :=
      ∑ i : Fin lifted.n,
        singularChainElement
          ((polygon4gMkContinuousMap (g + 1)).comp (lifted.lift i))
    subdividedChain_eq := rfl
    subdivisionBoundary := subdivisionBoundary
    subdivision_homology := ?_
  }⟩
  simpa [projectedPiece] using hsubdivision

/--
Endpoint repair data for two disk points identified in the polygon
quotient by `SideRel`.  The repair is a disk-side chain built from
partial boundary-side arcs.  Its projection is required to be homologous
to an edge-chain combination by an explicit singular 2-boundary, not
definitionally equal to full edge chains.
-/
structure Polygon4gEndpointRepairData
    (g : ℕ) (p q : DiskC)
    (_hrel : Polygon4g.SideRel (g + 1) p q) where
  coeff : Polygon4gAbelianization g
  diskRepairChain : SingularChainCoproduct DiskC 1
  projectedRepairChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  edgeChainBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  steps : List (Polygon4gBoundaryArcStep g)
  steps_connect : Polygon4gBoundaryArcListConnects g p q steps
  diskRepairChain_eq :
    diskRepairChain =
      (steps.map fun step =>
        step.orientation.sign • singularChainElement
          (step.path.comp stdSimplexToUnitInterval)).sum
  projectedRepairChain_eq :
    projectedRepairChain = polygon4gBoundaryArcStepsProjectedChain g steps
  diskRepairBoundary :
    (singularChainComplexZ DiskC).d 1 0 diskRepairChain =
      pointChain DiskC q - pointChain DiskC p
  projectedRepairBoundary :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        projectedRepairChain =
      pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) q) -
        pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) p)
  projectedRepair_homologous_edge :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 edgeChainBoundary =
      projectedRepairChain -
        ∑ e : Fin (2 * (g + 1)), coeff e • edgeChain g e

/--
The projected chain of one boundary-arc step is the singular-chain
pushforward of its disk chain along the polygon quotient map.
-/
theorem polygon4gBoundaryArcStep_projected_eq_chainMap
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      (singularChainElement (step.path.comp stdSimplexToUnitInterval)) =
      polygon4gBoundaryArcStepProjectedChain g step := by
  exact singularChainElement_map (polygon4gMkContinuousMap (g + 1)) 1
    (step.path.comp stdSimplexToUnitInterval)

/--
The projected chain of a list of boundary-arc steps is the
singular-chain pushforward of the corresponding disk-side step chain.
-/
theorem polygon4gBoundaryArcSteps_projected_eq_chainMap
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      ((steps.map fun step =>
        step.orientation.sign • singularChainElement
          (step.path.comp stdSimplexToUnitInterval)).sum) =
      polygon4gBoundaryArcStepsProjectedChain g steps := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      simp [polygon4gBoundaryArcStepsProjectedChain, ih,
        polygon4gBoundaryArcStep_projected_eq_chainMap]

/--
The projected repair chain stored in endpoint-repair data is the
singular-chain pushforward of the disk repair chain.
-/
theorem polygon4gEndpointRepair_projected_eq_chainMap
    (g : ℕ) (p q : DiskC)
    (hrel : Polygon4g.SideRel (g + 1) p q)
    (repair : Polygon4gEndpointRepairData g p q hrel) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      repair.diskRepairChain =
      repair.projectedRepairChain := by
  rw [repair.diskRepairChain_eq, repair.projectedRepairChain_eq]
  exact polygon4gBoundaryArcSteps_projected_eq_chainMap g repair.steps

/--
Reflexive endpoint repair: no boundary arcs, no edge coefficients,
and no two-chain are needed.
-/
theorem polygon4g_endpoint_pair_repaired_refl
    (g : ℕ) (p : DiskC) :
    Nonempty (Polygon4gEndpointRepairData g p p (Relation.EqvGen.refl p)) := by
  refine ⟨{
    coeff := 0
    diskRepairChain := 0
    projectedRepairChain := 0
    edgeChainBoundary := 0
    steps := []
    steps_connect := Polygon4gBoundaryArcListConnects.nil p
    diskRepairChain_eq := ?_
    projectedRepairChain_eq := ?_
    diskRepairBoundary := ?_
    projectedRepairBoundary := ?_
    projectedRepair_homologous_edge := ?_
  }⟩
  · simp
  · simp [polygon4gBoundaryArcStepsProjectedChain]
  · simp
  · simp
  · rw [map_zero]
    have hsum :
        (∑ e : Fin (2 * (g + 1)),
          ((0 : Polygon4gAbelianization g) e) • edgeChain g e :
            SingularChainCoproduct (Polygon4g (g + 1)) 1) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro e _he
      change (0 : ℤ) • edgeChain g e = 0
      exact zero_zsmul (edgeChain g e)
    rw [hsum, sub_zero]

/-- Edge-basis index corresponding to the `aᵢ` side pair. -/
def polygon4g_aPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    Fin (2 * (g + 1)) :=
  ⟨2 * i.val, by omega⟩

/-- Edge-basis index corresponding to the `bᵢ` side pair. -/
def polygon4g_bPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    Fin (2 * (g + 1)) :=
  ⟨2 * i.val + 1, by omega⟩

lemma edgeArcIdx_aPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    edgeArcIdx g (polygon4g_aPair_edgeIndex g i) = 4 * i.val := by
  unfold edgeArcIdx polygon4g_aPair_edgeIndex
  rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
  simp

lemma edgeArcIdx_bPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    edgeArcIdx g (polygon4g_bPair_edgeIndex g i) = 4 * i.val + 1 := by
  unfold edgeArcIdx polygon4g_bPair_edgeIndex
  have hdiv : (2 * i.val + 1) / 2 = i.val := by
    rw [show 2 * i.val + 1 = 1 + 2 * i.val by omega]
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    simp
  have hmod : (2 * i.val + 1) % 2 = 1 := by
    rw [show 2 * i.val + 1 = 1 + 2 * i.val by omega]
    rw [Nat.add_mul_mod_self_left]
  rw [hdiv, hmod]

/--
Local primitive side-strip repair.  This is the single geometric
leaf behind the `aᵢ` and `bᵢ` generator repairs: for one canonical
edge basis arc and its opposite paired side, build the finite boundary
arc repair and the side-strip two-chain relating its projection to the
edge generator.
-/
theorem polygon4g_partial_side_arc_homologous_to_edge_chain
    (g : ℕ) (e : Fin (2 * (g + 1))) (sideArc : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hside : edgeArcIdx g e = sideArc)
    (hrel : Polygon4g.SideRel (g + 1)
      (boundaryParam (g + 1) sideArc t)
      (boundaryParam (g + 1) (sideArc + 2) (1 - t))) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) sideArc t)
      (boundaryParam (g + 1) (sideArc + 2) (1 - t))
      hrel) := by
  -- Missing primitive side-strip geometry: build the partial boundary
  -- arc chain from `sideArc` through the adjacent edge to `sideArc + 2`,
  -- then construct the projected side-strip two-chain homologous to
  -- `edgeChain g e`.  This lemma is local to one edge and interval
  -- parameter; it contains no arbitrary cycles or Hurewicz spanning data.
  sorry

/-- Primitive endpoint repair for one `aᵢ` side-pairing generator. -/
theorem polygon4g_endpoint_pair_repaired_by_aPair
    (g : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) (4 * i.val) t)
      (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val) t)
        (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
        (Polygon4g.SideGen.a_pair i t ht))) := by
  simpa [edgeArcIdx_aPair_edgeIndex] using
    polygon4g_partial_side_arc_homologous_to_edge_chain
      g (polygon4g_aPair_edgeIndex g i) (4 * i.val) t ht
      (edgeArcIdx_aPair_edgeIndex g i)
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val) t)
        (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
        (Polygon4g.SideGen.a_pair i t ht))

/-- Primitive endpoint repair for one `bᵢ` side-pairing generator. -/
theorem polygon4g_endpoint_pair_repaired_by_bPair
    (g : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) (4 * i.val + 1) t)
      (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val + 1) t)
        (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
        (Polygon4g.SideGen.b_pair i t ht))) := by
  simpa [edgeArcIdx_bPair_edgeIndex] using
    polygon4g_partial_side_arc_homologous_to_edge_chain
      g (polygon4g_bPair_edgeIndex g i) (4 * i.val + 1) t ht
      (edgeArcIdx_bPair_edgeIndex g i)
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val + 1) t)
        (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
        (Polygon4g.SideGen.b_pair i t ht))

/--
Primitive endpoint repair for one side-pairing generator, assembled
from the two explicit `aᵢ` and `bᵢ` generator cases.
-/
theorem polygon4g_endpoint_pair_repaired_by_sideGen
    (g : ℕ) (p q : DiskC)
    (hgen : Polygon4g.SideGen (g + 1) p q) :
    Nonempty (Polygon4gEndpointRepairData g p q
      (Relation.EqvGen.rel p q hgen)) := by
  cases hgen with
  | a_pair i t ht =>
      exact polygon4g_endpoint_pair_repaired_by_aPair g i t ht
  | b_pair i t ht =>
      exact polygon4g_endpoint_pair_repaired_by_bPair g i t ht

/--
Reversal of endpoint repair data.  The reversed boundary-arc list is
constructed above, but ordinary singular chains also need the prism
homotopy comparing a simplex with its reversed reparametrization; that
local chain-homotopy computation is kept as the remaining symmetry leaf.
-/
theorem polygon4g_endpoint_pair_repaired_symm
    (g : ℕ) (p q : DiskC)
    (hrel : Polygon4g.SideRel (g + 1) p q)
    (repair : Polygon4gEndpointRepairData g p q hrel) :
    Nonempty (Polygon4gEndpointRepairData g q p
      (Relation.EqvGen.symm p q hrel)) := by
  obtain ⟨hdiskBoundary, hprojectedBoundary,
    ⟨projectedReverseHomotopy, hprojectedReverseHomotopy⟩⟩ :=
    polygon4gBoundaryArcStepsReverse_repair_identities g repair.steps
  refine ⟨{
    coeff := - repair.coeff
    diskRepairChain :=
      polygon4gBoundaryArcStepsDiskChain
        (polygon4gBoundaryArcStepsReverse repair.steps)
    projectedRepairChain :=
      polygon4gBoundaryArcStepsProjectedChain g
        (polygon4gBoundaryArcStepsReverse repair.steps)
    edgeChainBoundary :=
      projectedReverseHomotopy - repair.edgeChainBoundary
    steps := polygon4gBoundaryArcStepsReverse repair.steps
    steps_connect := Polygon4gBoundaryArcListConnects.reverse repair.steps_connect
    diskRepairChain_eq := ?_
    projectedRepairChain_eq := ?_
    diskRepairBoundary := ?_
    projectedRepairBoundary := ?_
    projectedRepair_homologous_edge := ?_
  }⟩
  · rfl
  · rfl
  · have horig :
        (singularChainComplexZ DiskC).d 1 0
            (polygon4gBoundaryArcStepsDiskChain repair.steps) =
          pointChain DiskC q - pointChain DiskC p := by
        rw [show polygon4gBoundaryArcStepsDiskChain repair.steps =
          repair.diskRepairChain from repair.diskRepairChain_eq.symm]
        exact repair.diskRepairBoundary
    rw [hdiskBoundary, horig]
    abel
  · have horig :
        (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
            (polygon4gBoundaryArcStepsProjectedChain g repair.steps) =
          pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) q) -
            pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) p) := by
        rw [show polygon4gBoundaryArcStepsProjectedChain g repair.steps =
          repair.projectedRepairChain from repair.projectedRepairChain_eq.symm]
        exact repair.projectedRepairBoundary
    rw [hprojectedBoundary, horig]
    abel
  · rw [map_sub, hprojectedReverseHomotopy,
      repair.projectedRepair_homologous_edge]
    have hsum :
        (∑ e : Fin (2 * (g + 1)),
          (-repair.coeff) e • edgeChain g e) =
          - (∑ e : Fin (2 * (g + 1)),
            repair.coeff e • edgeChain g e) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro e _he
      rw [Pi.neg_apply, neg_zsmul]
    rw [hsum]
    rw [show polygon4gBoundaryArcStepsProjectedChain g repair.steps =
      repair.projectedRepairChain from repair.projectedRepairChain_eq.symm]
    abel

/--
Algebraic concatenation of endpoint repair data.  This should append
the step lists, add coefficients, and add the stored two-chains.
-/
theorem polygon4g_endpoint_pair_repaired_trans
    (g : ℕ) (p q r : DiskC)
    (hpq : Polygon4g.SideRel (g + 1) p q)
    (hqr : Polygon4g.SideRel (g + 1) q r)
    (repair_pq : Polygon4gEndpointRepairData g p q hpq)
    (repair_qr : Polygon4gEndpointRepairData g q r hqr) :
    Nonempty (Polygon4gEndpointRepairData g p r
      (Relation.EqvGen.trans p q r hpq hqr)) := by
  refine ⟨{
    coeff := repair_pq.coeff + repair_qr.coeff
    diskRepairChain := repair_pq.diskRepairChain + repair_qr.diskRepairChain
    projectedRepairChain := repair_pq.projectedRepairChain + repair_qr.projectedRepairChain
    edgeChainBoundary := repair_pq.edgeChainBoundary + repair_qr.edgeChainBoundary
    steps := repair_pq.steps ++ repair_qr.steps
    steps_connect :=
      Polygon4gBoundaryArcListConnects.append
        repair_pq.steps_connect repair_qr.steps_connect
    diskRepairChain_eq := ?_
    projectedRepairChain_eq := ?_
    diskRepairBoundary := ?_
    projectedRepairBoundary := ?_
    projectedRepair_homologous_edge := ?_
  }⟩
  · rw [repair_pq.diskRepairChain_eq, repair_qr.diskRepairChain_eq]
    simp [List.map_append]
  · rw [repair_pq.projectedRepairChain_eq, repair_qr.projectedRepairChain_eq,
      polygon4gBoundaryArcStepsProjectedChain_append]
  · rw [map_add, repair_pq.diskRepairBoundary, repair_qr.diskRepairBoundary]
    abel
  · rw [map_add, repair_pq.projectedRepairBoundary, repair_qr.projectedRepairBoundary]
    abel
  · rw [map_add, repair_pq.projectedRepair_homologous_edge,
      repair_qr.projectedRepair_homologous_edge]
    have hsum :
        (∑ e : Fin (2 * (g + 1)),
          (repair_pq.coeff + repair_qr.coeff) e • edgeChain g e) =
          (∑ e : Fin (2 * (g + 1)), repair_pq.coeff e • edgeChain g e) +
            (∑ e : Fin (2 * (g + 1)), repair_qr.coeff e • edgeChain g e) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro e _he
      rw [Pi.add_apply, add_zsmul]
    rw [hsum]
    abel

/--
If two lifted endpoints project to the same polygon point, their
endpoint difference is repaired by a finite integral sum of polygon
edge arcs.
-/
theorem polygon4g_endpoint_pair_repaired_by_edge_arcs
    (g : ℕ) (p q : DiskC)
    (hrel : Polygon4g.SideRel (g + 1) p q) :
    Nonempty (Polygon4gEndpointRepairData g p q hrel) := by
  induction hrel with
  | rel _ _ hgen =>
      exact polygon4g_endpoint_pair_repaired_by_sideGen g _ _ hgen
  | refl x =>
      exact polygon4g_endpoint_pair_repaired_refl g x
  | symm _ _ _ ih =>
      obtain ⟨repair⟩ := ih
      exact polygon4g_endpoint_pair_repaired_symm g _ _ _ repair
  | trans _ _ _ _ _ ih₁ ih₂ =>
      obtain ⟨repair₁⟩ := ih₁
      obtain ⟨repair₂⟩ := ih₂
      exact polygon4g_endpoint_pair_repaired_trans g _ _ _ _ _ repair₁ repair₂

/--
Disk contractibility package, in the homology-level form needed by
the polygon projection step: every singular one-cycle in `DiskC` has
zero `H₁` class.
-/
theorem diskC_singular_one_cycle_homologyClass_eq_zero
    (z : SingularChainCoproduct DiskC 1)
    (hz : (singularChainComplexZ DiskC).d 1 0 z = 0) :
    singularH1ClassOfCycle DiskC z hz = 0 := by
  haveI : Subsingleton (singularH1 DiskC) :=
    singularH1_subsingleton_of_contractibleSpace
  exact Subsingleton.elim _ _

/--
The homology class of the i-th edge cycle in
`singularH1 (Polygon4g (g+1))`.
-/
noncomputable def edgeHomologyClass (g : ℕ) (i : Fin (2 * (g + 1))) :
    singularH1 (Polygon4g (g + 1)) :=
  ((forget₂ (ModuleCat ℤ) Ab).map
      ((Polygon4gSingularC1.polygonChainComplexOnGenus (g + 1)).homologyπ 1))
    ((Polygon4gSingularC1.polygonChainComplexOnGenus (g + 1)).cyclesMk
      (edgeChain g i) 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
      (by
        simpa [Polygon4gSingularC1.polygonChainComplexOnGenus]
          using edgeChain_isCycle g i))

/-- The image set of the edge homology classes. -/
noncomputable def edgeHomologyFamily (g : ℕ) :
    Fin (2 * (g + 1)) → singularH1 (Polygon4g (g + 1)) :=
  edgeHomologyClass g

/--
The linear map sending each free edge generator to its concrete
singular homology class.
-/
noncomputable def edgeBasisMap (g : ℕ) :
    Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g + 1)) :=
  ∑ i : Fin (2 * (g + 1)),
    (LinearMap.toSpanSingleton ℤ _ (edgeHomologyClass g i)).comp
      (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (2 * (g + 1)) => ℤ) i)

/-- Evaluation of the edge-basis map on coefficients. -/
theorem edgeBasisMap_apply (g : ℕ) (v : Polygon4gAbelianization g) :
    edgeBasisMap g v =
      ∑ i : Fin (2 * (g + 1)),
        LinearMap.toSpanSingleton ℤ _ (edgeHomologyClass g i) (v i) := by
  simp [edgeBasisMap, LinearMap.proj]

/--
The homology class of a finite integral edge-chain combination is
exactly the edge-basis map applied to its coefficient vector.
-/
theorem edgeBasisMap_eq_homologyClass_edgeChain_sum
    (g : ℕ) (v : Polygon4gAbelianization g)
    (hsum :
      (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) = 0) :
    singularH1ClassOfCycle (Polygon4g (g + 1))
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) hsum =
        edgeBasisMap g v := by
  classical
  let K := singularChainComplexZ (Polygon4g (g + 1))
  have hclass_sum :
      singularH1ClassOfCycle (Polygon4g (g + 1))
        (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) hsum =
          ∑ i : Fin (2 * (g + 1)), v i • edgeHomologyClass g i := by
    unfold singularH1ClassOfCycle
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1))
        (K.cyclesMk (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hsum) =
      ∑ i : Fin (2 * (g + 1)), v i • edgeHomologyClass g i
    have hcycles :
        K.cyclesMk (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hsum =
          ∑ i : Fin (2 * (g + 1)),
            v i • K.cyclesMk (edgeChain g i) 0
              (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
              (by
                simpa [K, singularChainComplexZ,
                    Polygon4gSingularC1.polygonChainComplexOnGenus]
                  using edgeChain_isCycle g i) := by
      apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
      change
        ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
          (K.cyclesMk (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hsum) =
        ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
          (∑ i : Fin (2 * (g + 1)),
            v i • K.cyclesMk (edgeChain g i) 0
              (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
              (by
                simpa [K, singularChainComplexZ,
                    Polygon4gSingularC1.polygonChainComplexOnGenus]
                  using edgeChain_isCycle g i))
      rw [K.i_cyclesMk, map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [map_zsmul, K.i_cyclesMk]
    rw [hcycles, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [map_zsmul]
    unfold edgeHomologyClass
    rfl
  rw [edgeBasisMap_apply, hclass_sum]
  simp only [LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact (Int.cast_smul_eq_zsmul (R := ℤ) (v i) (edgeHomologyClass g i)).symm

/--
A finite integral combination of polygon edge chains is a singular
one-cycle.
-/
theorem edgeChain_sum_isCycle
    (g : ℕ) (v : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero (fun e _he => ?_)
  rw [map_zsmul, edgeChain_isCycle g e]
  exact zsmul_zero (v e)

/--
Repaired disk-cycle data for a polygon singular cycle.  The disk
cycle records the lifted-and-repaired cycle in `DiskC`; the projection
relation says that the original polygon class is the projected disk
class plus the concrete edge correction.
-/
structure Polygon4gRepairedDiskCycleData
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0) where
  edgeCoeffs : Polygon4gAbelianization g
  diskCycle : SingularChainCoproduct DiskC 1
  diskCycle_isCycle : (singularChainComplexZ DiskC).d 1 0 diskCycle = 0
  projected_relation :
    singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
        (singularH1ClassOfCycle DiskC diskCycle diskCycle_isCycle) +
        edgeBasisMap g edgeCoeffs

/--
A finite-support presentation of a singular one-chain as an
integral sum of singular one-simplices.
-/
structure SingularOneChainSupportDecomposition
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1) where
  Simplex : Type
  simplexFintype : Fintype Simplex
  coeff : Simplex → ℤ
  simplex : Simplex → C(stdSimplex ℝ (Fin 2), X)
  chain_eq :
    z = ∑ s : Simplex, coeff s • singularChainElement (simplex s)

/--
Atomic finite-support algebra leaf: every coproduct singular
one-chain has a finite presentation by basis singular simplices.
-/
theorem singularChainCoproduct_sum_support_decomposition
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1) :
    Nonempty (SingularOneChainSupportDecomposition X z) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋1⦌)
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let dz : DirectSum I (fun i => (Z i : Type)) := iso.hom.hom z
  let f : I →₀ ℤ := (finsuppLEquivDirectSum ℤ ℤ I).symm dz
  let Simplex := {i : I // i ∈ f.support}
  refine ⟨{
    Simplex := Simplex
    simplexFintype := inferInstance
    coeff := fun s => f s.1
    simplex := fun s => (singularChainSimplexIndex X 1).symm s.1
    chain_eq := ?_
  }⟩
  change z =
    ∑ s : Simplex,
      f s.1 • singularChainElement ((singularChainSimplexIndex X 1).symm s.1)
  have hinj : Function.Injective iso.hom.hom := by
    intro a b h
    have h2 := congrArg iso.inv.hom h
    simpa [iso, Z] using h2
  apply hinj
  rw [map_sum]
  simp only [map_zsmul]
  have hdz : dz = (finsuppLEquivDirectSum ℤ ℤ I) f := by
    simp [f, dz]
  change dz =
    ∑ x : Simplex,
      f x.1 • iso.hom.hom
        (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))
  rw [hdz]
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hsum :
      (∑ x : Simplex,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    change
      (∑ x ∈ f.support.attach,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)
    simpa [singularChainElement, I, Z, iso, hι] using
      (Finset.sum_attach f.support
        (fun i => f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)))
  rw [hsum]
  rw [← Finsupp.sum_of_support_subset f
    (show f.support ⊆ f.support from fun _ h => h)
    (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ))]
  · calc
      (finsuppLEquivDirectSum ℤ ℤ I) f
          = (finsuppLEquivDirectSum ℤ ℤ I)
              (f.sum fun i c => Finsupp.single i c) := by
              rw [Finsupp.sum_single]
      _ = f.sum
            (fun i c => (finsuppLEquivDirectSum ℤ ℤ I) (Finsupp.single i c)) := by
              simp [Finsupp.sum, map_sum]
      _ = f.sum
            (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)) := by
              apply Finsupp.sum_congr
              intro i _hi
              simpa [finsuppLEquivDirectSum_single] using
                ((DirectSum.lof ℤ I (fun _ : I => ℤ) i).map_smul (f i) (1 : ℤ))
  · intro i _hi
    simp

/--
A finite-support presentation of a singular `n`-chain as an integral
sum of singular `n`-simplices.
-/
structure SingularChainSupportDecomposition
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : SingularChainCoproduct X n) where
  Simplex : Type
  simplexFintype : Fintype Simplex
  coeff : Simplex → ℤ
  simplex : Simplex → C(stdSimplex ℝ (Fin (n + 1)), X)
  chain_eq :
    z = ∑ s : Simplex, coeff s • singularChainElement (simplex s)

/--
Atomic finite-support algebra leaf in arbitrary degree: every
coproduct singular chain has a finite presentation by basis singular
simplices.
-/
theorem singularChainCoproduct_sum_support_decomposition_degree
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : SingularChainCoproduct X n) :
    Nonempty (SingularChainSupportDecomposition X n z) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let dz : DirectSum I (fun i => (Z i : Type)) := iso.hom.hom z
  let f : I →₀ ℤ := (finsuppLEquivDirectSum ℤ ℤ I).symm dz
  let Simplex := {i : I // i ∈ f.support}
  refine ⟨{
    Simplex := Simplex
    simplexFintype := inferInstance
    coeff := fun s => f s.1
    simplex := fun s => (singularChainSimplexIndex X n).symm s.1
    chain_eq := ?_
  }⟩
  change z =
    ∑ s : Simplex,
      f s.1 • singularChainElement ((singularChainSimplexIndex X n).symm s.1)
  have hinj : Function.Injective iso.hom.hom := by
    intro a b h
    have h2 := congrArg iso.inv.hom h
    simpa [iso, Z] using h2
  apply hinj
  rw [map_sum]
  simp only [map_zsmul]
  have hdz : dz = (finsuppLEquivDirectSum ℤ ℤ I) f := by
    simp [f, dz]
  change dz =
    ∑ x : Simplex,
      f x.1 • iso.hom.hom
        (singularChainElement ((singularChainSimplexIndex X n).symm x.1))
  rw [hdz]
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hsum :
      (∑ x : Simplex,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X n).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    change
      (∑ x ∈ f.support.attach,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X n).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)
    simpa [singularChainElement, I, Z, iso, hι] using
      (Finset.sum_attach f.support
        (fun i => f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)))
  rw [hsum]
  rw [← Finsupp.sum_of_support_subset f
    (show f.support ⊆ f.support from fun _ h => h)
    (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ))]
  · calc
      (finsuppLEquivDirectSum ℤ ℤ I) f
          = (finsuppLEquivDirectSum ℤ ℤ I)
              (f.sum fun i c => Finsupp.single i c) := by
              rw [Finsupp.sum_single]
      _ = f.sum
            (fun i c => (finsuppLEquivDirectSum ℤ ℤ I) (Finsupp.single i c)) := by
              simp [Finsupp.sum, map_sum]
      _ = f.sum
            (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)) := by
              apply Finsupp.sum_congr
              intro i _hi
              simpa [finsuppLEquivDirectSum_single] using
                ((DirectSum.lof ℤ I (fun _ : I => ℤ) i).map_smul (f i) (1 : ℤ))
  · intro i _hi
    simp

/--
Lift data summed over a finite-support presentation of a polygon
singular one-chain.  This is still before endpoint repair: it only says
each support simplex has a subdivision/lift package and records the
summed lifted disk chain and projected subdivided chain.
-/
structure Polygon4gLiftedSupportData
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z) where
  simplexLift :
    ∀ s : decomp.Simplex,
      Polygon4gSingularSimplexDiskLiftData g (decomp.simplex s)
  liftedDiskChain : SingularChainCoproduct DiskC 1
  liftedDiskChain_eq :
    liftedDiskChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s •
          (∑ i : Fin ((simplexLift s).n),
            singularChainElement ((simplexLift s).lift i)))
  projectedSubdivisionChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  projectedSubdivisionChain_eq :
    projectedSubdivisionChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s • (simplexLift s).subdividedChain)
  subdivisionBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  subdivision_homology :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 subdivisionBoundary =
      projectedSubdivisionChain - z

/--
Atomic lift-summation leaf: apply simplex subdivision/lift data over
the finite support of a singular chain and sum the resulting chain
relations.
-/
theorem polygon4g_lift_data_sum_projects_to_subdivision_chain
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z) :
    Nonempty (Polygon4gLiftedSupportData g z decomp) := by
  classical
  let simplexLift :
      ∀ s : decomp.Simplex,
        Polygon4gSingularSimplexDiskLiftData g (decomp.simplex s) :=
    fun s => Classical.choice
      (polygon4g_singularSimplex_subdivision_lifts_to_disk g (decomp.simplex s))
  let liftedDiskChain : SingularChainCoproduct DiskC 1 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s •
        (∑ i : Fin ((simplexLift s).n),
          singularChainElement ((simplexLift s).lift i)))
  let projectedSubdivisionChain :
      SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s • (simplexLift s).subdividedChain)
  let subdivisionBoundary :
      SingularChainCoproduct (Polygon4g (g + 1)) 2 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s • (simplexLift s).subdivisionBoundary)
  refine ⟨{
    simplexLift := simplexLift
    liftedDiskChain := liftedDiskChain
    liftedDiskChain_eq := rfl
    projectedSubdivisionChain := projectedSubdivisionChain
    projectedSubdivisionChain_eq := rfl
    subdivisionBoundary := subdivisionBoundary
    subdivision_homology := ?_
  }⟩
  letI := decomp.simplexFintype
  dsimp [subdivisionBoundary, projectedSubdivisionChain]
  rw [map_sum]
  simp only [map_zsmul]
  calc
    ∑ s : decomp.Simplex,
        decomp.coeff s •
          (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
            (simplexLift s).subdivisionBoundary
        =
      ∑ s : decomp.Simplex,
        decomp.coeff s •
          ((simplexLift s).subdividedChain -
            singularChainElement (decomp.simplex s)) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          exact congrArg (fun c => decomp.coeff s • c)
            (simplexLift s).subdivision_homology
    _ =
      (∑ s : decomp.Simplex, decomp.coeff s • (simplexLift s).subdividedChain) -
        ∑ s : decomp.Simplex,
          decomp.coeff s • singularChainElement (decomp.simplex s) := by
          simp [zsmul_sub, Finset.sum_sub_distrib]
    _ =
      (∑ s : decomp.Simplex, decomp.coeff s • (simplexLift s).subdividedChain) -
        z := by
          exact congrArg
            (fun t =>
              (∑ s : decomp.Simplex,
                decomp.coeff s • (simplexLift s).subdividedChain) - t)
            decomp.chain_eq.symm

/--
The projected subdivision chain is exactly the degree-one singular
chain pushforward of the summed lifted disk chain.
-/
theorem polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
        lifted.liftedDiskChain =
      lifted.projectedSubdivisionChain := by
  classical
  letI := decomp.simplexFintype
  rw [lifted.liftedDiskChain_eq, lifted.projectedSubdivisionChain_eq]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [map_zsmul]
  congr 1
  rw [map_sum, (lifted.simplexLift s).subdividedChain_eq]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact singularChainElement_map (polygon4gMkContinuousMap (g + 1)) 1
    ((lifted.simplexLift s).lift i)

/--
Endpoint pairs extracted from the boundary of the summed lifted
chain.  Each pair is a specific `SideRel` pair and carries the endpoint
repair data for that relation.
-/
structure Polygon4gCycleEndpointPairFamily
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint : Pair → DiskC
  rightEndpoint : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint pair) (rightEndpoint pair)
  repair :
    ∀ pair : Pair,
      Polygon4gEndpointRepairData g (leftEndpoint pair) (rightEndpoint pair)
        (endpointRel pair)
  lifted_boundary_eq_pairs :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint pair) -
            pointChain DiskC (leftEndpoint pair))

/--
Endpoint relation pairs extracted from the boundary of the summed
lifted chain, before endpoint repairs are attached.
-/
structure Polygon4gCycleEndpointRelPairFamily
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint : Pair → DiskC
  rightEndpoint : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint pair) (rightEndpoint pair)
  lifted_boundary_eq_pairs :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint pair) -
            pointChain DiskC (leftEndpoint pair))

/--
The projected boundary of the lifted disk chain vanishes in the
polygon quotient.  This is the chain-map/naturality part of endpoint
pair extraction, before finite endpoint pairing is applied.
-/
structure Polygon4gLiftedBoundaryProjectsToZero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  projected_lifted_boundary_zero :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 0)
        ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) = 0

/--
The boundary of the summed lifted disk chain expanded into the
finite list of endpoints of the lifted subdivided one-simplices.
-/
structure Polygon4gLiftedEndpointBoundaryExpansion
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  lifted_boundary_eq_endpoint_sum :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s •
          ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
            (fun i =>
            pointChain DiskC ((lifted.simplexLift s).lift i (stdSimplexVertex 1)) -
              pointChain DiskC
                ((lifted.simplexLift s).lift i (stdSimplexVertex 0)))))

/--
The quotient image of the expanded lifted endpoint boundary is zero.
This is still before the finite matching/permutation argument.
-/
structure Polygon4gProjectedEndpointBoundaryCancellation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  projected_endpoint_sum_zero :
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s =>
        decomp.coeff s •
          (((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
              (fun i =>
                pointChain (Polygon4g (g + 1))
                  (Polygon4g.mk (g + 1)
                    ((lifted.simplexLift s).lift i (stdSimplexVertex 1))))) -
            ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
              (fun i =>
                pointChain (Polygon4g (g + 1))
                  (Polygon4g.mk (g + 1)
                    ((lifted.simplexLift s).lift i (stdSimplexVertex 0))))))) = 0

/--
Pure finite-support endpoint pairing output.  This strips the
cycle-level names away from endpoint matching: a finite signed endpoint
sum in the disk whose projection vanishes is represented as endpoint
differences between disk points with equal quotient images, equivalently
`SideRel`-related endpoints.
-/
structure FiniteProjectedEndpointPairFamily
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (boundary : SingularChainCoproduct DiskC 0) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint' : Pair → DiskC
  rightEndpoint' : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint' pair) (rightEndpoint' pair)
  boundary_eq_pairs :
    boundary =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint' pair) -
            pointChain DiskC (leftEndpoint' pair))

/--
Finite endpoint matching data for a projected-zero endpoint sum.

This is the pure finite-support matching substrate: after expanding the
integer coefficients into endpoint occurrences, vanishing of the projected
endpoint sum pairs each disk endpoint with another endpoint having the same
quotient image, hence related by `Polygon4g.SideRel`.
-/
structure FiniteProjectedEndpointMatchingData
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint' : Pair → DiskC
  rightEndpoint' : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint' pair) (rightEndpoint' pair)
  endpoint_sum_eq_pairs :
    (@Finset.univ S inferInstance).sum
        (fun s => coeff s •
          ((@Finset.univ (I s) inferInstance).sum
            (fun i =>
              pointChain DiskC (rightEndpoint s i) -
                pointChain DiskC (leftEndpoint s i)))) =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint' pair) -
            pointChain DiskC (leftEndpoint' pair))

/--
Architectural finite-support matching provider.

Given a finite signed endpoint sum whose quotient projection vanishes,
construct matched disk endpoints whose differences realize the original
disk endpoint sum. This is the finite free-abelian bookkeeping leaf
behind endpoint repair; the surrounding theorem only substitutes an
arbitrary `boundary` known to equal this endpoint sum.
-/
theorem finite_projected_endpoint_matching_data
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (_projected_endpoint_sum_zero :
      (@Finset.univ S inferInstance).sum
        (fun s =>
          coeff s •
            (((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (rightEndpoint s i)))) -
              ((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (leftEndpoint s i)))))) = 0) :
    Nonempty
      (FiniteProjectedEndpointMatchingData
        g S I coeff leftEndpoint rightEndpoint) := by
  -- Finite free-abelian matching: normalize signed integer coefficients,
  -- pair projected endpoint occurrences in the quotient, then convert
  -- equality of quotient representatives to `Polygon4g.SideRel`.
  sorry

/--
Finite-support quotient bookkeeping provider.  This is the exact
remaining algebraic leaf below cycle-level endpoint extraction: from a
finite signed endpoint expansion and vanishing of its quotient image,
construct a finite family of matched endpoint differences.
-/
theorem finite_projected_endpoint_sum_zero_pairing
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (boundary : SingularChainCoproduct DiskC 0)
    (_boundary_eq_endpoint_sum :
      boundary =
        (@Finset.univ S inferInstance).sum
          (fun s => coeff s •
            ((@Finset.univ (I s) inferInstance).sum
              (fun i =>
                pointChain DiskC (rightEndpoint s i) -
                  pointChain DiskC (leftEndpoint s i)))))
    (_projected_endpoint_sum_zero :
      (@Finset.univ S inferInstance).sum
        (fun s =>
          coeff s •
            (((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (rightEndpoint s i)))) -
              ((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (leftEndpoint s i)))))) = 0) :
    Nonempty
      (FiniteProjectedEndpointPairFamily g S I coeff leftEndpoint rightEndpoint
        boundary) := by
  obtain ⟨pairs⟩ :=
    finite_projected_endpoint_matching_data
      g S I coeff leftEndpoint rightEndpoint _projected_endpoint_sum_zero
  exact ⟨{
    Pair := pairs.Pair
    pairFintype := pairs.pairFintype
    leftEndpoint' := pairs.leftEndpoint'
    rightEndpoint' := pairs.rightEndpoint'
    endpointRel := pairs.endpointRel
    boundary_eq_pairs := by
      rw [_boundary_eq_endpoint_sum, pairs.endpoint_sum_eq_pairs]
  }⟩

/--
Chain-boundary expansion part of endpoint extraction: no quotient
pairing is involved here, only finite-sum algebra and the boundary
formula for singular one-simplices.
-/
theorem polygon4g_lifted_endpoint_boundary_expansion
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted := by
  classical
  refine ⟨?_⟩
  rw [lifted.liftedDiskChain_eq, map_sum]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [map_zsmul, map_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact singularChainElement_boundary_one_simplex DiskC
    ((lifted.simplexLift s).lift i)

/--
Project the expanded lifted endpoint boundary to the polygon
quotient and use the chain-map zero result.
-/
theorem polygon4g_projected_endpoint_boundary_cancellation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (projectedZero :
      Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted)
    (endpointExpansion :
      Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted) :
    Polygon4gProjectedEndpointBoundaryCancellation g z hz decomp lifted := by
  classical
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  have hmap :=
    congrArg (fun c => ModuleCat.Hom.hom (F.f 0) c)
      endpointExpansion.lifted_boundary_eq_endpoint_sum
  have hzero :
      ModuleCat.Hom.hom (F.f 0)
        ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) = 0 := by
    simpa [F] using projectedZero.projected_lifted_boundary_zero
  have hmap' :
      ModuleCat.Hom.hom (F.f 0)
          ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) =
        ModuleCat.Hom.hom (F.f 0)
          ((@Finset.univ decomp.Simplex decomp.simplexFintype).sum
            (fun s => decomp.coeff s •
              ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
                (fun i =>
                  pointChain DiskC
                      ((lifted.simplexLift s).lift i (stdSimplexVertex 1)) -
                    pointChain DiskC
                      ((lifted.simplexLift s).lift i (stdSimplexVertex 0)))))) := by
    simpa using hmap
  rw [hzero] at hmap'
  rw [map_sum] at hmap'
  simp only [map_zsmul] at hmap'
  simp [F, pointChain_map] at hmap'
  exact ⟨hmap'.symm⟩

/--
Chain-map part of endpoint extraction: use the projected cycle
condition and subdivision homology to show the projected lifted boundary
is zero.
-/
theorem polygon4g_lifted_boundary_projects_to_zero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Nonempty (Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted) := by
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  let K := singularChainComplexZ (Polygon4g (g + 1))
  have hcomm :
      ModuleCat.Hom.hom (F.f 0)
          ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) =
        K.d 1 0 (ModuleCat.Hom.hom (F.f 1) lifted.liftedDiskChain) := by
    rw [← ModuleCat.comp_apply ((singularChainComplexZ DiskC).d 1 0) (F.f 0)]
    rw [← ModuleCat.comp_apply (F.f 1) (K.d 1 0)]
    exact congrArg
      (fun φ : (singularChainComplexZ DiskC).X 1 ⟶ K.X 0 =>
        ModuleCat.Hom.hom φ lifted.liftedDiskChain)
      (F.comm 1 0).symm
  have hproj :
      ModuleCat.Hom.hom (F.f 1) lifted.liftedDiskChain =
        lifted.projectedSubdivisionChain := by
    simpa [F] using
      polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain
        g z decomp lifted
  have hboundary_projected :
      K.d 1 0 lifted.projectedSubdivisionChain = 0 := by
    have hdd :
        K.d 1 0 (K.d 2 1 lifted.subdivisionBoundary) = 0 := by
      rw [← ModuleCat.comp_apply (K.d 2 1) (K.d 1 0)]
      exact congrArg
        (fun φ : K.X 2 ⟶ K.X 0 =>
          ModuleCat.Hom.hom φ lifted.subdivisionBoundary)
        (HomologicalComplex.d_comp_d K 2 1 0)
    have hsub := congrArg (fun c => K.d 1 0 c) lifted.subdivision_homology
    change K.d 1 0 (K.d 2 1 lifted.subdivisionBoundary) =
      K.d 1 0 (lifted.projectedSubdivisionChain - z) at hsub
    rw [hdd, map_sub, hz, sub_zero] at hsub
    exact hsub.symm
  refine ⟨{ projected_lifted_boundary_zero := ?_ }⟩
  rw [hcomm, hproj, hboundary_projected]

/--
Finite endpoint-pairing leaf: once the projected boundary of a
finite disk endpoint chain is zero, pair the disk endpoints whose
projections agree, and convert those equal projections to `SideRel`.
-/
theorem finite_projected_endpoint_boundary_zero_pairs
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (_projectedZero :
      Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted)
    (_endpointExpansion :
      Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted)
    (_projectedEndpointCancellation :
      Polygon4gProjectedEndpointBoundaryCancellation g z hz decomp lifted) :
    Nonempty (Polygon4gCycleEndpointRelPairFamily g z hz decomp lifted) := by
  classical
  letI := decomp.simplexFintype
  let I : decomp.Simplex → Type :=
    fun s => Fin ((lifted.simplexLift s).n)
  let leftEndpoint : ∀ s, I s → DiskC :=
    fun s i => (lifted.simplexLift s).lift i (stdSimplexVertex 0)
  let rightEndpoint : ∀ s, I s → DiskC :=
    fun s i => (lifted.simplexLift s).lift i (stdSimplexVertex 1)
  obtain ⟨pairs⟩ :=
    finite_projected_endpoint_sum_zero_pairing
      g decomp.Simplex I decomp.coeff leftEndpoint rightEndpoint
      ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain)
      (by
        simpa [I, leftEndpoint, rightEndpoint] using
          _endpointExpansion.lifted_boundary_eq_endpoint_sum)
      (by
        simpa [I, leftEndpoint, rightEndpoint] using
          _projectedEndpointCancellation.projected_endpoint_sum_zero)
  exact ⟨{
    Pair := pairs.Pair
    pairFintype := pairs.pairFintype
    leftEndpoint := pairs.leftEndpoint'
    rightEndpoint := pairs.rightEndpoint'
    endpointRel := pairs.endpointRel
    lifted_boundary_eq_pairs := pairs.boundary_eq_pairs
  }⟩

/--
Atomic endpoint-pair extraction leaf: the polygon cycle condition
forces the boundary of the lifted disk chain to be a finite sum of
`SideRel` endpoint pairs.  Endpoint repairs are attached separately.
-/
theorem polygon4g_cycle_endpoint_rel_pairs_from_boundary_zero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Nonempty (Polygon4gCycleEndpointRelPairFamily g z hz decomp lifted) := by
  obtain ⟨projectedZero⟩ :=
    polygon4g_lifted_boundary_projects_to_zero g z hz decomp lifted
  let endpointExpansion :=
    polygon4g_lifted_endpoint_boundary_expansion g z decomp lifted
  let projectedEndpointCancellation :=
    polygon4g_projected_endpoint_boundary_cancellation
      g z hz decomp lifted projectedZero endpointExpansion
  exact finite_projected_endpoint_boundary_zero_pairs
    g z hz decomp lifted projectedZero endpointExpansion
      projectedEndpointCancellation

/-- Endpoint-pair extraction with endpoint repairs attached. -/
theorem polygon4g_cycle_endpoint_pairs_from_boundary_zero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Nonempty (Polygon4gCycleEndpointPairFamily g z hz decomp lifted) := by
  classical
  obtain ⟨pairs⟩ :=
    polygon4g_cycle_endpoint_rel_pairs_from_boundary_zero g z hz decomp lifted
  let repair :
      ∀ pair : pairs.Pair,
        Polygon4gEndpointRepairData g (pairs.leftEndpoint pair)
          (pairs.rightEndpoint pair) (pairs.endpointRel pair) :=
    fun pair => Classical.choice
      (polygon4g_endpoint_pair_repaired_by_edge_arcs g
        (pairs.leftEndpoint pair) (pairs.rightEndpoint pair)
        (pairs.endpointRel pair))
  exact ⟨{
    Pair := pairs.Pair
    pairFintype := pairs.pairFintype
    leftEndpoint := pairs.leftEndpoint
    rightEndpoint := pairs.rightEndpoint
    endpointRel := pairs.endpointRel
    repair := repair
    lifted_boundary_eq_pairs := pairs.lifted_boundary_eq_pairs
  }⟩

/--
The chain-algebra output of summing a finite family of endpoint
repairs.  This is separated from the final homology statement so the
remaining obstruction, if any, is only the passage from explicit
chain-boundary relations to equality in `H₁`.
-/
structure Polygon4gRepairSumAlgebraData
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted) where
  edgeCoeffs : Polygon4gAbelianization g
  diskRepairSum : SingularChainCoproduct DiskC 1
  diskCycle : SingularChainCoproduct DiskC 1
  diskCycle_eq : diskCycle = lifted.liftedDiskChain - diskRepairSum
  diskCycle_isCycle : (singularChainComplexZ DiskC).d 1 0 diskCycle = 0
  projectedRepairSum : SingularChainCoproduct (Polygon4g (g + 1)) 1
  projectedRepairSum_eq_chainMap_diskRepairSum :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      diskRepairSum =
      projectedRepairSum
  projectedRepairBoundary :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 projectedRepairSum =
      (@Finset.univ pairs.Pair pairs.pairFintype).sum
        (fun pair =>
          pointChain (Polygon4g (g + 1))
              (Polygon4g.mk (g + 1) (pairs.rightEndpoint pair)) -
            pointChain (Polygon4g (g + 1))
              (Polygon4g.mk (g + 1) (pairs.leftEndpoint pair)))
  edgeChainBoundarySum : SingularChainCoproduct (Polygon4g (g + 1)) 2
  projectedRepair_homologous_edge :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 edgeChainBoundarySum =
      projectedRepairSum -
        ∑ e : Fin (2 * (g + 1)), edgeCoeffs e • edgeChain g e

/--
The finite-sum repair algebra: endpoint repairs can be summed into a
repaired disk cycle and a projected repair chain homologous to the
corresponding edge-chain combination.
-/
noncomputable def polygon4g_repair_pairs_sum_algebra_data
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted) :
    Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs := by
  classical
  letI := pairs.pairFintype
  let pairFinset : Finset pairs.Pair := @Finset.univ pairs.Pair pairs.pairFintype
  let edgeCoeffs : Polygon4gAbelianization g :=
    pairFinset.sum fun pair => (pairs.repair pair).coeff
  let diskRepairSum : SingularChainCoproduct DiskC 1 :=
    pairFinset.sum fun pair => (pairs.repair pair).diskRepairChain
  let diskCycle : SingularChainCoproduct DiskC 1 :=
    lifted.liftedDiskChain - diskRepairSum
  let projectedRepairSum : SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    pairFinset.sum fun pair => (pairs.repair pair).projectedRepairChain
  let edgeChainBoundarySum : SingularChainCoproduct (Polygon4g (g + 1)) 2 :=
    pairFinset.sum fun pair => (pairs.repair pair).edgeChainBoundary
  refine {
    edgeCoeffs := edgeCoeffs
    diskRepairSum := diskRepairSum
    diskCycle := diskCycle
    diskCycle_eq := rfl
    diskCycle_isCycle := ?_
    projectedRepairSum := projectedRepairSum
    projectedRepairSum_eq_chainMap_diskRepairSum := ?_
    projectedRepairBoundary := ?_
    edgeChainBoundarySum := edgeChainBoundarySum
    projectedRepair_homologous_edge := ?_
  }
  · dsimp [diskCycle, diskRepairSum, pairFinset]
    rw [map_sub, pairs.lifted_boundary_eq_pairs, map_sum]
    have hrepair :
        (∑ x : pairs.Pair,
          (singularChainComplexZ DiskC).d 1 0 (pairs.repair x).diskRepairChain) =
        ∑ x : pairs.Pair,
          (pointChain DiskC (pairs.rightEndpoint x) -
            pointChain DiskC (pairs.leftEndpoint x)) := by
      refine Finset.sum_congr rfl ?_
      intro pair _hpair
      exact (pairs.repair pair).diskRepairBoundary
    rw [hrepair]
    simp
  · dsimp [projectedRepairSum, diskRepairSum, pairFinset]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro pair _hpair
    exact polygon4gEndpointRepair_projected_eq_chainMap g
      (pairs.leftEndpoint pair) (pairs.rightEndpoint pair)
      (pairs.endpointRel pair) (pairs.repair pair)
  · dsimp [projectedRepairSum, pairFinset]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro pair _hpair
    exact (pairs.repair pair).projectedRepairBoundary
  · dsimp [edgeChainBoundarySum, projectedRepairSum, edgeCoeffs, pairFinset]
    rw [map_sum]
    calc
      ∑ x : pairs.Pair,
          (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
            (pairs.repair x).edgeChainBoundary
          =
        ∑ x : pairs.Pair,
          ((pairs.repair x).projectedRepairChain -
            ∑ e : Fin (2 * (g + 1)),
              (pairs.repair x).coeff e • edgeChain g e) := by
            refine Finset.sum_congr rfl ?_
            intro pair _hpair
            exact (pairs.repair pair).projectedRepair_homologous_edge
      _ =
        (∑ x : pairs.Pair, (pairs.repair x).projectedRepairChain) -
          ∑ x : pairs.Pair,
            ∑ e : Fin (2 * (g + 1)),
              (pairs.repair x).coeff e • edgeChain g e := by
            simp [Finset.sum_sub_distrib]
      _ =
        (∑ x : pairs.Pair, (pairs.repair x).projectedRepairChain) -
          ∑ e : Fin (2 * (g + 1)),
            (∑ x : pairs.Pair, (pairs.repair x).coeff e) • edgeChain g e := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro e _he
            simp_rw [← Int.cast_smul_eq_zsmul ℤ]
            exact (Finset.sum_smul
              (s := (Finset.univ : Finset pairs.Pair))
              (x := edgeChain g e)
              (f := fun x => (pairs.repair x).coeff e)).symm
      _ =
        (∑ x : pairs.Pair, (pairs.repair x).projectedRepairChain) -
          ∑ e : Fin (2 * (g + 1)),
            ((∑ x : pairs.Pair, (pairs.repair x).coeff) e) • edgeChain g e := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro e _he
            congr 1
            exact (Finset.sum_apply e (Finset.univ : Finset pairs.Pair)
              (fun x => (pairs.repair x).coeff)).symm

/--
The quotient-map pushforward of the repaired disk cycle is the
projected lifted subdivision chain minus the projected repair chain.
-/
theorem polygon4g_repair_sum_diskCycle_chainMap_eq
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted)
    (algebra : Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      algebra.diskCycle =
      lifted.projectedSubdivisionChain - algebra.projectedRepairSum := by
  rw [algebra.diskCycle_eq, map_sub,
    polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain g z decomp lifted,
    algebra.projectedRepairSum_eq_chainMap_diskRepairSum]

/--
Narrow remaining projection/naturality bridge for the repair-sum
package.  It no longer mentions the edge-basis map: it only says that
the quotient-map image of the repaired disk cycle, together with the
explicit repaired edge-chain cycle, represents the original polygon
cycle.
-/
theorem polygon4g_repair_sum_projected_diskCycle_relation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted)
    (algebra : Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs) :
    singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
        (singularH1ClassOfCycle DiskC algebra.diskCycle algebra.diskCycle_isCycle) +
        singularH1ClassOfCycle (Polygon4g (g + 1))
          (∑ e : Fin (2 * (g + 1)), algebra.edgeCoeffs e • edgeChain g e)
          (edgeChain_sum_isCycle g algebra.edgeCoeffs) := by
  let X := Polygon4g (g + 1)
  let K := singularChainComplexZ X
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  let pushedDiskCycle : SingularChainCoproduct X 1 :=
    ModuleCat.Hom.hom (F.f 1) algebra.diskCycle
  let edgeCycle : SingularChainCoproduct X 1 :=
    ∑ e : Fin (2 * (g + 1)), algebra.edgeCoeffs e • edgeChain g e
  have hpushedCycle : K.d 1 0 pushedDiskCycle = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
      (((forget₂ (ModuleCat ℤ) Ab).map (F.f 1)) algebra.diskCycle) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.Hom.comm,
      ConcreteCategory.forget₂_comp_apply]
    change ModuleCat.Hom.hom (F.f 0)
      (ModuleCat.Hom.hom ((singularChainComplexZ DiskC).d 1 0) algebra.diskCycle) = 0
    rw [algebra.diskCycle_isCycle]
    exact map_zero (ModuleCat.Hom.hom (F.f 0))
  have hedgeCycle : K.d 1 0 edgeCycle = 0 := by
    exact edgeChain_sum_isCycle g algebra.edgeCoeffs
  have hsumCycle : K.d 1 0 (pushedDiskCycle + edgeCycle) = 0 := by
    rw [map_add, hpushedCycle, hedgeCycle, add_zero]
  have hnat :
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
          (singularH1ClassOfCycle DiskC algebra.diskCycle algebra.diskCycle_isCycle) =
        singularH1ClassOfCycle X pushedDiskCycle hpushedCycle := by
    exact singularH1_inducedLinearMap_classOfCycle
      (polygon4gMkContinuousMap (g + 1))
      algebra.diskCycle algebra.diskCycle_isCycle hpushedCycle
  rw [hnat]
  rw [← singularH1ClassOfCycle_add pushedDiskCycle edgeCycle
    hpushedCycle hedgeCycle hsumCycle]
  have hpushedEq :
      pushedDiskCycle =
        lifted.projectedSubdivisionChain - algebra.projectedRepairSum := by
    exact polygon4g_repair_sum_diskCycle_chainMap_eq
      g z hz decomp lifted pairs algebra
  refine singularH1ClassOfCycle_eq_of_boundary
    hz hsumCycle (algebra.edgeChainBoundarySum - lifted.subdivisionBoundary) ?_
  calc
    K.d 2 1 (algebra.edgeChainBoundarySum - lifted.subdivisionBoundary)
        = K.d 2 1 algebra.edgeChainBoundarySum -
            K.d 2 1 lifted.subdivisionBoundary := by
            rw [map_sub]
    _ = (algebra.projectedRepairSum - edgeCycle) -
          (lifted.projectedSubdivisionChain - z) := by
          rw [algebra.projectedRepair_homologous_edge,
            lifted.subdivision_homology]
    _ = z - ((lifted.projectedSubdivisionChain -
          algebra.projectedRepairSum) + edgeCycle) := by
          abel
    _ = z - (pushedDiskCycle + edgeCycle) := by
          rw [← hpushedEq]

/--
Remaining homological-algebra bridge for the repair-sum package:
the explicit chain-boundary relations in `Polygon4gRepairSumAlgebraData`
give the desired equality in singular `H₁`.
-/
theorem polygon4g_repair_sum_projected_relation_from_algebra_data
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted)
    (algebra : Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs) :
    singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
        (singularH1ClassOfCycle DiskC algebra.diskCycle algebra.diskCycle_isCycle) +
        edgeBasisMap g algebra.edgeCoeffs := by
  rw [← edgeBasisMap_eq_homologyClass_edgeChain_sum
    g algebra.edgeCoeffs (edgeChain_sum_isCycle g algebra.edgeCoeffs)]
  exact polygon4g_repair_sum_projected_diskCycle_relation
    g z hz decomp lifted pairs algebra

/--
Atomic repair-summation leaf: sum the endpoint repairs and edge
coefficients for a finite endpoint-pair family, producing the repaired
disk-cycle relation used by the final projection step.
-/
theorem polygon4g_repair_pairs_sum_edge_coefficients
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted) :
    Nonempty (Polygon4gRepairedDiskCycleData g z hz) := by
  let algebra := polygon4g_repair_pairs_sum_algebra_data g z hz decomp lifted pairs
  exact ⟨{
    edgeCoeffs := algebra.edgeCoeffs
    diskCycle := algebra.diskCycle
    diskCycle_isCycle := algebra.diskCycle_isCycle
    projected_relation :=
      polygon4g_repair_sum_projected_relation_from_algebra_data
        g z hz decomp lifted pairs algebra
  }⟩

/--
Cycle-level lift and endpoint-repair package.  This is where the
simplex subdivision/lift data and endpoint repair data are assembled
over the finite support of the singular chain.
-/
theorem polygon4g_cycle_lift_repair_data
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0) :
    Nonempty (Polygon4gRepairedDiskCycleData g z hz) := by
  obtain ⟨decomp⟩ :=
    singularChainCoproduct_sum_support_decomposition
      (Polygon4g (g + 1)) z
  obtain ⟨lifted⟩ :=
    polygon4g_lift_data_sum_projects_to_subdivision_chain g z decomp
  obtain ⟨pairs⟩ :=
    polygon4g_cycle_endpoint_pairs_from_boundary_zero g z hz decomp lifted
  exact polygon4g_repair_pairs_sum_edge_coefficients g z hz decomp lifted pairs

/--
Projecting the repaired disk-chain relation to the quotient polygon
and killing the disk-cycle class by contractibility identifies the
original polygon cycle class with an edge-basis combination.
-/
theorem polygon4g_project_repaired_disk_cycle_to_edgeBasis
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (data : Polygon4gRepairedDiskCycleData g z hz) :
    ∃ v : Polygon4gAbelianization g,
      singularH1ClassOfCycle (Polygon4g (g + 1)) z hz = edgeBasisMap g v := by
  refine ⟨data.edgeCoeffs, ?_⟩
  rw [data.projected_relation,
    diskC_singular_one_cycle_homologyClass_eq_zero data.diskCycle data.diskCycle_isCycle]
  simp

/--
Zero homology class means an explicit singular two-boundary.

This is the concrete `ModuleCat` quotient form of first singular
homology specialized to one-cycles.
-/
theorem singularH1ClassOfCycle_eq_zero_boundary
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (h : singularH1ClassOfCycle X z hz = 0) :
    ∃ B : ((singularChainComplexZ X).sc 1).X₁,
      ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B = z := by
  let K := singularChainComplexZ X
  let S := K.sc 1
  let c : K.cycles 1 :=
    K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz
  have hπ :
      ModuleCat.Hom.hom (K.homologyπ 1) c = 0 := by
    change singularH1ClassOfCycle X z hz = 0 at h
    simpa [K, c, singularH1ClassOfCycle] using h
  have hπS :
      ModuleCat.Hom.hom S.homologyπ c = 0 := by
    simpa [S, K] using hπ
  have hq :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) = 0 := by
    have hπiso :
        ModuleCat.Hom.hom (S.homologyπ ≫ S.moduleCatHomologyIso.hom) c = 0 := by
      rw [ModuleCat.comp_apply, hπS, map_zero]
    rwa [S.π_moduleCatCyclesIso_hom] at hπiso
  have hmem :
      ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c ∈
        LinearMap.range S.moduleCatLeftHomologyData.f'.hom := by
    simpa [ShortComplex.moduleCatLeftHomologyData_π_hom] using
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range S.moduleCatLeftHomologyData.f'.hom)).1 hq
  rcases hmem with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  have hBsub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) := by
    rw [hB]
  have hcycleSub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) =
        ModuleCat.Hom.hom S.iCycles c := by
    change
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) =
        ModuleCat.Hom.hom S.iCycles c
    rw [← ModuleCat.comp_apply, S.moduleCatCyclesIso_hom_i]
  calc
    ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) := by
          change ModuleCat.Hom.hom S.f B =
            ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
              (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B)
          rw [← ModuleCat.comp_apply, S.moduleCatLeftHomologyData.f'_i]
    _ = ModuleCat.Hom.hom S.iCycles c := by
      rw [hBsub, hcycleSub]
    _ = z := by
      exact K.i_cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz

/--
Bridge from the short-complex boundary object in degree one to the
displayed degree-two singular-chain object.
-/
theorem hurewicz_singularBoundary_eq_sc_f
    (X : Type) [TopologicalSpace X] :
    let K := singularChainComplexZ X
    let S := K.sc 1
    ∀ (s : S.X₁), ∃ s' : (singularChainComplexZ X).X 2,
      S.f.hom s = ((singularChainComplexZ X).d 2 1).hom s' := by
  unfold singularChainComplexZ Polygon4gSingularC1.singularChainComplexZ
  simp +decide [AlgebraicTopology.singularChainComplexFunctor]
  unfold AlgebraicTopology.SSet.singularChainComplexFunctor
  simp +decide
  unfold AlgebraicTopology.alternatingFaceMapComplex
  unfold AlgebraicTopology.AlternatingFaceMapComplex.obj
  simp +decide [ComplexShape.down]
  unfold ChainComplex.of
  simp +decide [ComplexShape.down']
  split_ifs <;> simp_all +decide [ComplexShape.prev]
  exact fun s => ⟨_, rfl⟩

noncomputable def signedFaceTargetEdgeCoefficient
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1))) :
    ℤ := by
  classical
  exact
    ∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
        (Finset.univ : Finset (Fin 3)),
      (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) *
        if singularSimplexFace (simplex si.1) si.2 = edgeSimplex g target then
          (1 : ℤ)
        else
          0

noncomputable def edgeSimplexTargetCoefficient
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g) :
    ℤ := by
  classical
  exact
    ∑ e : Fin (2 * (g + 1)),
      v e *
        if edgeSimplex g e = edgeSimplex g target then
          (1 : ℤ)
        else
          0

/--
Concrete edge singular simplices are distinct for distinct edge indices.
-/
theorem edgeArcIdx_injective
    (g : ℕ) :
    Function.Injective (edgeArcIdx g) := by
  intro i j h
  apply Fin.ext
  unfold edgeArcIdx at h
  have hi := Nat.div_add_mod i.val 2
  have hj := Nat.div_add_mod j.val 2
  omega

/--
An arc index is one of the canonical representatives used by the
edge-basis loops.
-/
def IsCanonicalEdgeArcIdx (g : ℕ) (a : ℕ) : Prop :=
  ∃ i : Fin (2 * (g + 1)), a = edgeArcIdx g i

/--
Concrete arithmetic shape of the boundary arcs used as canonical
edge representatives: they lie in the polygon side range and occupy
residue slots `0` or `1` modulo `4`.
-/
def IsCanonicalEdgeArcResidue (g : ℕ) (a : ℕ) : Prop :=
  a < 4 * (g + 1) ∧ a % 4 < 2

/-- Canonical edge arc indices lie among the `4 * (g + 1)` polygon sides. -/
lemma IsCanonicalEdgeArcIdx.lt_four_mul
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    a < 4 * (g + 1) := by
  obtain ⟨i, rfl⟩ := ha
  unfold edgeArcIdx
  have hi := i.2
  have hdiv := Nat.div_add_mod i.val 2
  omega

/-- Canonical edge arc indices are exactly the first two side slots in each block of four. -/
lemma IsCanonicalEdgeArcIdx.mod_four_lt_two
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    a % 4 < 2 := by
  obtain ⟨i, rfl⟩ := ha
  unfold edgeArcIdx
  have hmod2 : i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- Canonical edge arc indices have the concrete residue-range shape. -/
lemma IsCanonicalEdgeArcIdx.residue
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    IsCanonicalEdgeArcResidue g a :=
  ⟨ha.lt_four_mul, ha.mod_four_lt_two⟩

/-- Every arc in the canonical residue range is represented by an edge index. -/
lemma IsCanonicalEdgeArcResidue.to_edgeArcIdx
    {g a : ℕ} (ha : IsCanonicalEdgeArcResidue g a) :
    IsCanonicalEdgeArcIdx g a := by
  refine ⟨⟨2 * (a / 4) + a % 4, ?_⟩, ?_⟩
  · have hdecomp : a = 4 * (a / 4) + a % 4 := by
      have h0 : 4 * (a / 4) + a % 4 = a := by
        simpa [Nat.mul_comm] using Nat.div_add_mod a 4
      exact h0.symm
    have hmod4 : a % 4 < 4 := Nat.mod_lt a (by norm_num : 0 < 4)
    have ha_lt : a < 4 * (g + 1) := ha.1
    have hrem_lt : a % 4 < 2 := ha.2
    have hq_lt : a / 4 < g + 1 := by
      have hblock_le : 4 * (a / 4) ≤ a := by
        omega
      omega
    have hstep : 2 * (a / 4) + a % 4 < 2 * ((a / 4) + 1) := by
      omega
    have hbound : 2 * ((a / 4) + 1) ≤ 2 * (g + 1) := by
      omega
    omega
  · unfold edgeArcIdx
    have hdiv :
        (2 * (a / 4) + a % 4) / 2 = a / 4 := by
      rw [show 2 * (a / 4) + a % 4 = a % 4 + 2 * (a / 4) by omega]
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      rw [Nat.div_eq_of_lt ha.2]
      simp
    have hmod :
        (2 * (a / 4) + a % 4) % 2 = a % 4 := by
      rw [show 2 * (a / 4) + a % 4 = a % 4 + 2 * (a / 4) by omega]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt ha.2
    change a = 4 * ((2 * (a / 4) + a % 4) / 2) +
      (2 * (a / 4) + a % 4) % 2
    rw [hdiv, hmod]
    have hdecomp : a = 4 * (a / 4) + a % 4 := by
      have h0 : 4 * (a / 4) + a % 4 = a := by
        simpa [Nat.mul_comm] using Nat.div_add_mod a 4
      exact h0.symm
    omega

/--
The source-side boundary equality for an `aᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_aPair_source_angle_eq
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t) :
    (a : ℝ) + 1 / 2 = (4 * i.val : ℝ) + t := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val) t := by
    exact congrArg Subtype.val _ha_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val) t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val) t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    positivity
  have htarget_lt_one :
      ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the source side of an `aᵢ`
pairing recovers the concrete source arc index.
-/
theorem boundary_midpoint_aPair_source_arc_index
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t) :
    a = 4 * i.val := by
  have hangle :=
    boundary_midpoint_aPair_source_angle_eq g a i t _ha _ht _ha_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have ha_lt_succ : (a : ℝ) < (4 * i.val : ℝ) + 1 := by
    linarith
  have hi_lt_succ : (4 * i.val : ℝ) < (a : ℝ) + 1 := by
    linarith
  have ha_le : a ≤ 4 * i.val := by
    by_contra hle
    have hlt : 4 * i.val < a := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 1 ≤ a := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have hi_le : 4 * i.val ≤ a := by
    by_contra hle
    have hlt : a < 4 * i.val := Nat.lt_of_not_ge hle
    have hsucc : a + 1 ≤ 4 * i.val := Nat.succ_le_of_lt hlt
    have hsuccR : (a : ℝ) + 1 ≤ (4 * i.val : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
The target-side boundary equality for an `aᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_aPair_target_angle_eq
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    (b : ℝ) + 1 / 2 = (4 * i.val + 2 : ℝ) + (1 - t) := by
  have hval :
      boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 2) (1 - t) := by
    exact congrArg Subtype.val _hb_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 2) (1 - t) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 2) (1 - t) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hb_nonneg : (0 : ℝ) ≤ ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · nlinarith
    · positivity
  have htarget_lt_one :
      ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the reversed target side of an
`aᵢ` pairing recovers the concrete target arc index.
-/
theorem boundary_midpoint_aPair_target_arc_index
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    b = 4 * i.val + 2 := by
  have hangle :=
    boundary_midpoint_aPair_target_angle_eq g b i t _hb _ht _hb_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_lt_succ :
      (b : ℝ) < (4 * i.val + 2 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 2 : ℝ) < (b : ℝ) + 1 := by
    linarith
  have hb_le : b ≤ 4 * i.val + 2 := by
    by_contra hle
    have hlt : 4 * i.val + 2 < b := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 2 + 1 ≤ b := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 2 : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 2 ≤ b := by
    by_contra hle
    have hlt : b < 4 * i.val + 2 := Nat.lt_of_not_ge hle
    have hsucc : b + 1 ≤ 4 * i.val + 2 := Nat.succ_le_of_lt hlt
    have hsuccR : (b : ℝ) + 1 ≤ (4 * i.val + 2 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
At a canonical midpoint, an `aᵢ` side-pairing source/target equality
recovers the concrete source and reversed target arc indices.
-/
theorem boundary_midpoint_aPair_arc_indices
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    a = 4 * i.val ∧ b = 4 * i.val + 2 := by
  exact ⟨
    boundary_midpoint_aPair_source_arc_index g a i t _ha _ht _ha_eq,
    boundary_midpoint_aPair_target_arc_index g b i t _hb _ht _hb_eq⟩

/--
The midpoint of a canonical-residue arc cannot be the reversed endpoint
of an `aᵢ` side-pairing generator.
-/
theorem boundary_midpoint_aPair_target_residue_absurd
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    False := by
  obtain ⟨_ha_idx, hb_idx⟩ :=
    boundary_midpoint_aPair_arc_indices
      g a b i t _ha _hb _ht _ha_eq _hb_eq
  have hb_mod : (4 * i.val + 2) % 4 < 2 := by
    simpa [hb_idx] using _hb.2
  omega

/--
The source-side boundary equality for a `bᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_bPair_source_angle_eq
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t) :
    (a : ℝ) + 1 / 2 = (4 * i.val + 1 : ℝ) + t := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 1) t := by
    exact congrArg Subtype.val _ha_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 1) t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 1) t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    positivity
  have htarget_lt_one :
      ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the source side of a `bᵢ`
pairing recovers the concrete source arc index.
-/
theorem boundary_midpoint_bPair_source_arc_index
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t) :
    a = 4 * i.val + 1 := by
  have hangle :=
    boundary_midpoint_bPair_source_angle_eq g a i t _ha _ht _ha_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have ha_lt_succ :
      (a : ℝ) < (4 * i.val + 1 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 1 : ℝ) < (a : ℝ) + 1 := by
    linarith
  have ha_le : a ≤ 4 * i.val + 1 := by
    by_contra hle
    have hlt : 4 * i.val + 1 < a := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 1 + 1 ≤ a := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 1 : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 1 ≤ a := by
    by_contra hle
    have hlt : a < 4 * i.val + 1 := Nat.lt_of_not_ge hle
    have hsucc : a + 1 ≤ 4 * i.val + 1 := Nat.succ_le_of_lt hlt
    have hsuccR : (a : ℝ) + 1 ≤ (4 * i.val + 1 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
The target-side boundary equality for a `bᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_bPair_target_angle_eq
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    (b : ℝ) + 1 / 2 = (4 * i.val + 3 : ℝ) + (1 - t) := by
  have hval :
      boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 3) (1 - t) := by
    exact congrArg Subtype.val _hb_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 3) (1 - t) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 3) (1 - t) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hb_pos : (0 : ℝ) < ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · nlinarith
    · positivity
  have htarget_le_one :
      ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) ≤ 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_le_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the reversed target side of a
`bᵢ` pairing recovers the concrete target arc index.
-/
theorem boundary_midpoint_bPair_target_arc_index
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    b = 4 * i.val + 3 := by
  have hangle :=
    boundary_midpoint_bPair_target_angle_eq g b i t _hb _ht _hb_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_lt_succ :
      (b : ℝ) < (4 * i.val + 3 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 3 : ℝ) < (b : ℝ) + 1 := by
    linarith
  have hb_le : b ≤ 4 * i.val + 3 := by
    by_contra hle
    have hlt : 4 * i.val + 3 < b := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 3 + 1 ≤ b := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 3 : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 3 ≤ b := by
    by_contra hle
    have hlt : b < 4 * i.val + 3 := Nat.lt_of_not_ge hle
    have hsucc : b + 1 ≤ 4 * i.val + 3 := Nat.succ_le_of_lt hlt
    have hsuccR : (b : ℝ) + 1 ≤ (4 * i.val + 3 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
At a canonical midpoint, a `bᵢ` side-pairing source/target equality
recovers the concrete source and reversed target arc indices.
-/
theorem boundary_midpoint_bPair_arc_indices
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    a = 4 * i.val + 1 ∧ b = 4 * i.val + 3 := by
  exact ⟨
    boundary_midpoint_bPair_source_arc_index g a i t _ha _ht _ha_eq,
    boundary_midpoint_bPair_target_arc_index g b i t _hb _ht _hb_eq⟩

/--
The midpoint of a canonical-residue arc cannot be the reversed endpoint
of a `bᵢ` side-pairing generator.
-/
theorem boundary_midpoint_bPair_target_residue_absurd
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    False := by
  obtain ⟨_ha_idx, hb_idx⟩ :=
    boundary_midpoint_bPair_arc_indices
      g a b i t _ha _hb _ht _ha_eq _hb_eq
  have hb_mod : (4 * i.val + 3) % 4 < 2 := by
    simpa [hb_idx] using _hb.2
  omega

/--
No direct side-pairing generator relates two midpoint arcs that both lie
in the canonical residue range.
-/
theorem boundary_midpoint_sideGen_residue_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Polygon4g.SideGen (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    False := by
  generalize hx :
      boundaryParam (g + 1) a (1 / 2 : ℝ) = x at _h
  generalize hy :
      boundaryParam (g + 1) b (1 / 2 : ℝ) = y at _h
  cases _h with
  | a_pair i t ht =>
      exact boundary_midpoint_aPair_target_residue_absurd
        g a b i t _ha _hb ht hx hy
  | b_pair i t ht =>
      exact boundary_midpoint_bPair_target_residue_absurd
        g a b i t _ha _hb ht hx hy

/--
The direct `EqvGen.rel` case cannot identify distinct canonical-residue
midpoint arcs once direct side-generator steps have been ruled out.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_rel_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hstep :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        False)
    (_h :
      Polygon4g.SideGen (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exfalso
  exact _hstep _ha _hb _h

/--
Equality of two canonical-residue midpoint boundary parameters recovers
the raw boundary arc index.
-/
theorem boundary_midpoint_residue_eq_of_param_eq
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) := by
    exact congrArg Subtype.val _h
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hb_nonneg : (0 : ℝ) ≤ ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hab_real : (a : ℝ) = b := by
    have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
    field_simp [hGpos.ne'] at hmul
    linarith
  exact_mod_cast hab_real

/--
The reflexive constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_refl
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hpt :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  exact boundary_midpoint_residue_eq_of_param_eq g a b _ha _hb _hpt

private theorem boundaryParam_midpoint_inj_of_lt
    (g : ℕ) {j j' : ℕ}
    (hj : j < 4 * (g + 1)) (hj' : j' < 4 * (g + 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h :
      boundaryParam (g + 1) j (1 / 2 : ℝ) =
        boundaryParam (g + 1) j' t) :
    t = 1 / 2 ∧ j = j' := by
  have hval :
      boundaryParamC' (4 * (g + 1)) j (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) j' t := by
    exact congrArg Subtype.val h
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) j (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) j' t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) j (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) j' t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((j' : ℝ) + t) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hj_pos : (0 : ℝ) < ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hj_lt_one : ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hj_succ_le : (j : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · positivity
    · positivity
  have htarget_le_one :
      ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) ≤ 1 := by
    have hj'_succ_le : (j' : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt hj')
    rw [div_le_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hreal : (j : ℝ) + 1 / 2 = (j' : ℝ) + t := by
    have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
    field_simp [hGpos.ne'] at hmul
    linarith
  have hj_eq : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsucc : j + 1 ≤ j' := Nat.succ_le_of_lt hlt
      have hsuccR : (j : ℝ) + 1 ≤ (j' : ℝ) := by exact_mod_cast hsucc
      linarith
    · have hsucc : j' + 1 ≤ j := Nat.succ_le_of_lt hgt
      have hsuccR : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hsucc
      linarith
  have ht_half : t = 1 / 2 := by
    subst hj_eq
    linarith
  exact ⟨ht_half, hj_eq⟩

private theorem boundary_midpoint_sideGen_image_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      y = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  cases h with
  | a_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val) t := by
        rw [← hx]
      obtain ⟨ht_half, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      refine ⟨4 * i.val + 2, by omega, ?_⟩
      norm_num [ht_half]
  | b_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 1) t := by
        rw [← hx]
      obtain ⟨ht_half, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      refine ⟨4 * i.val + 3, by omega, ?_⟩
      norm_num [ht_half]

private theorem boundary_midpoint_sideGen_preimage_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hy : y = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      x = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  cases h with
  | a_pair i t ht =>
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 2) (1 - t) := by
        rw [← hy]
      obtain ⟨hone_minus_t, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht_rev hy_param
      have ht_half : t = 1 / 2 := by linarith
      refine ⟨4 * i.val, by omega, ?_⟩
      simp [ht_half]
  | b_pair i t ht =>
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 3) (1 - t) := by
        rw [← hy]
      obtain ⟨hone_minus_t, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht_rev hy_param
      have ht_half : t = 1 / 2 := by linarith
      refine ⟨4 * i.val + 1, by omega, ?_⟩
      simp [ht_half]

private theorem boundary_midpoint_eqvGen_image_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      y = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  have midpoint_iff :
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          x = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            y = boundaryParam (g + 1) k (1 / 2 : ℝ)) ∧
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          y = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            x = boundaryParam (g + 1) k (1 / 2 : ℝ)) := by
    clear hj hx
    induction h with
    | refl p =>
        exact ⟨
          (fun hj hp => ⟨_, hj, hp⟩),
          (fun hj hp => ⟨_, hj, hp⟩)⟩
    | rel p q hrel =>
        exact ⟨
          (fun hj hp => boundary_midpoint_sideGen_image_is_midpoint g hrel hj hp),
          (fun hj hq => boundary_midpoint_sideGen_preimage_is_midpoint g hrel hj hq)⟩
    | symm p q _ ih =>
        exact ⟨ih.2, ih.1⟩
    | trans p mid q _ _ ih_left ih_right =>
        exact ⟨
          (fun hj hp => by
            obtain ⟨m, hm, hmid⟩ := ih_left.1 hj hp
            exact ih_right.1 hm hmid),
          (fun hj hq => by
            obtain ⟨m, hm, hmid⟩ := ih_right.2 hj hq
            exact ih_left.2 hm hmid)⟩
  exact midpoint_iff.1 hj hx

private theorem boundary_midpoint_eqvGen_preimage_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hy : y = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      x = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  have midpoint_iff :
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          x = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            y = boundaryParam (g + 1) k (1 / 2 : ℝ)) ∧
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          y = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            x = boundaryParam (g + 1) k (1 / 2 : ℝ)) := by
    clear hj hy
    induction h with
    | refl p =>
        exact ⟨
          (fun hj hp => ⟨_, hj, hp⟩),
          (fun hj hp => ⟨_, hj, hp⟩)⟩
    | rel p q hrel =>
        exact ⟨
          (fun hj hp => boundary_midpoint_sideGen_image_is_midpoint g hrel hj hp),
          (fun hj hq => boundary_midpoint_sideGen_preimage_is_midpoint g hrel hj hq)⟩
    | symm p q _ ih =>
        exact ⟨ih.2, ih.1⟩
    | trans p mid q _ _ ih_left ih_right =>
        exact ⟨
          (fun hj hp => by
            obtain ⟨m, hm, hmid⟩ := ih_left.1 hj hp
            exact ih_right.1 hm hmid),
          (fun hj hq => by
            obtain ⟨m, hm, hmid⟩ := ih_right.2 hj hq
            exact ih_left.2 hm hmid)⟩
  exact midpoint_iff.2 hj hy

private def boundaryMidpointCanonicalRep (n : ℕ) : ℕ :=
  if n % 4 < 2 then n else n - 2

private theorem boundaryMidpointCanonicalRep_of_residue
    {g n : ℕ} (hn : IsCanonicalEdgeArcResidue g n) :
    boundaryMidpointCanonicalRep n = n := by
  simp [boundaryMidpointCanonicalRep, hn.2]

private theorem boundary_midpoint_sideGen_canonicalRep_eq
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j k : ℕ} (hj : j < 4 * (g + 1)) (hk : k < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ))
    (hy : y = boundaryParam (g + 1) k (1 / 2 : ℝ)) :
    boundaryMidpointCanonicalRep j = boundaryMidpointCanonicalRep k := by
  cases h with
  | a_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val) t := by
        rw [← hx]
      obtain ⟨ht_half, hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) k (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 2) (1 - t) := by
        rw [← hy]
      obtain ⟨_hone_minus_t, hk_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hk (by omega) ht_rev hy_param
      rw [hj_eq, hk_eq]
      simp [boundaryMidpointCanonicalRep]
  | b_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 1) t := by
        rw [← hx]
      obtain ⟨ht_half, hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) k (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 3) (1 - t) := by
        rw [← hy]
      obtain ⟨_hone_minus_t, hk_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hk (by omega) ht_rev hy_param
      rw [hj_eq, hk_eq]
      simp [boundaryMidpointCanonicalRep]

private theorem boundary_midpoint_eqvGen_canonicalRep_eq
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j k : ℕ} (hj : j < 4 * (g + 1)) (hk : k < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ))
    (hy : y = boundaryParam (g + 1) k (1 / 2 : ℝ)) :
    boundaryMidpointCanonicalRep j = boundaryMidpointCanonicalRep k := by
  revert j k
  induction h with
  | refl p =>
      intro j k hj hk hx hy
      have hidx :=
        boundaryParam_midpoint_inj_of_lt g hj hk
          (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
          (by rw [← hx, ← hy])
      simp [hidx.2]
  | rel p q hrel =>
      intro j k hj hk hx hy
      exact boundary_midpoint_sideGen_canonicalRep_eq g hrel hj hk hx hy
  | symm p q _ ih =>
      intro j k hj hk hx hy
      exact (ih hk hj hy hx).symm
  | trans p mid q hpq hqr ih_left ih_right =>
      intro j k hj hk hx hy
      obtain ⟨m, hm, hmid⟩ :=
        boundary_midpoint_eqvGen_image_is_midpoint g hpq hj hx
      exact (ih_left hj hm hx hmid).trans (ih_right hm hk hmid hy)

theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    {g : ℕ} {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {a b : ℕ}
    (ha : IsCanonicalEdgeArcResidue g a)
    (hb : IsCanonicalEdgeArcResidue g b)
    (hxa : x = boundaryParam (g + 1) a (1 / 2 : ℝ))
    (hyb : y = boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  have hrep :=
    boundary_midpoint_eqvGen_canonicalRep_eq g h ha.1 hb.1 hxa hyb
  simpa [boundaryMidpointCanonicalRep_of_residue ha,
    boundaryMidpointCanonicalRep_of_residue hb] using hrep

/--
The remaining reversed-closure content for the symmetric constructor case.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm_core
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))) :
    a = b := by
  exact (boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    _h _hb _ha rfl rfl).symm

/--
The symmetric constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm_core
    g a b _ha _hb _h

/--
The transitive constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_trans
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (mid : DiskC)
    (_hleft :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ)) mid)
    (_hright :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        mid (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    (Relation.EqvGen.trans _ _ _ _hleft _hright) _ha _hb rfl rfl

/--
The remaining transitive-closure content for midpoint `EqvGen` separation,
assuming the one-step canonical-residue midpoint case has already been
handled.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_closure
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hrel :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        a = b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  generalize hx :
      boundaryParam (g + 1) a (1 / 2 : ℝ) = x at _h
  generalize hy :
      boundaryParam (g + 1) b (1 / 2 : ℝ) = y at _h
  cases _h with
  | refl p =>
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_refl g a b _ha _hb
        (by rw [hx, hy])
  | rel p q hrel =>
      rw [← hx, ← hy] at hrel
      exact _hrel _ha _hb hrel
  | symm p q hrel =>
      rw [← hy, ← hx] at hrel
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm
        g a b _ha _hb hrel
  | trans p mid q hleft hright =>
      rw [← hx] at hleft
      rw [← hy] at hright
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_trans
        g a b _ha _hb mid hleft hright

/--
Midpoint `EqvGen` separation for canonical-residue arcs, assuming the
direct side-generator obstruction for canonical-residue endpoints.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_and_sideGen_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hstep :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        False)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_closure g a b _ha _hb
    (fun ha hb hrel =>
      boundary_midpoint_sideRel_residue_eq_of_eqvGen_rel_absurd
        g _ _ ha hb _hstep hrel)
    _h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_and_sideGen_absurd
    g a b _ha _hb
    (fun ha hb hstep =>
      boundary_midpoint_sideGen_residue_absurd g _ _ ha hb hstep)
    _h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_residue_eq
    (g : ℕ) (a b : ℕ)
    (ha : IsCanonicalEdgeArcResidue g a)
    (hb : IsCanonicalEdgeArcResidue g b)
    (h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen g a b ha hb h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_canonical_residue_eq
    (g : ℕ) (a b : ℕ)
    (ha_lt : a < 4 * (g + 1)) (ha_mod : a % 4 < 2)
    (hb_lt : b < 4 * (g + 1)) (hb_mod : b % 4 < 2)
    (h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq g a b
    ⟨ha_lt, ha_mod⟩ ⟨hb_lt, hb_mod⟩ h

/--
Midpoint `SideRel` between two canonical boundary-arc indices forces
the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_isCanonicalArc_eq
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcIdx g a)
    (_hb : IsCanonicalEdgeArcIdx g b)
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_canonical_residue_eq g a b
    _ha.lt_four_mul _ha.mod_four_lt_two _hb.lt_four_mul _hb.mod_four_lt_two _h

/--
Midpoint `SideRel` between two canonical boundary-arc indices forces
the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_canonical_arc_eq
    (g : ℕ) (a b : ℕ)
    (_ha : ∃ i : Fin (2 * (g + 1)), a = edgeArcIdx g i)
    (_hb : ∃ j : Fin (2 * (g + 1)), b = edgeArcIdx g j)
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_isCanonicalArc_eq g a b _ha _hb _h

/--
The side-pairing relation at midpoints of canonical boundary-edge
representatives separates the edge-basis arc index.
-/
theorem edgeArcIdx_eq_of_boundary_midpoint_sideRel
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ))
        (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))) :
    edgeArcIdx g i = edgeArcIdx g j := by
  exact boundary_midpoint_sideRel_canonical_arc_eq g
    (edgeArcIdx g i) (edgeArcIdx g j) ⟨i, rfl⟩ ⟨j, rfl⟩ _h

/--
The quotient midpoint of a canonical boundary-edge representative
separates the edge-basis arc index.
-/
theorem edgeArcIdx_eq_of_boundary_midpoint_mk_eq
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (h :
      Polygon4g.mk (g + 1)
          (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ)) =
        Polygon4g.mk (g + 1)
          (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))) :
    edgeArcIdx g i = edgeArcIdx g j := by
  exact edgeArcIdx_eq_of_boundary_midpoint_sideRel g
    ((Polygon4g.mk_eq_mk_iff (g + 1)
      (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ))
      (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))).mp h)

/--
Equality of concrete edge interval maps determines the boundary arc
index used by the parametrization.
-/
theorem edgeArcIdx_eq_of_edgeContMap_eq
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (h : edgeContMap g i = edgeContMap g j) :
    edgeArcIdx g i = edgeArcIdx g j := by
  apply edgeArcIdx_eq_of_boundary_midpoint_mk_eq g
  let mid : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩
  have happ := congrFun (congrArg DFunLike.coe h) mid
  simpa [edgeContMap, mid] using happ

/--
Concrete edge interval maps are distinct for distinct edge indices.
-/
theorem edgeContMap_injective
    (g : ℕ) :
    Function.Injective (edgeContMap g) := by
  intro i j h
  exact edgeArcIdx_injective g (edgeArcIdx_eq_of_edgeContMap_eq g h)

/--
Concrete edge singular simplices are distinct for distinct edge indices.
-/
theorem edgeSimplex_injective
    (g : ℕ) :
    Function.Injective (edgeSimplex g) := by
  intro i j h
  apply edgeContMap_injective g
  ext t
  let s : stdSimplex ℝ (Fin 2) := stdSimplexHomeomorphUnitInterval.symm t
  have hs : stdSimplexToUnitInterval s = t := by
    exact stdSimplexHomeomorphUnitInterval.apply_symm_apply t
  have happ := congrFun (congrArg DFunLike.coe h) s
  simpa [edgeSimplex, s, hs] using happ

/--
Reading the coefficient of the target concrete edge simplex in a chain
equality between signed face terms and the concrete edge-simplex sum
identifies the explicit face coefficient with the corresponding
coefficient of the edge-simplex sum.
-/
theorem signedFaceTargetEdgeCoefficient_eq_edgeSimplexTargetCoefficient_of_sum
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (_hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex =
      edgeSimplexTargetCoefficient g target v := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of (Polygon4g (g + 1)))).obj (op ⦋1⦌)
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let targetIdx : I := singularChainSimplexIndex (Polygon4g (g + 1)) 1
    (edgeSimplex g target)
  let coeffAt : SingularChainCoproduct (Polygon4g (g + 1)) 1 →ₗ[ℤ] ℤ :=
    (DirectSum.component ℤ I (fun _ : I => ℤ) targetIdx).comp iso.hom.hom
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hcoeff := congrArg coeffAt _hB
  have hleft :
      coeffAt
        (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        signedFaceTargetEdgeCoefficient g target Simplex coeff simplex := by
    simp [signedFaceTargetEdgeCoefficient, coeffAt, targetIdx,
      singularChainElement, I, Z, iso, hι, map_sum, DirectSum.component.of]
  have hright :
      coeffAt
        (∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        edgeSimplexTargetCoefficient g target v := by
    simp [edgeSimplexTargetCoefficient, coeffAt, targetIdx,
      singularChainElement, I, Z, iso, hι, map_sum, DirectSum.component.of]
  rw [hleft, hright] at hcoeff
  exact hcoeff

/--
The target coefficient of the concrete edge-simplex sum is the target
coordinate of the coefficient vector.
-/
theorem edgeSimplexTargetCoefficient_eq_of_injective
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (hinj : Function.Injective (edgeSimplex g)) :
    edgeSimplexTargetCoefficient g target v = v target := by
  classical
  unfold edgeSimplexTargetCoefficient
  calc
    (∑ e : Fin (2 * (g + 1)),
        v e *
          if edgeSimplex g e = edgeSimplex g target then
            (1 : ℤ)
          else
            0) =
        v target *
          if edgeSimplex g target = edgeSimplex g target then
            (1 : ℤ)
          else
            0 := by
        apply Finset.sum_eq_single target
        · intro e _he hne
          have hneq : edgeSimplex g e ≠ edgeSimplex g target := by
            intro h
            exact hne (hinj h)
          simp [hneq]
        · intro htarget
          simp at htarget
    _ = v target := by
      simp

/--
The target coefficient of the concrete edge-simplex sum is the target
coordinate of the coefficient vector.
-/
theorem edgeSimplexTargetCoefficient_eq
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g) :
    edgeSimplexTargetCoefficient g target v = v target :=
  edgeSimplexTargetCoefficient_eq_of_injective g target v (edgeSimplex_injective g)

/--
Reading the coefficient of the target concrete edge simplex in a chain
equality between signed face terms and the concrete edge-simplex sum
gives the corresponding coordinate of the edge vector.
-/
theorem signedFaceTargetEdgeCoefficient_eq_of_edgeSimplex_sum
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = v target := by
  rw [signedFaceTargetEdgeCoefficient_eq_edgeSimplexTargetCoefficient_of_sum
    g target v Simplex coeff simplex hB]
  exact edgeSimplexTargetCoefficient_eq g target v

/-- Read an explicit target-edge cancellation input as the zero statement. -/
theorem signedFaceTargetEdgeCoefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0 :=
  hcancel

/--
Scalar target-edge coefficient comparison for a finite signed face sum.

The fields are stated directly for the explicit signed count of those
face terms whose induced one-simplex is the target concrete edge
simplex. The `targetCoeff_eq` field says that reading this coefficient
in the chain equality gives `v target`, and `targetCoeff_zero` is the
remaining geometric assertion that this coefficient vanishes for the
signed face-boundary sum.
-/
structure EdgeBoundarySignedFaceCoefficientComparison
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1))) where
  targetCoeff_eq :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = v target
  targetCoeff_zero :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0

/--
Construct the scalar coefficient comparison data for the target edge
from equality of a signed face-boundary sum with an edge-simplex sum.
-/
theorem edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_coefficient_comparison
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (_hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    Nonempty
      (EdgeBoundarySignedFaceCoefficientComparison
        g target v Simplex coeff simplex) := by
  exact
    ⟨{
      targetCoeff_eq :=
        signedFaceTargetEdgeCoefficient_eq_of_edgeSimplex_sum
          g target v Simplex coeff simplex _hB
      targetCoeff_zero :=
        signedFaceTargetEdgeCoefficient_zero
          g target Simplex coeff simplex hcancel
    }⟩

/--
Finite individual-face coefficient form with combined signed integer
coefficients.

This is the local geometric leaf after each face term has one integer
coefficient rather than nested scalar actions.
-/
theorem edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  obtain ⟨data⟩ :=
    edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_coefficient_comparison
      g target v Simplex coeff simplex hcancel hB
  rw [← data.targetCoeff_eq]
  exact data.targetCoeff_zero

/--
Finite individual-face coefficient form against explicit edge simplex
generators.

This is the local geometric leaf after flattening the finite
two-simplex boundary sum into its signed one-face terms.
-/
theorem edgeChain_sum_singular_boundary_face_terms_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
        (Finset.univ : Finset (Fin 3)),
        (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
          (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
        refine Finset.sum_congr rfl ?_
        intro si _hsi
        rw [mul_zsmul]
    _ = ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1) := hB

/--
Finite face-sum coefficient form against explicit edge simplex
generators.

This is the local geometric leaf after expanding the right-hand edge
chains to the singular one-simplices that generate them.
-/
theorem edgeChain_sum_singular_boundary_faces_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_face_terms_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
        symm
        calc
          (∑ s : Simplex, coeff s •
              (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
                (singularChainElement (singularSimplexFace (simplex s) i) :
                  SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
              ∑ s : Simplex, ∑ i : Fin 3,
                coeff s • (((-1 : ℤ) ^ (i : ℕ)) •
                  (singularChainElement (singularSimplexFace (simplex s) i) :
                    SingularChainCoproduct (Polygon4g (g + 1)) 1)) := by
              refine Finset.sum_congr rfl ?_
              intro s _hs
              exact (Finset.sum_zsmul
                (fun i : Fin 3 =>
                  ((-1 : ℤ) ^ (i : ℕ)) •
                    (singularChainElement (singularSimplexFace (simplex s) i) :
                      SingularChainCoproduct (Polygon4g (g + 1)) 1))
                Finset.univ (coeff s)).symm
          _ = (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
                  (Finset.univ : Finset (Fin 3)),
                coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
                  (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
                    SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
              rw [← Finset.sum_product']
    _ = ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1) := hB

/--
Finite face-sum coefficient form of edge-chain singular-boundary
independence.

This is the local geometric leaf after expanding each singular
two-simplex boundary into its alternating face sum.
-/
theorem edgeChain_sum_singular_boundary_faces_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_faces_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  simpa [edgeChain] using hB

/--
Finite-simplex coefficient form of edge-chain singular-boundary
independence.

This is the local finite-support leaf behind the concrete singular
two-boundary statement: a finite integral combination of singular
two-simplex boundaries cannot equal a nonzero target edge combination.
-/
theorem edgeChain_sum_singular_boundary_decomposition_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom
            (singularChainElement (simplex s))) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_faces_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ s : Simplex, coeff s •
        (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
          (singularChainElement (singularSimplexFace (simplex s) i) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ s : Simplex, coeff s •
          ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom
            (singularChainElement (simplex s)) := by
        refine Finset.sum_congr rfl ?_
        intro s _hs
        rw [singularChainElement_boundary_decomposition
          (Polygon4g (g + 1)) 1 (simplex s)]
    _ = ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := hB

/--
Architectural axiom: edge-chain singular-boundary independence.

If a singular 2-chain `B` has boundary
`∂B = ∑ e, v e • edgeChain g e`, then each target coordinate of `v`
vanishes. This is the homological fact that the concrete polygon edge
chains form the free basis of `H₁ (Polygon4g (g + 1); ℤ)`, specialized to
one coordinate.

This replaces the previously circular substrate axiom
`signedFaceTargetEdgeCoefficient_zero_of_singular_boundary`: `d ∘ d = 0`
only proves the signed face one-chain is a cycle, not that a particular
edge coefficient in that cycle is zero.
-/
theorem edgeChain_sum_singular_boundary_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (B : (singularChainComplexZ (Polygon4g (g + 1))).X 2)
    (hB :
      ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom B =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  sorry

/--
Pointwise coefficient form of edge-chain boundary independence.

This is the remaining scalar-coordinate geometric input needed for
edge independence: if a singular two-boundary is a finite sum of
concrete edge chains, then the coefficient of each target edge is zero.
-/
theorem edgeChain_sum_boundary_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (B : ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).X₁)
    (hB :
      ModuleCat.Hom.hom (((singularChainComplexZ (Polygon4g (g + 1))).sc 1).f) B =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  obtain ⟨B', hB'⟩ :=
    hurewicz_singularBoundary_eq_sc_f (Polygon4g (g + 1)) B
  exact
    edgeChain_sum_singular_boundary_scalar_coefficient_zero
      g target v B' (hB' ▸ hB)

/--
Kernel-zero form of edge independence.

This is the primitive edge-chain theorem still needed for injectivity:
an integral combination of polygon edge cycles with zero singular
homology class has all coefficients zero.
-/
theorem edgeChain_sum_boundary_coefficients_zero
    (g : ℕ) (v : Polygon4gAbelianization g)
    (B : ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).X₁)
    (hB :
      ModuleCat.Hom.hom (((singularChainComplexZ (Polygon4g (g + 1))).sc 1).f) B =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v = 0 := by
  funext target
  exact edgeChain_sum_boundary_scalar_coefficient_zero g target v B hB

/--
Homology-kernel form of edge independence, reduced to the concrete
boundary statement `edgeChain_sum_boundary_coefficients_zero`.
-/
theorem edgeChain_sum_homologyClass_eq_zero_coefficients_zero
    (g : ℕ) (v : Polygon4gAbelianization g)
    (h :
      singularH1ClassOfCycle (Polygon4g (g + 1))
        (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e)
        (edgeChain_sum_isCycle g v) = 0) :
    v = 0 := by
  obtain ⟨B, hB⟩ :=
    singularH1ClassOfCycle_eq_zero_boundary (Polygon4g (g + 1))
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e)
      (edgeChain_sum_isCycle g v) h
  exact edgeChain_sum_boundary_coefficients_zero g v B hB

/--
Kernel-zero form of edge independence for the linear edge-basis map.

The actual geometric input is
`edgeChain_sum_homologyClass_eq_zero_coefficients_zero`; this theorem
is now just the rewrite between the linear map and the homology class
of the corresponding finite edge-chain sum.
-/
theorem edgeBasisMap_eq_zero_coefficients_zero
    (g : ℕ) (v : Polygon4gAbelianization g)
    (h : edgeBasisMap g v = 0) :
    v = 0 := by
  apply edgeChain_sum_homologyClass_eq_zero_coefficients_zero g v
  rw [edgeBasisMap_eq_homologyClass_edgeChain_sum
    g v (edgeChain_sum_isCycle g v)]
  exact h

/--
Uniqueness of the edge coefficients produced by the repaired disk-cycle
package.

This is the remaining local independence theorem for the explicit
polygon repair construction: a repaired representative whose projected
class is also represented by another edge-basis coefficient vector must
have exactly that coefficient vector.
-/
theorem polygon4g_repaired_edgeCoeffs_unique
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (data : Polygon4gRepairedDiskCycleData g z hz)
    (v : Polygon4gAbelianization g)
    (h :
      singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
        edgeBasisMap g v) :
    data.edgeCoeffs = v := by
  have hdata :
      singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
        edgeBasisMap g data.edgeCoeffs := by
    rw [data.projected_relation,
      diskC_singular_one_cycle_homologyClass_eq_zero data.diskCycle data.diskCycle_isCycle]
    simp
  have heq : edgeBasisMap g data.edgeCoeffs = edgeBasisMap g v := by
    rw [← hdata, h]
  have hzero : edgeBasisMap g (data.edgeCoeffs - v) = 0 := by
    rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp (edgeBasisMap_eq_zero_coefficients_zero g
    (data.edgeCoeffs - v) hzero)

/--
Polygon cellular approximation in degree one: every singular
one-cycle on `Polygon4g (g+1)` is homologous to a concrete integral
combination of the polygon edge loops.

This is now an assembly from the lift/repair package and the projection
package.
-/
theorem polygon4g_cycle_homologous_to_edge_chain
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0) :
    ∃ v : Polygon4gAbelianization g,
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ (Polygon4g (g + 1))).homologyπ 1))
        ((singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz) =
        edgeBasisMap g v := by
  obtain ⟨data⟩ := polygon4g_cycle_lift_repair_data g z hz
  exact polygon4g_project_repaired_disk_cycle_to_edgeBasis g z hz data

/-- Edge-loop classes span Mathlib singular `H₁` of the polygon quotient. -/
theorem edgeBasisMap_surjective (g : ℕ) :
    Function.Surjective (edgeBasisMap g) := by
  intro y
  obtain ⟨z, hz, hy⟩ :=
    singularH1_exists_cycle_repr (Polygon4g (g + 1)) y
  obtain ⟨v, hv⟩ := polygon4g_cycle_homologous_to_edge_chain g z hz
  refine ⟨v, ?_⟩
  rw [← hy]
  exact hv.symm

/-- Edge-chain finite sums are additive in their coefficient vector. -/
theorem edgeChain_sum_add
    (g : ℕ) (v w : Polygon4gAbelianization g) :
    (∑ e : Fin (2 * (g + 1)), (v + w) e • edgeChain g e) =
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) +
        ∑ e : Fin (2 * (g + 1)), w e • edgeChain g e := by
  calc
    ∑ e : Fin (2 * (g + 1)), (v + w) e • edgeChain g e
        =
      ∑ e : Fin (2 * (g + 1)),
        (v e • edgeChain g e + w e • edgeChain g e) := by
        refine Finset.sum_congr rfl ?_
        intro e _he
        rw [Pi.add_apply, add_zsmul]
    _ = (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) +
        ∑ e : Fin (2 * (g + 1)), w e • edgeChain g e := by
        rw [Finset.sum_add_distrib]

/-- Edge-chain finite sums are compatible with integer scaling. -/
theorem edgeChain_sum_zsmul
    (g : ℕ) (n : ℤ) (v : Polygon4gAbelianization g) :
    (∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e) =
      n • ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := by
  calc
    ∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e
        =
      ∑ e : Fin (2 * (g + 1)), n • (v e • edgeChain g e) := by
        refine Finset.sum_congr rfl ?_
        intro e _he
        change (n * v e) • edgeChain g e = n • (v e • edgeChain g e)
        rw [mul_zsmul]
    _ = n • ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := by
        exact Finset.sum_zsmul
          (fun e : Fin (2 * (g + 1)) => v e • edgeChain g e)
          Finset.univ n

/-- The zero coefficient vector realizes the zero edge-chain sum. -/
theorem edgeChain_sum_zero (g : ℕ) :
    (∑ e : Fin (2 * (g + 1)),
        (0 : Polygon4gAbelianization g) e • edgeChain g e) = 0 := by
  change (∑ e : Fin (2 * (g + 1)), (0 : ℤ) • edgeChain g e) = 0
  exact Finset.sum_eq_zero (fun e _ => zero_smul ℤ (edgeChain g e))

/-- Edge-chain finite sums are compatible with negation. -/
theorem edgeChain_sum_neg
    (g : ℕ) (v : Polygon4gAbelianization g) :
    (∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e) =
      -∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := by
  calc
    ∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e
        =
      ∑ e : Fin (2 * (g + 1)), -(v e • edgeChain g e) := by
        refine Finset.sum_congr rfl ?_
        intro e _he
        rw [Pi.neg_apply, neg_zsmul]
    _ = -∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := by
        rw [Finset.sum_neg_distrib]

/-- Edge-chain finite sums are compatible with subtraction. -/
theorem edgeChain_sum_sub
    (g : ℕ) (v w : Polygon4gAbelianization g) :
    (∑ e : Fin (2 * (g + 1)), (v - w) e • edgeChain g e) =
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) -
        ∑ e : Fin (2 * (g + 1)), w e • edgeChain g e := by
  calc
    ∑ e : Fin (2 * (g + 1)), (v - w) e • edgeChain g e
        =
      ∑ e : Fin (2 * (g + 1)), (v + -w) e • edgeChain g e := by
        rfl
    _ = (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) +
        ∑ e : Fin (2 * (g + 1)), (-w) e • edgeChain g e := by
        exact edgeChain_sum_add g v (-w)
    _ = (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) -
        ∑ e : Fin (2 * (g + 1)), w e • edgeChain g e := by
        rw [edgeChain_sum_neg, sub_eq_add_neg]

/-- Edge-chain cycles are additive in their coefficient vector. -/
theorem edgeChain_cyclesMk_add
    (g : ℕ) (v w : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (v + w) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (v + w)) =
      (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) +
        (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), w e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g w) := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
  change
    ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), (v + w) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (v + w))) =
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g v) +
          K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), w e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g w))
  rw [K.i_cyclesMk, map_add, K.i_cyclesMk, K.i_cyclesMk]
  exact edgeChain_sum_add g v w

/-- Edge-chain cycles are compatible with integer scaling. -/
theorem edgeChain_cyclesMk_zsmul
    (g : ℕ) (n : ℤ) (v : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (n • v)) =
      n • (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
  change
    (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (n • v))) =
      (ConcreteCategory.hom (K.iCycles 1))
        (n • K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v))
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (n • v))) =
        ∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e by
        exact K.i_cyclesMk
          (∑ e : Fin (2 * (g + 1)), (n • v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (n • v))]
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (n • K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)) =
        n • (ConcreteCategory.hom (K.iCycles 1))
          (K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g v)) by
        exact map_zsmul (ConcreteCategory.hom (K.iCycles 1)) n
          (K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g v))]
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e by
        exact K.i_cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)]
  exact edgeChain_sum_zsmul g n v

/-- The zero coefficient vector realizes the zero edge-chain cycle. -/
theorem edgeChain_cyclesMk_zero (g : ℕ) :
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)),
          (0 : Polygon4gAbelianization g) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g 0) = 0 := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
  change
    (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)),
            (0 : Polygon4gAbelianization g) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g 0)) =
      (ConcreteCategory.hom (K.iCycles 1)) 0
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)),
            (0 : Polygon4gAbelianization g) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g 0)) =
        ∑ e : Fin (2 * (g + 1)),
          (0 : Polygon4gAbelianization g) e • edgeChain g e by
        exact K.i_cyclesMk
          (∑ e : Fin (2 * (g + 1)),
            (0 : Polygon4gAbelianization g) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g 0)]
  rw [map_zero]
  exact edgeChain_sum_zero g

/-- Edge-chain cycles are compatible with negation. -/
theorem edgeChain_cyclesMk_neg
    (g : ℕ) (v : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (-v)) =
      - (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
  change
    (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (-v))) =
      (ConcreteCategory.hom (K.iCycles 1))
        (-K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v))
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (-v))) =
        ∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e by
        exact K.i_cyclesMk
          (∑ e : Fin (2 * (g + 1)), (-v) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (-v))]
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (-K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)) =
        - (ConcreteCategory.hom (K.iCycles 1))
          (K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g v)) by
        exact map_neg (ConcreteCategory.hom (K.iCycles 1))
          (K.cyclesMk
            (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
            (edgeChain_sum_isCycle g v))]
  rw [show
      (ConcreteCategory.hom (K.iCycles 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e by
        exact K.i_cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)]
  exact edgeChain_sum_neg g v

/-- Edge-chain cycles are compatible with subtraction. -/
theorem edgeChain_cyclesMk_sub
    (g : ℕ) (v w : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (v - w) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (v - w)) =
      (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) -
        (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), w e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g w) := by
  calc
    (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (v - w) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (v - w))
        =
      (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), (v + -w) e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g (v + -w)) := by
        rfl
    _ =
      (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) +
        (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), (-w) e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g (-w)) := by
        exact edgeChain_cyclesMk_add g v (-w)
    _ =
      (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v) -
        (singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), w e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g w) := by
        rw [edgeChain_cyclesMk_neg, sub_eq_add_neg]

/--
Cycle-level coefficient extractor for the edge basis.

This is the non-circular input needed for edge independence: define
edge coefficients on actual singular one-cycles, prove all singular
two-boundaries have coefficient zero, and prove the extractor reads a
finite edge-chain combination as its original coefficient vector.
-/
structure EdgeCoefficientCycleFunctionalData (g : ℕ) where
  coeffCycles :
    (singularChainComplexZ (Polygon4g (g + 1))).cycles 1 ⟶
      ModuleCat.of ℤ (Polygon4gAbelianization g)
  coeffCycles_boundary_zero :
    ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).toCycles ≫
      coeffCycles = 0
  coeffCycles_edge_sum :
    ∀ v : Polygon4gAbelianization g,
      coeffCycles.hom
        ((singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v)) = v

/--
Chosen edge-coefficient value of a singular one-cycle.

This is the pointwise coefficient extraction coming from the explicit
lift/repair package; linearity and boundary-invariance are separated
below as named proof obligations.
-/
noncomputable def edgeCoefficientCycleValue
    (g : ℕ)
    (c : (singularChainComplexZ (Polygon4g (g + 1))).cycles 1) :
    Polygon4gAbelianization g := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let z : SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    (ConcreteCategory.hom (K.iCycles 1)) c
  have hz : K.d 1 0 z = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
        (((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) c) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, K.iCycles_d]
    simp
  exact (Classical.choice (polygon4g_cycle_lift_repair_data g z hz)).edgeCoeffs

/--
The chosen edge-coefficient value represents the same singular homology
class as the input cycle.

This is the sorry-free consequence of the lift/repair package.  The
remaining pointwise coefficient facts are precisely the uniqueness
statements needed to read this representative equality back as equality
of coefficient vectors.
-/
theorem edgeCoefficientCycleValue_homologyClass
    (g : ℕ)
    (c : (singularChainComplexZ (Polygon4g (g + 1))).cycles 1) :
    ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ (Polygon4g (g + 1))).homologyπ 1)) c =
      edgeBasisMap g (edgeCoefficientCycleValue g c) := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let z : SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    (ConcreteCategory.hom (K.iCycles 1)) c
  have hz : K.d 1 0 z = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
        (((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) c) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, K.iCycles_d]
    simp
  let data := Classical.choice (polygon4g_cycle_lift_repair_data g z hz)
  have hcycles :
      K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz =
        c := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    simpa [K, z] using
      (K.i_cyclesMk z 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)
  have hclass :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1))
          (K.cyclesMk z 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz) =
        edgeBasisMap g data.edgeCoeffs := by
    change singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
      edgeBasisMap g data.edgeCoeffs
    rw [data.projected_relation,
      diskC_singular_one_cycle_homologyClass_eq_zero data.diskCycle data.diskCycle_isCycle]
    simp
  simpa [K, edgeCoefficientCycleValue, z, hz, data, hcycles] using hclass

/--
For a singular two-boundary, the chosen edge coefficients map to zero
in homology under `edgeBasisMap`.
-/
theorem edgeCoefficientCycleValue_boundary_edgeBasis_zero
    (g : ℕ)
    (x : ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).X₁) :
    edgeBasisMap g
      (edgeCoefficientCycleValue g
        (((singularChainComplexZ (Polygon4g (g + 1))).sc 1).toCycles.hom x)) = 0 := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let c : K.cycles 1 := ((K.sc 1).toCycles).hom x
  have hclass := edgeCoefficientCycleValue_homologyClass g c
  have hzero :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) c = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map
        ((K.sc 1).toCycles ≫ K.homologyπ 1)) x = 0
    rw [show (K.sc 1).toCycles ≫ K.homologyπ 1 = 0 by
      set_option linter.unnecessarySimpa false in
      simpa [HomologicalComplex.homologyπ] using
        (K.sc 1).toCycles_comp_homologyπ]
    simp
  rw [← hclass]
  simpa [K, c] using hzero

/--
For a finite edge-chain cycle, the chosen edge coefficients represent
the same edge-basis homology class as the input coefficient vector.
-/
theorem edgeCoefficientCycleValue_edge_sum_edgeBasis
    (g : ℕ) (v : Polygon4gAbelianization g) :
    edgeBasisMap g
      (edgeCoefficientCycleValue g
        ((singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v))) =
      edgeBasisMap g v := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let c : K.cycles 1 :=
    K.cyclesMk
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
      (edgeChain_sum_isCycle g v)
  have hclass := edgeCoefficientCycleValue_homologyClass g c
  have hedge :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) c =
        edgeBasisMap g v := by
    change singularH1ClassOfCycle (Polygon4g (g + 1))
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e)
      (edgeChain_sum_isCycle g v) = edgeBasisMap g v
    exact edgeBasisMap_eq_homologyClass_edgeChain_sum g v
      (edgeChain_sum_isCycle g v)
  rw [← hclass]
  exact hedge

/--
The chosen coefficient value is additive after applying `edgeBasisMap`.
Thus the remaining pointwise additivity leaf is exactly a coefficient
uniqueness statement, not additional homology plumbing.
-/
theorem edgeCoefficientCycleValue_add_edgeBasis
    (g : ℕ)
    (x y : (singularChainComplexZ (Polygon4g (g + 1))).cycles 1) :
    edgeBasisMap g (edgeCoefficientCycleValue g (x + y)) =
      edgeBasisMap g (edgeCoefficientCycleValue g x +
        edgeCoefficientCycleValue g y) := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  have hxy := edgeCoefficientCycleValue_homologyClass g (x + y)
  have hx := edgeCoefficientCycleValue_homologyClass g x
  have hy := edgeCoefficientCycleValue_homologyClass g y
  calc
    edgeBasisMap g (edgeCoefficientCycleValue g (x + y))
        = ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) (x + y) := by
          exact hxy.symm
    _ = ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) x +
        ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) y := by
          rw [map_add]
    _ = edgeBasisMap g (edgeCoefficientCycleValue g x) +
        edgeBasisMap g (edgeCoefficientCycleValue g y) := by
          rw [hx, hy]
    _ = edgeBasisMap g (edgeCoefficientCycleValue g x +
        edgeCoefficientCycleValue g y) := by
          rw [map_add]

/--
Uniqueness of the chosen repair coefficient vector among edge-basis
representatives of the same homology class.

This is the remaining non-circular coefficient theorem needed by the
cycle-level extractor: once proved from the explicit polygon repair
construction, the additivity, boundary-vanishing, and edge-sum
normalization leaves below become formal consequences.
-/
theorem edgeCoefficientCycleValue_unique
    (g : ℕ)
    (c : (singularChainComplexZ (Polygon4g (g + 1))).cycles 1)
    (v : Polygon4gAbelianization g)
    (h :
      ((forget₂ (ModuleCat ℤ) Ab).map
          ((singularChainComplexZ (Polygon4g (g + 1))).homologyπ 1)) c =
        edgeBasisMap g v) :
    edgeCoefficientCycleValue g c = v := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let z : SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    (ConcreteCategory.hom (K.iCycles 1)) c
  have hz : K.d 1 0 z = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
        (((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) c) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, K.iCycles_d]
    simp
  let data := Classical.choice (polygon4g_cycle_lift_repair_data g z hz)
  have hcycles :
      K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz =
        c := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    simpa [K, z] using
      (K.i_cyclesMk z 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)
  have hclass :
      singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
        edgeBasisMap g v := by
    unfold singularH1ClassOfCycle
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1))
      (K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz) =
        edgeBasisMap g v
    rw [hcycles]
    exact h
  have hcoeff :
      data.edgeCoeffs = v :=
    polygon4g_repaired_edgeCoeffs_unique g z hz data v hclass
  simpa [K, edgeCoefficientCycleValue, z, hz, data] using hcoeff

/--
The chosen cycle coefficient value is additive.  This is the explicit
linearity statement for the lift/repair construction: finite supports,
lifts, endpoint-pair repairs, and their accumulated edge coefficients
must commute with addition of cycles.
-/
theorem edgeCoefficientCycleValue_add
    (g : ℕ)
    (x y : (singularChainComplexZ (Polygon4g (g + 1))).cycles 1) :
    edgeCoefficientCycleValue g (x + y) =
      edgeCoefficientCycleValue g x + edgeCoefficientCycleValue g y := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  apply edgeCoefficientCycleValue_unique g (x + y)
  calc
    ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) (x + y)
        = ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) x +
          ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) y := by
          rw [map_add]
    _ = edgeBasisMap g (edgeCoefficientCycleValue g x) +
        edgeBasisMap g (edgeCoefficientCycleValue g y) := by
          rw [edgeCoefficientCycleValue_homologyClass,
            edgeCoefficientCycleValue_homologyClass]
    _ = edgeBasisMap g (edgeCoefficientCycleValue g x +
        edgeCoefficientCycleValue g y) := by
          rw [map_add]

/--
The cycle-level edge-coefficient map before descent to homology.

Bottom-up route: for a cycle object element, use `K.iCycles` to view it
as an actual singular one-cycle, apply the finite support
decomposition/lift/repair package, and return the resulting repaired
edge coefficient vector.  Since the scalars are `ℤ`, additivity gives
linearity via `AddMonoidHom.toIntLinearMap`; the remaining work is the
additivity of the explicit repair-coefficient construction, then descent
and normalization on edge generators.
-/
noncomputable def edgeCoefficientCyclesMap (g : ℕ) :
    (singularChainComplexZ (Polygon4g (g + 1))).cycles 1 ⟶
      ModuleCat.of ℤ (Polygon4gAbelianization g) :=
  let coeffAdd :
      ((singularChainComplexZ (Polygon4g (g + 1))).cycles 1) →+
        Polygon4gAbelianization g :=
    {
      toFun := edgeCoefficientCycleValue g
      map_zero' := by
        have h := edgeCoefficientCycleValue_add g 0 0
        have h' :
            edgeCoefficientCycleValue g 0 + edgeCoefficientCycleValue g 0 =
              edgeCoefficientCycleValue g 0 + 0 := by
          simpa [zero_add, add_zero] using h.symm
        exact add_left_cancel h'
      map_add' := edgeCoefficientCycleValue_add g
    }
  ModuleCat.ofHom {
    toFun := edgeCoefficientCycleValue g
    map_add' := coeffAdd.map_add
    map_smul' := by
      intro n x
      change
        coeffAdd ((inferInstance :
          Module ℤ ((singularChainComplexZ (Polygon4g (g + 1))).cycles 1)).smul n x) =
          (inferInstance : Module ℤ (Polygon4gAbelianization g)).smul n (coeffAdd x)
      rw [int_smul_eq_zsmul
          (inferInstance :
            Module ℤ ((singularChainComplexZ (Polygon4g (g + 1))).cycles 1)),
        int_smul_eq_zsmul
          (inferInstance : Module ℤ (Polygon4gAbelianization g))]
      exact coeffAdd.map_zsmul x n
  }

/--
Pointwise boundary-vanishing for the chosen edge-coefficient value.
This is the chain-level independence statement before rewriting it as
a categorical composition.
-/
theorem edgeCoefficientCycleValue_boundary_zero
    (g : ℕ)
    (x : ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).X₁) :
    edgeCoefficientCycleValue g
      (((singularChainComplexZ (Polygon4g (g + 1))).sc 1).toCycles.hom x) = 0 := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let c : K.cycles 1 := ((K.sc 1).toCycles).hom x
  apply edgeCoefficientCycleValue_unique g c 0
  have hzero :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) c = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map
        ((K.sc 1).toCycles ≫ K.homologyπ 1)) x = 0
    rw [show (K.sc 1).toCycles ≫ K.homologyπ 1 = 0 by
      set_option linter.unnecessarySimpa false in
      simpa [HomologicalComplex.homologyπ] using
        (K.sc 1).toCycles_comp_homologyπ]
    simp
  simpa [K, c] using hzero

/--
Pointwise normalization of the chosen edge-coefficient value on finite
edge-chain cycles.
-/
theorem edgeCoefficientCycleValue_edge_sum
    (g : ℕ) (v : Polygon4gAbelianization g) :
    edgeCoefficientCycleValue g
      ((singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g v)) = v := by
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let c : K.cycles 1 :=
    K.cyclesMk
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
      (edgeChain_sum_isCycle g v)
  apply edgeCoefficientCycleValue_unique g c v
  change singularH1ClassOfCycle (Polygon4g (g + 1))
    (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e)
    (edgeChain_sum_isCycle g v) = edgeBasisMap g v
  exact edgeBasisMap_eq_homologyClass_edgeChain_sum g v
    (edgeChain_sum_isCycle g v)

/--
The cycle-level edge-coefficient map kills singular two-boundaries.

This is the exact chain-level independence statement: if a singular
one-cycle is a boundary, cutting it to the polygon and summing endpoint
repairs yields total edge coefficient zero.
-/
theorem edgeCoefficientCyclesMap_boundary_zero (g : ℕ) :
    ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).toCycles ≫
      edgeCoefficientCyclesMap g = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact edgeCoefficientCycleValue_boundary_zero g x

/--
The cycle-level edge-coefficient map reads finite edge-chain
combinations as their original coefficient vectors.
-/
theorem edgeCoefficientCyclesMap_edge_sum
    (g : ℕ) (v : Polygon4gAbelianization g) :
    (edgeCoefficientCyclesMap g).hom
      ((singularChainComplexZ (Polygon4g (g + 1))).cyclesMk
        (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
        (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
        (edgeChain_sum_isCycle g v)) = v := by
  exact edgeCoefficientCycleValue_edge_sum g v

/--
Concrete coefficient-extractor provider.  Bottom-up route: construct
`coeffCycles` by cutting the representative cycle to the `4g`-gon,
summing endpoint repairs as in `polygon4g_cycle_lift_repair_data`, and
then prove independence from singular two-boundaries by the explicit
boundary-word/commutator cancellation.

This provider is strictly cycle-level: homology descent is handled
below by `descHomology`.
-/
theorem edgeCoefficientCycleFunctionalData (g : ℕ) :
    Nonempty (EdgeCoefficientCycleFunctionalData g) := by
  exact ⟨{
    coeffCycles := edgeCoefficientCyclesMap g
    coeffCycles_boundary_zero := edgeCoefficientCyclesMap_boundary_zero g
    coeffCycles_edge_sum := edgeCoefficientCyclesMap_edge_sum g
  }⟩

/--
Edge-loop classes are independent in Mathlib singular `H₁` of the
polygon quotient.

Bottom-up route: construct this map by sending a singular homology
class to the vector of edge coefficients obtained from the explicit
polygon cellular approximation, and prove that the construction is
independent of the chosen singular cycle representative.  Equivalently,
show that the coefficient functional vanishes on singular two-boundaries
after cutting to the `4g`-gon.
-/
theorem edgeBasisMap_leftInverse (g : ℕ) :
    ∃ coeffMap :
      singularH1 (Polygon4g (g + 1)) →ₗ[ℤ] Polygon4gAbelianization g,
        coeffMap.comp (edgeBasisMap g) = LinearMap.id := by
  obtain ⟨data⟩ := edgeCoefficientCycleFunctionalData g
  let K := singularChainComplexZ (Polygon4g (g + 1))
  let coeffHom :
      K.homology 1 ⟶ ModuleCat.of ℤ (Polygon4gAbelianization g) :=
    (K.sc 1).descHomology data.coeffCycles data.coeffCycles_boundary_zero
  refine ⟨coeffHom.hom, ?_⟩
  ext v
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← edgeBasisMap_eq_homologyClass_edgeChain_sum
    g v (edgeChain_sum_isCycle g v)]
  unfold singularH1ClassOfCycle
  change coeffHom.hom
      (((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1))
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v))) = v
  change coeffHom.hom
      ((K.homologyπ 1).hom
        (K.cyclesMk
          (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
          (edgeChain_sum_isCycle g v))) = v
  rw [← ModuleCat.comp_apply]
  have hπ :
      K.homologyπ 1 ≫ coeffHom = data.coeffCycles := by
    exact
      (ShortComplex.π_descHomology (S := K.sc 1)
        data.coeffCycles data.coeffCycles_boundary_zero)
  rw [hπ]
  exact data.coeffCycles_edge_sum v

/--
Edge-loop classes are independent in Mathlib singular `H₁` of the
polygon quotient.
-/
theorem edgeBasisMap_injective_aux (g : ℕ) :
    Function.Injective (edgeBasisMap g) := by
  obtain ⟨coeffMap, hcoeffMap⟩ := edgeBasisMap_leftInverse g
  intro x y hxy
  calc
    x = coeffMap (edgeBasisMap g x) := by
      simpa using
        (congrArg
          (fun F : Polygon4gAbelianization g →ₗ[ℤ] Polygon4gAbelianization g =>
            F x) hcoeffMap).symm
    _ = coeffMap (edgeBasisMap g y) := by
      rw [hxy]
    _ = y := by
      simpa using
        (congrArg
          (fun F : Polygon4gAbelianization g →ₗ[ℤ] Polygon4gAbelianization g =>
            F y) hcoeffMap)

/--
In positive genus, the project-side singular-C1 map is exactly the
edge-basis map applied to the coefficient vector.
-/
theorem polygon4gSingularC1_toSingularH1LinearMap_apply_succ
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C)
    (c : Polygon4gSingularC1 (g + 1) C D) :
    Polygon4gSingularC1.toSingularH1LinearMap (g + 1) C D c =
      edgeBasisMap g c.coeff := by
  rw [edgeBasisMap_apply]
  unfold Polygon4gSingularC1.toSingularH1LinearMap
  simp only [LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [LinearMap.proj_apply]
  have hcoeff :
      (Polygon4gSingularC1.coeffLinearMap (g + 1) C D c) i = c.coeff i := rfl
  rw [hcoeff]
  rw [show edgeHomologyClass g i =
      Polygon4gSingularC1.toSingularH1Class (g + 1) C D ⟨Pi.single i 1⟩ by
    rw [Polygon4gSingularC1.toSingularH1_single]
    rfl]

/--
Positive-genus bridge from project-side singular edge chains to
Mathlib singular `H₁`, assembled from the edge-basis spanning and
independence leaves.
-/
theorem polygon4gSingularC1_toSingularH1LinearMap_bijective_succ
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Function.Bijective (Polygon4gSingularC1.toSingularH1LinearMap (g + 1) C D) := by
  constructor
  · intro x y hxy
    have hcoeff : x.coeff = y.coeff := by
      apply edgeBasisMap_injective_aux g
      rw [← polygon4gSingularC1_toSingularH1LinearMap_apply_succ g C D x,
        ← polygon4gSingularC1_toSingularH1LinearMap_apply_succ g C D y]
      exact hxy
    ext i
    exact congrFun hcoeff i
  · intro y
    obtain ⟨v, hv⟩ := edgeBasisMap_surjective g y
    refine ⟨⟨v⟩, ?_⟩
    rw [polygon4gSingularC1_toSingularH1LinearMap_apply_succ g C D]
    exact hv

/--
Genus-zero bridge.  The domain has no edge coefficients, and
`Polygon4g 0` is contractible, so both sides are subsingletons.
-/
theorem polygon4gSingularC1_toSingularH1LinearMap_bijective_zero
    (C : Polygon4gCellularModel 0)
    (D : Polygon4gCellularSingularComparisonData 0 C) :
    Function.Bijective (Polygon4gSingularC1.toSingularH1LinearMap 0 C D) := by
  constructor
  · intro x y _h
    ext i
    exact Fin.elim0 i
  · intro y
    haveI : ContractibleSpace (Polygon4g 0) := by
      obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
      exact h.contractibleSpace
    haveI : Subsingleton (singularH1 (Polygon4g 0)) :=
      singularH1_subsingleton_of_contractibleSpace
    refine ⟨⟨0⟩, ?_⟩
    exact Subsingleton.elim _ _


theorem polygon4gSingularC1_toSingularH1LinearMap_bijective
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Function.Bijective (Polygon4gSingularC1.toSingularH1LinearMap g C D) := by
  cases g with
  | zero => exact polygon4gSingularC1_toSingularH1LinearMap_bijective_zero C D
  | succ g => exact polygon4gSingularC1_toSingularH1LinearMap_bijective_succ g C D

/-- Injectivity half extracted from the concrete polygon singular-C1 bridge. -/
theorem polygon4gSingularC1_toSingularH1LinearMap_injective
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Function.Injective (Polygon4gSingularC1.toSingularH1LinearMap g C D) :=
  (polygon4gSingularC1_toSingularH1LinearMap_bijective g C D).injective

/-- Surjectivity half extracted from the concrete polygon singular-C1 bridge. -/
theorem polygon4gSingularC1_toSingularH1LinearMap_surjective
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Function.Surjective (Polygon4gSingularC1.toSingularH1LinearMap g C D) :=
  (polygon4gSingularC1_toSingularH1LinearMap_bijective g C D).surjective

/--
Project-side singular two-chains for the comparison: free rank one
on the characteristic disk.
-/
abbrev Polygon4gSingularC2
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_D : Polygon4gCellularSingularComparisonData g C) : Type :=
  Unit → ℤ

/--
Boundary of a path-chain: target minus source as a singular
zero-chain.
-/
noncomputable def polygon4gPathBoundary
    {g : ℕ} {C : Polygon4gCellularModel g} (γ : Path C.vertex C.vertex) :
    Polygon4gSingularC0 g :=
  Finsupp.single (γ 1) (1 : ℤ) - Finsupp.single (γ 0) (1 : ℤ)

/--
A based loop has zero path boundary when both endpoints are the
model vertex.
-/
theorem polygon4gPathBoundary_eq_zero_of_endpoints
    {g : ℕ} {C : Polygon4gCellularModel g} (γ : Path C.vertex C.vertex)
    (h0 : γ 0 = C.vertex) (h1 : γ 1 = C.vertex) :
    polygon4gPathBoundary γ = 0 := by
  rw [polygon4gPathBoundary, h0, h1, sub_self]

/-- The singular zero-chain at the unique cellular vertex. -/
noncomputable def polygon4gSingularVertexChain
    {g : ℕ} (C : Polygon4gCellularModel g) : Polygon4gSingularC0 g :=
  Finsupp.single C.vertex (1 : ℤ)

/--
The singular one-chain associated to the cellular boundary word:
the abelianised word coefficients on the recorded edge-path generators.
-/
def polygon4gBoundaryWordChain
    {g : ℕ} {C : Polygon4gCellularModel g}
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D :=
  ⟨edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord⟩

/--
The cellular-to-singular chain map and the singular proxy
boundaries used by the polygon comparison.  This is deliberately
chain-level: the fields are maps between chain modules and explicit
boundary operators, not propositions about endpoints alone.
-/
structure Polygon4gCellularToSingularChainMap
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) where
  mapC0 : Polygon4gCellularC0 g →ₗ[ℤ] Polygon4gSingularC0 g
  mapC1 : Polygon4gCellularC1 g →ₗ[ℤ] Polygon4gSingularC1 g C D
  mapC2 : Polygon4gCellularC2 g →ₗ[ℤ] Polygon4gSingularC2 g C D
  singularBoundaryC1 :
    Polygon4gSingularC1 g C D →ₗ[ℤ] Polygon4gSingularC0 g
  singularBoundaryC2 :
    Polygon4gSingularC2 g C D →ₗ[ℤ] Polygon4gSingularC1 g C D
  /--
On every one-cell generator, the singular boundary is target minus
  source for the corresponding path.
-/
  boundaryC1_on_basis :
    ∀ e : Fin (2 * g),
      singularBoundaryC1 (mapC1 (polygon4gCellularBasis e)) =
        polygon4gPathBoundary (D.oneCells.edgePath e)
  /--
The characteristic disk boundary is represented by the boundary-word
  one-chain.
-/
  boundaryC2_on_face :
    singularBoundaryC2 (mapC2 polygon4gCellularC2Face) =
      polygon4gBoundaryWordChain D

/--
The concrete cellular-to-singular chain map carried by the project-side
polygon data.
-/
noncomputable def polygon4g_cellularToSingularChainMap
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularToSingularChainMap g C D where
  mapC0 := {
    toFun := fun c => c () • polygon4gSingularVertexChain C
    map_add' := by
      intro c d
      ext x
      simp [Pi.add_apply, add_smul]
    map_smul' := by
      intro n c
      ext x
      simp [Pi.smul_apply, smul_smul]
  }
  mapC1 := {
    toFun := fun c => ⟨c⟩
    map_add' := by
      intro c d
      ext e
      rfl
    map_smul' := by
      intro n c
      ext e
      rfl
  }
  mapC2 := LinearMap.id
  singularBoundaryC1 := {
    toFun := fun c =>
      ∑ e : Fin (2 * g), c.coeff e • polygon4gPathBoundary (D.oneCells.edgePath e)
    map_add' := by
      intro a b
      ext x
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_add,
        Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change
        (∑ e : Fin (2 * g),
            (a.coeff e + b.coeff e) *
              (polygon4gPathBoundary (D.oneCells.edgePath e)) x) =
          ∑ e : Fin (2 * g),
            a.coeff e * (polygon4gPathBoundary (D.oneCells.edgePath e)) x +
          ∑ e : Fin (2 * g),
            b.coeff e * (polygon4gPathBoundary (D.oneCells.edgePath e)) x
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro n a
      ext x
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Polygon4gSingularC1.smul_coeff]
      change
        (∑ e : Fin (2 * g),
            (n * a.coeff e) *
              (polygon4gPathBoundary (D.oneCells.edgePath e)) x) =
          n * ∑ e : Fin (2 * g),
            a.coeff e * (polygon4gPathBoundary (D.oneCells.edgePath e)) x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
  }
  singularBoundaryC2 := {
    toFun := fun c => c () • polygon4gBoundaryWordChain D
    map_add' := by
      intro a b
      ext e
      simp [Pi.add_apply, add_smul]
    map_smul' := by
      intro n a
      ext e
      simp [Pi.smul_apply, smul_smul]
  }
  boundaryC1_on_basis := by
    intro e
    ext x
    simp [polygon4gCellularBasis]
  boundaryC2_on_face := by
    ext e
    simp [polygon4gCellularC2Face]

/--
The concrete cellular-to-singular map sends a cellular one-cell
generator to the actual singular edge chain after realizing the project
side `Polygon4gSingularC1` wrapper as concrete singular chains.
-/
theorem polygon4g_cellularToSingularChainMap_basis_realizes_edgeChain
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C)
    (e : Fin (2 * g)) :
    Polygon4gSingularC1.toConcreteEdgeChain g C D
        ((polygon4g_cellularToSingularChainMap g C D).mapC1
          (polygon4gCellularBasis e)) =
      edgeChainOnGenus g e := by
  rw [show (polygon4g_cellularToSingularChainMap g C D).mapC1
      (polygon4gCellularBasis e) = (⟨Pi.single e 1⟩ : Polygon4gSingularC1 g C D) by
    ext e'
    simp [polygon4g_cellularToSingularChainMap, polygon4gCellularBasis, Pi.single_apply]]
  exact Polygon4gSingularC1.toConcreteEdgeChain_single g C D e


def Polygon4gZeroSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  x = C.vertex


def Polygon4gOneSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  x = C.vertex ∨ ∃ e : Fin (2 * g), ∃ t : Set.Icc (0 : ℝ) 1, C.oneCellPath e t = x


def Polygon4gTwoSkeleton
    (g : ℕ) (_C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  ∃ z : DiskC, Polygon4g.mk g z = x


theorem polygon4g_mem_twoSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) :
    Polygon4gTwoSkeleton g C x := by
  induction x using Quotient.inductionOn with
  | h z => exact ⟨z, rfl⟩

/--
Chain-level support predicates for the singular chains used in the
filtered comparison.  The predicates are stated on chains, not just on
individual cellular attaching maps.
-/
structure Polygon4gFilteredSingularChainSupport
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_M : Polygon4gCellularToSingularChainMap g C D) : Type where
  /-- Zero-chains are generated by the unique vertex chain. -/
  zeroChainSupported : Polygon4gSingularC0 g → Prop
  /-- One-chains are supported on the recorded edge-path generators. -/
  oneChainSupported : Polygon4gSingularC1 g C D → Prop
  /-- Two-chains are supported on the characteristic disk generator. -/
  twoChainSupported : Polygon4gSingularC2 g C D → Prop
  zeroChainSupported_iff :
    ∀ c, zeroChainSupported c ↔
      ∃ n : ℤ, c = n • polygon4gSingularVertexChain C
  oneChainSupported_iff :
    ∀ c, oneChainSupported c ↔
      ∀ e : Fin (2 * g), c.coeff e ≠ 0 →
        ∀ t : Set.Icc (0 : ℝ) 1,
          Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)
  twoChainSupported_iff :
    ∀ c, twoChainSupported c ↔
      c () ≠ 0 →
        ∀ z : C.disk.diskSource.carrier,
          Polygon4gTwoSkeleton g C (D.twoCell.characteristic.characteristic z)

/--
The associated-graded degree-one comparison as a real linear
equivalence from cellular one-generators to the singular edge-chain
wrapper.  This is intentionally not a reflexive equivalence between
aliases.
-/
def polygon4g_cellularH1_to_singularC1_equiv
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularH1 g ≃ₗ[ℤ] Polygon4gSingularC1 g C D where
  toFun := fun c => ⟨c⟩
  invFun := fun c => c.coeff
  left_inv := by
    intro c
    rfl
  right_inv := by
    intro c
    ext e
    rfl
  map_add' := by
    intro c d
    ext e
    rfl
  map_smul' := by
    intro n c
    ext e
    rfl

/--
Degree-zero correctness of the comparison data: the unique
zero-cell maps to the singular class of the polygon vertex.
-/
structure Polygon4gCellularSingularChainMapDegreeZero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop where
  /-- The comparison's zero-cell representative is the model vertex. -/
  vertex_eq_model : D.zeroCell.vertex = C.vertex
  
  vertex_mem_zeroSkeleton :
    Polygon4gZeroSkeleton g C D.zeroCell.vertex

/--
Degree-one correctness of the comparison data: each oriented
one-cell maps to the corresponding singular edge path, and its singular
boundary agrees with the zero cellular boundary at the unique vertex.
-/
structure Polygon4gCellularSingularChainMapDegreeOneBoundary
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop where
  /-- The comparison sends each one-cell generator to the model one-cell path. -/
  edgePath_eq_model : D.oneCells.edgePath = C.oneCellPath
  /-- Each comparison edge starts at the unique model vertex. -/
  edgePath_source : ∀ e : Fin (2 * g), (D.oneCells.edgePath e) 0 = C.vertex
  /-- Each comparison edge ends at the unique model vertex. -/
  edgePath_target : ∀ e : Fin (2 * g), (D.oneCells.edgePath e) 1 = C.vertex
  /-- The cellular one-boundary is zero for every edge. -/
  cellular_boundary_zero : Polygon4gOneCellBoundaryZero g C
  /--
There is a concrete chain map whose degree-one singular boundary is
  the path-chain boundary on each cellular one-cell generator.
-/
  singular_path_boundary_formula :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      ∀ e : Fin (2 * g),
        M.singularBoundaryC1 (M.mapC1 (polygon4gCellularBasis e)) =
          polygon4gPathBoundary (D.oneCells.edgePath e)
  /--
Since the edge representatives are based loops, their singular
  path-chain boundaries vanish.
-/
  singular_path_boundary_zero :
    ∀ e : Fin (2 * g), polygon4gPathBoundary (D.oneCells.edgePath e) = 0
  /--
Consequently the chain-level singular boundary of each mapped one-cell
  generator vanishes.
-/
  singular_chain_boundary_zero :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      ∀ e : Fin (2 * g),
        M.singularBoundaryC1 (M.mapC1 (polygon4gCellularBasis e)) = 0
  
  edgePath_mem_oneSkeleton :
    ∀ e : Fin (2 * g), ∀ t : Set.Icc (0 : ℝ) 1,
      Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)

/--
Degree-two correctness of the comparison data: the two-cell
attaching map is sent to the singular boundary represented by the
surface word, whose abelianised boundary is the cellular formula.
-/
structure Polygon4gCellularSingularChainMapDegreeTwoAttaching
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop where
  /-- The comparison's two-cell characteristic map is the quotient map. -/
  characteristic_eq_mk :
    ∀ z, D.twoCell.characteristic.characteristic z =
      Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z)
  /--
The comparison's two-cell characteristic map agrees pointwise with
  the cellular model's characteristic map.
-/
  characteristic_eq_model :
    ∀ z, D.twoCell.characteristic.characteristic z = C.twoCellCharacteristic z
  /-- The boundary word is the model boundary word. -/
  boundaryWord_eq_model : D.twoCell.boundaryWord.boundaryWord = C.boundaryWord
  /-- The boundary word is the standard product of commutators. -/
  boundaryWord_standard : D.twoCell.boundaryWord.boundaryWord.IsStandardForm
  /-- The word induces the polygon side-pairing relation. -/
  boundaryWord_sidePairing :
    EdgeWord.sidePairingRel g D.twoCell.boundaryWord.boundaryWord = Polygon4g.SideRel g
  /-- The abelianised two-boundary vanishes in cellular one-chains. -/
  boundaryWord_abelianizedBoundary :
    edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord = 0
  /--
The singular boundary of the mapped characteristic disk is the
  boundary-word one-chain.
-/
  singular_disk_boundary_formula :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      M.singularBoundaryC2 (M.mapC2 polygon4gCellularC2Face) =
        polygon4gBoundaryWordChain D
  /--
The boundary-word one-chain has exactly the abelianised word
  coefficients.
-/
  boundaryWord_chain_coefficients :
    (polygon4gBoundaryWordChain D).coeff =
      edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord
  /--
The boundary-word singular one-chain vanishes because the surface
  relator abelianises to zero.
-/
  boundaryWord_chain_zero : polygon4gBoundaryWordChain D = 0
  /-- The model cellular two-boundary formula is available. -/
  cellular_two_boundary_formula : Polygon4gTwoCellBoundaryAbelianizedRelator g C

/--
**Comparison leaf 2a.** The comparison data is correct in degree
zero.
-/
theorem polygon4g_cellular_singular_chain_map_degree_zero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D :=
  ⟨D.zeroCell.vertex_eq_model, D.zeroCell.vertex_eq_model⟩

/--
**Comparison leaf 2b.** The comparison data is compatible with the
one-cell boundary calculation.
-/
theorem polygon4g_cellular_singular_chain_map_degree_one_boundary
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D := by
  let M := polygon4g_cellularToSingularChainMap g C D
  have h_source : ∀ e : Fin (2 * g), (D.oneCells.edgePath e) 0 = C.vertex := by
    intro e
    rw [D.oneCells.edgePath_eq_model]
    exact (h_boundary.1 e).1
  have h_target : ∀ e : Fin (2 * g), (D.oneCells.edgePath e) 1 = C.vertex := by
    intro e
    rw [D.oneCells.edgePath_eq_model]
    exact (h_boundary.1 e).2
  refine
    { edgePath_eq_model := D.oneCells.edgePath_eq_model
      edgePath_source := h_source
      edgePath_target := h_target
      cellular_boundary_zero := h_boundary.1
      singular_path_boundary_formula := ?_
      singular_path_boundary_zero := ?_
      singular_chain_boundary_zero := ?_
      edgePath_mem_oneSkeleton := ?_ }
  · exact ⟨M, fun e => M.boundaryC1_on_basis e⟩
  · intro e
    exact polygon4gPathBoundary_eq_zero_of_endpoints
      (D.oneCells.edgePath e) (h_source e) (h_target e)
  · refine ⟨M, ?_⟩
    intro e
    rw [M.boundaryC1_on_basis e]
    exact polygon4gPathBoundary_eq_zero_of_endpoints
      (D.oneCells.edgePath e) (h_source e) (h_target e)
  · intro e t
    right
    exact ⟨e, t, by rw [D.oneCells.edgePath_eq_model]⟩

/--
**Comparison leaf 2c.** The comparison data is compatible with the
two-cell attaching map.
-/
theorem polygon4g_cellular_singular_chain_map_degree_two_attaching
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D := by
  let M := polygon4g_cellularToSingularChainMap g C D
  refine
    { characteristic_eq_mk := D.twoCell.characteristic.characteristic_eq_mk
      characteristic_eq_model := ?_
      boundaryWord_eq_model := D.twoCell.boundaryWord.boundaryWord_eq_model
      boundaryWord_standard := D.twoCell.boundaryWord.boundaryWord_standard
      boundaryWord_sidePairing := D.twoCell.boundaryWord.boundaryWord_sidePairing
      boundaryWord_abelianizedBoundary :=
        D.twoCell.boundaryWord.boundaryWord_abelianizedBoundary
      singular_disk_boundary_formula := ⟨M, M.boundaryC2_on_face⟩
      boundaryWord_chain_coefficients := rfl
      boundaryWord_chain_zero := ?_
      cellular_two_boundary_formula := h_boundary.2 }
  · intro z
    rw [D.twoCell.characteristic.characteristic_eq_mk z,
      C.twoCellCharacteristic_eq_mk z]
  · change
      (⟨edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord⟩ :
        Polygon4gSingularC1 g C D) = 0
    rw [D.twoCell.boundaryWord.boundaryWord_abelianizedBoundary]
    rfl

/--
Correctness of the comparison data: it is compatible with the
cellular and singular differentials and computes the intended attaching
maps in dimensions `0`, `1`, and `2`.
-/
abbrev Polygon4gCellularSingularChainMapCorrect
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop :=
  Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D ∧
    Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D ∧
      Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D

/--
**Comparison assembly 2.** The chosen comparison data gives the
correct chain-level cellular-to-singular comparison map.  This is now
assembled from the degree `0`, `1`, and `2` correctness leaves.
-/
theorem polygon4g_cellular_singular_chain_map_correct
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapCorrect g C h_boundary D :=
by
  exact ⟨polygon4g_cellular_singular_chain_map_degree_zero g C h_boundary D,
    polygon4g_cellular_singular_chain_map_degree_one_boundary g C h_boundary D,
    polygon4g_cellular_singular_chain_map_degree_two_attaching g C h_boundary D⟩


structure Polygon4gCellularSingularFiltrationCompatible
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D) : Prop where
  /--
A concrete chain map, chain-level support predicates, filtered image
  statements, and boundary-preservation statements for the singular-chain
  filtration.
-/
  filtered_chain_support :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      ∃ S : Polygon4gFilteredSingularChainSupport g C D M,
        (∀ c : Polygon4gCellularC0 g, S.zeroChainSupported (M.mapC0 c)) ∧
        (∀ c : Polygon4gCellularC1 g, S.oneChainSupported (M.mapC1 c)) ∧
        (∀ c : Polygon4gCellularC2 g, S.twoChainSupported (M.mapC2 c)) ∧
        (∀ c : Polygon4gSingularC1 g C D,
          S.oneChainSupported c → S.zeroChainSupported (M.singularBoundaryC1 c)) ∧
        (∀ c : Polygon4gSingularC2 g C D,
          S.twoChainSupported c → S.oneChainSupported (M.singularBoundaryC2 c))
  
  zeroCell_supported : Polygon4gZeroSkeleton g C D.zeroCell.vertex
  
  oneCells_supported :
    ∀ e : Fin (2 * g), ∀ t : Set.Icc (0 : ℝ) 1,
      Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)
  
  twoCell_supported :
    ∀ z : C.disk.diskSource.carrier,
      Polygon4gTwoSkeleton g C (D.twoCell.characteristic.characteristic z)

/--
The associated graded map of the cellular-to-singular comparison is
the identity on the cellular generators in degrees relevant to `H₁`.
This packages the local relative-homology calculation for each open
cell.
-/
structure Polygon4gCellularSingularAssociatedGradedH1Iso
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D)
    (_h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C _h_boundary D h_correct) :
    Prop where
  /--
The associated graded degree-zero generator is represented by the
  model vertex.
-/
  graded_zero_generator : D.zeroCell.vertex = C.vertex
  /--
The associated graded degree-one generators are represented by the
  model one-cell loops.
-/
  graded_one_generators : D.oneCells.edgePath = C.oneCellPath
  /--
The concrete associated-graded degree-one map is the degree-one
  component of a real cellular-to-singular chain map.
-/
  graded_one_map_eq_chainMap :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      (polygon4g_cellularH1_to_singularC1_equiv g C D).toLinearMap = M.mapC1
  /--
The associated graded degree-two boundary is the abelianised surface
  relator, hence zero in cellular one-chains.
-/
  graded_two_boundary_zero :
    edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord = 0
  /--
The project-side degree-one associated-graded map is an isomorphism
  from cellular `H₁` generators to singular edge-chain generators.
-/
  graded_one_isomorphism :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] Polygon4gSingularC1 g C D)

/--
A concrete bridge from the project-side singular one-chain wrapper
used by the polygon comparison to Mathlib's actual singular `H₁`.
This is the precise topological input still missing from the current
API: the filtered/five-lemma argument must construct this equivalence
from the chain map and filtration data, not by definitional equality.
-/
structure Polygon4gSingularC1RealizesSingularH1
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) where
  /--
The resulting equivalence between the project-side edge-chain
  associated-graded model and Mathlib singular homology.
-/
  equiv : Polygon4gSingularC1 g C D ≃ₗ[ℤ] singularH1 (Polygon4g g)
  /--
The chain-level comparison whose degree-one component gives the
  project-side edge-chain model.
-/
  chainMap : Polygon4gCellularToSingularChainMap g C D
  /--
The chain map realizes the associated-graded degree-one comparison,
  so the bridge is tied to the cellular-to-singular chain data rather than
  to an arbitrary algebraic isomorphism.
-/
  chainMap_degree_one :
    chainMap.mapC1 = (polygon4g_cellularH1_to_singularC1_equiv g C D).toLinearMap

/--
If the concrete linear edge-chain class map is bijective, it gives
the realization data required by the filtered Hurewicz comparison.
This isolates the remaining topological content as bijectivity of the
actual edge-chain map into Mathlib singular `H₁`.
-/
noncomputable def polygon4g_singularC1_realizes_singularH1_of_toSingularH1LinearMap_bijective
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_bij :
      Function.Bijective (Polygon4gSingularC1.toSingularH1LinearMap g C D)) :
    Polygon4gSingularC1RealizesSingularH1 g C D :=
  { equiv :=
      LinearEquiv.ofBijective
        (Polygon4gSingularC1.toSingularH1LinearMap g C D) h_bij
    chainMap := polygon4g_cellularToSingularChainMap g C D
    chainMap_degree_one := by
      ext c e
      rfl }

/--
Conditional form of the filtered comparison: once the project-side
singular edge-chain wrapper is identified with Mathlib `singularH1`
by a chain-level realization, the existing associated-graded cellular
isomorphism gives the desired cellular-to-singular `H₁` equivalence.
-/
theorem polygon4g_cellular_to_singular_H1_iso_of_singularC1_realization
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct)
    (h_graded :
      Polygon4gCellularSingularAssociatedGradedH1Iso
        g C h_boundary D h_correct h_filtration)
    (h_realizes : Polygon4gSingularC1RealizesSingularH1 g C D) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  obtain ⟨e₁⟩ := h_graded.graded_one_isomorphism
  exact ⟨e₁.trans h_realizes.equiv⟩


theorem polygon4g_cellular_to_singular_H1_iso_of_toSingularH1LinearMap_bijective
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h0 : Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D)
    (h1 : Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D)
    (h2 : Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D ⟨h0, h1, h2⟩)
    (h_graded :
      Polygon4gCellularSingularAssociatedGradedH1Iso
        g C h_boundary D ⟨h0, h1, h2⟩ h_filtration)
    (h_bij :
      Function.Bijective (Polygon4gSingularC1.toSingularH1LinearMap g C D)) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  exact polygon4g_cellular_to_singular_H1_iso_of_singularC1_realization
    g C h_boundary D ⟨h0, h1, h2⟩ h_filtration h_graded
    (polygon4g_singularC1_realizes_singularH1_of_toSingularH1LinearMap_bijective
      g C D h_bij)

/--
This is the remaining missing theorem boundary: it is the filtered
cellular/singular comparison in degree `1`, specialized to the standard
two-dimensional `Polygon4g` cellular model and stated over concrete
project-side data rather than opaque predicates.
-/
theorem polygon4g_cellular_to_singular_H1_iso_from_concrete_comparison
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h0 : Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D)
    (h1 : Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D)
    (h2 : Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D ⟨h0, h1, h2⟩)
    (h_graded :
      Polygon4gCellularSingularAssociatedGradedH1Iso
        g C h_boundary D ⟨h0, h1, h2⟩ h_filtration) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  exact polygon4g_cellular_to_singular_H1_iso_of_toSingularH1LinearMap_bijective
    g C h_boundary D h0 h1 h2 h_filtration h_graded
    (polygon4gSingularC1_toSingularH1LinearMap_bijective g C D)

/--
**Comparison leaf 3a.** The correct comparison map is compatible
with the cellular filtration.
-/
theorem polygon4g_cellular_singular_filtration_compatible
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D) :
    Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct := by
  let M := polygon4g_cellularToSingularChainMap g C D
  let S : Polygon4gFilteredSingularChainSupport g C D M :=
    { zeroChainSupported := fun c =>
        ∃ n : ℤ, c = n • polygon4gSingularVertexChain C
      oneChainSupported := fun c =>
        ∀ e : Fin (2 * g), c.coeff e ≠ 0 →
          ∀ t : Set.Icc (0 : ℝ) 1,
            Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)
      twoChainSupported := fun c =>
        c () ≠ 0 →
          ∀ z : C.disk.diskSource.carrier,
            Polygon4gTwoSkeleton g C (D.twoCell.characteristic.characteristic z)
      zeroChainSupported_iff := by
        intro c
        rfl
      oneChainSupported_iff := by
        intro c
        rfl
      twoChainSupported_iff := by
        intro c
        rfl }
  refine
    { filtered_chain_support := ?_
      zeroCell_supported := h_correct.1.vertex_mem_zeroSkeleton
      oneCells_supported := h_correct.2.1.edgePath_mem_oneSkeleton
      twoCell_supported := ?_ }
  · refine ⟨M, S, ?_, ?_, ?_, ?_, ?_⟩
    · intro c
      change ∃ n : ℤ, M.mapC0 c = n • polygon4gSingularVertexChain C
      exact ⟨c (), rfl⟩
    · intro c e _ t
      exact h_correct.2.1.edgePath_mem_oneSkeleton e t
    · intro c _ z
      rw [h_correct.2.2.characteristic_eq_mk z]
      exact polygon4g_mem_twoSkeleton g C
        (Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z))
    · intro c _hc
      change ∃ n : ℤ, M.singularBoundaryC1 c = n • polygon4gSingularVertexChain C
      refine ⟨0, ?_⟩
      have h_path_zero :
          ∀ e : Fin (2 * g), polygon4gPathBoundary (D.oneCells.edgePath e) = 0 :=
        h_correct.2.1.singular_path_boundary_zero
      ext x
      simp [M, polygon4g_cellularToSingularChainMap, h_path_zero]
    · intro c _hc e _he t
      exact h_correct.2.1.edgePath_mem_oneSkeleton e t
  · intro z
    rw [h_correct.2.2.characteristic_eq_mk z]
    exact polygon4g_mem_twoSkeleton g C
      (Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z))

/--
**Comparison leaf 3b.** The associated graded comparison is an
isomorphism in the degrees that control first homology.
-/
theorem polygon4g_cellular_singular_associated_graded_H1_iso
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct) :
    Polygon4gCellularSingularAssociatedGradedH1Iso
      g C h_boundary D h_correct h_filtration :=
by
  let M := polygon4g_cellularToSingularChainMap g C D
  let E := polygon4g_cellularH1_to_singularC1_equiv g C D
  refine
    { graded_zero_generator := h_correct.1.vertex_eq_model
      graded_one_generators := h_correct.2.1.edgePath_eq_model
      graded_one_map_eq_chainMap := ?_
      graded_two_boundary_zero := h_correct.2.2.boundaryWord_abelianizedBoundary
      graded_one_isomorphism := ⟨E⟩ }
  refine ⟨M, ?_⟩
  ext c e
  rfl

/--
**Comparison leaf 3c.** A filtration-compatible comparison whose
associated graded map is an isomorphism in the relevant degrees induces
the expected isomorphism on first homology.  Bottom-up route: specialise
the cellular homology theorem / filtration spectral sequence argument
to this finite two-dimensional CW complex.
-/
theorem polygon4g_cellular_singular_H1_iso_of_filtered_graded
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct)
    (_h_graded :
      Polygon4gCellularSingularAssociatedGradedH1Iso
        g C h_boundary D h_correct h_filtration) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  exact polygon4g_cellular_to_singular_H1_iso_from_concrete_comparison
    g C h_boundary D h_correct.1 h_correct.2.1 h_correct.2.2 h_filtration _h_graded


theorem polygon4g_cellular_singular_H1_iso_of_chain_map
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) :=
by
  let h_filtration :=
    polygon4g_cellular_singular_filtration_compatible
      g C h_boundary D _h_correct
  exact polygon4g_cellular_singular_H1_iso_of_filtered_graded
    g C h_boundary D _h_correct h_filtration
    (polygon4g_cellular_singular_associated_graded_H1_iso
      g C h_boundary D _h_correct h_filtration)


theorem polygon4g_cellular_to_singularH1_comparison
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) :=
by
  obtain ⟨D⟩ := polygon4g_cellular_singular_comparison_data g C _h_boundary
  exact polygon4g_cellular_singular_H1_iso_of_chain_map g C _h_boundary D
    (polygon4g_cellular_singular_chain_map_correct g C _h_boundary D)

/--
**Hurewicz/cellular bridge assembly.** A named project-side
comparison from the computed cellular group to singular `H₁`.
-/
theorem polygon4g_cellularH1_to_singularH1 (g : ℕ) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact polygon4g_cellular_to_singularH1_comparison g C
    (polygon4g_cellular_boundary_formula g C)

/-- Hurewicz isomorphism on the standard fundamental polygon. -/
theorem polygon4g_succ_hurewicz_iso_freeZ_internal (g : ℕ) :
    Nonempty (Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1))) := by
  obtain ⟨e⟩ := polygon4g_cellularH1_to_singularH1 (g + 1)
  exact ⟨e⟩

/-- Edge-loop classes are independent in Mathlib singular `H₁` of the
polygon quotient. -/
theorem edgeBasisMap_injective (g : ℕ) :
    Function.Injective (edgeBasisMap g) := by
  obtain ⟨e⟩ := polygon4g_succ_hurewicz_iso_freeZ_internal g
  have h_surj : Function.Surjective (e.symm.toLinearMap.comp (edgeBasisMap g)) := by
    intro x
    obtain ⟨y, hy⟩ := edgeBasisMap_surjective g (e x)
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hy, LinearEquiv.symm_apply_apply]
  have h_inj : Function.Injective (e.symm.toLinearMap.comp (edgeBasisMap g)) :=
    Module.End.injective_of_surjective ℤ (Polygon4gAbelianization g) h_surj
  intro x y hxy
  have hcomp : (e.symm.toLinearMap.comp (edgeBasisMap g)) x =
      (e.symm.toLinearMap.comp (edgeBasisMap g)) y := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hxy]
    rfl
  exact h_inj hcomp

end JacobianChallenge.Periods
