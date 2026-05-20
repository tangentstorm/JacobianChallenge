import Jacobian.Periods.CellularChainComplex
import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.LinearAlgebra.Pi

/-!
# Project-side Hurewicz and cellular-to-singular bridge

This file names the comparison theorem missing from Mathlib v4.28.0:
cellular homology agrees with singular homology for the cellular model
of the fundamental polygon.  It is deliberately stated at the narrow
surface needed by the Jacobian project.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory

/-- The singular datum attached to the unique zero-cell of the standard
polygonal cell structure. -/
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

/-- The singular edge-path data attached to the `2g` oriented one-cells
of the standard polygonal cell structure. -/
structure Polygon4gCellularSingularOneCellData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  /-- The singular representatives of the oriented one-cells. -/
  edgePath : Fin (2 * g) → Path C.vertex C.vertex
  /-- They are the one-cell loops recorded by the cellular model. -/
  edgePath_eq_model : edgePath = C.oneCellPath

/-- **Comparison leaf 1b.** Construct the singular one-cell edge-path
data. -/
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

/-- **Comparison leaf 1c(i).** Construct the singular characteristic
map data for the unique two-cell. -/
theorem polygon4g_cellular_singular_two_cell_characteristic_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularTwoCellCharacteristicData g C) :=
  ⟨{
    characteristic := C.twoCellCharacteristic
    characteristic_eq_mk := C.twoCellCharacteristic_eq_mk
  }⟩

/-- The boundary parametrisation of the singular two-cell by the
standard surface word `∏ᵢ [aᵢ,bᵢ]`. -/
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

/-- **Comparison leaf 1c(ii).** Construct the boundary-word
parametrisation for the singular two-cell. -/
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

/-- The singular two-cell datum: the quotient disk characteristic map
and its boundary parametrisation by the surface word. -/
structure Polygon4gCellularSingularTwoCellData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  characteristic : Polygon4gCellularSingularTwoCellCharacteristicData g C
  boundaryWord : Polygon4gCellularSingularTwoCellBoundaryWordData g C characteristic

/-- **Comparison assembly 1c.** Construct the singular two-cell disk and
attaching-map data from characteristic-map and boundary-word leaves. -/
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

/-- The comparison data between the cellular chain complex of the
standard polygon model and singular chains on the quotient surface.

Bottom-up route: define the characteristic-map pushforward on cells,
or specialise the usual cellular filtration construction to the finite
CW complex with one zero-cell, `2g` one-cells, and one two-cell. -/
structure Polygon4gCellularSingularComparisonData
    (g : ℕ) (C : Polygon4gCellularModel g) where
  zeroCell : Polygon4gCellularSingularZeroCellData g C
  oneCells : Polygon4gCellularSingularOneCellData g C
  twoCell : Polygon4gCellularSingularTwoCellData g C

/-- **Comparison assembly 1.** Existence of the cellular-to-singular
comparison data for the standard polygonal cell structure, assembled
from the zero-cell, one-cell, and two-cell data leaves. -/
theorem polygon4g_cellular_singular_comparison_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularComparisonData g C) :=
by
  obtain ⟨zeroCell⟩ := polygon4g_cellular_singular_zero_cell_data g C _h_boundary
  obtain ⟨oneCells⟩ := polygon4g_cellular_singular_one_cell_data g C _h_boundary
  obtain ⟨twoCell⟩ := polygon4g_cellular_singular_two_cell_data g C _h_boundary
  exact ⟨{ zeroCell, oneCells, twoCell }⟩

/-- The cellular zero-chain module for the standard polygon model:
free rank one on the unique vertex. -/
abbrev Polygon4gCellularC0 (_g : ℕ) : Type :=
  Unit → ℤ

/-- The cellular two-chain module for the standard polygon model:
free rank one on the unique two-cell. -/
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

/-- Project-side singular zero-chains on `Polygon4g g`: finitely
supported integral sums of points. -/
abbrev Polygon4gSingularC0 (g : ℕ) : Type :=
  Polygon4g g →₀ ℤ

/-- Project-side singular one-chains for the polygon comparison, wrapped
around the coefficients of the recorded edge paths.  The wrapper prevents
the associated-graded comparison from reducing to a reflexive equivalence
between aliases. -/
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

/-- Realize the project-side singular one-chain wrapper as an actual
Mathlib singular 1-chain by summing the concrete polygon edge chains with
the recorded coefficients. -/
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

/-- The concrete edge-chain realization of a single project-side edge
generator is the corresponding singular edge chain. -/
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

/-- The shape relation `(down ℕ).next 1 = 0` used by `cyclesMk`. -/
private lemma next_one_eq_zero_on_genus :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/-- The concrete realization of every project-side singular one-chain is
a Mathlib singular one-cycle, because it is a finite integral linear
combination of the concrete edge cycles. -/
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

/-- Project-side singular edge chains determine actual Mathlib
singular `H₁` by taking their concrete singular-chain realization,
proving it is a cycle, and applying `homologyπ`. -/
noncomputable def toSingularH1Class
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D → singularH1 (Polygon4g g) :=
  fun c =>
    ((forget₂ (ModuleCat ℤ) Ab).map ((polygonChainComplexOnGenus g).homologyπ 1))
      ((polygonChainComplexOnGenus g).cyclesMk
        (toConcreteEdgeChain g C D c) 0 next_one_eq_zero_on_genus
        (by simpa [polygonChainComplexOnGenus] using toConcreteEdgeChain_isCycle g C D c))

/-- On a single project-side edge generator, the canonical map to
Mathlib `H₁` is represented by the corresponding concrete edge chain. -/
theorem toSingularH1_single
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) (e : Fin (2 * g)) :
    toSingularH1Class g C D ⟨Pi.single e 1⟩ =
      ((forget₂ (ModuleCat ℤ) Ab).map ((polygonChainComplexOnGenus g).homologyπ 1))
        ((polygonChainComplexOnGenus g).cyclesMk
          (edgeChainOnGenus g e) 0 next_one_eq_zero_on_genus
          (by simpa [polygonChainComplexOnGenus] using edgeChainOnGenus_isCycle g e)) := by
  simp [toSingularH1Class, toConcreteEdgeChain_single]

/-- Linearized version of `toSingularH1Class`: a project-side singular
one-chain is sent to the finite integral linear combination of the
actual singular `H₁` classes of its edge generators. -/
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

/-- Linearized version of `toSingularH1Class`: a project-side singular
one-chain is sent to the finite integral linear combination of the
actual singular `H₁` classes of its edge generators. -/
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

/-- Project-side singular two-chains for the comparison: free rank one
on the characteristic disk. -/
abbrev Polygon4gSingularC2
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_D : Polygon4gCellularSingularComparisonData g C) : Type :=
  Unit → ℤ

/-- Boundary of a path-chain: target minus source as a singular
zero-chain. -/
noncomputable def polygon4gPathBoundary
    {g : ℕ} {C : Polygon4gCellularModel g} (γ : Path C.vertex C.vertex) :
    Polygon4gSingularC0 g :=
  Finsupp.single (γ 1) (1 : ℤ) - Finsupp.single (γ 0) (1 : ℤ)

/-- A based loop has zero path boundary when both endpoints are the
model vertex. -/
theorem polygon4gPathBoundary_eq_zero_of_endpoints
    {g : ℕ} {C : Polygon4gCellularModel g} (γ : Path C.vertex C.vertex)
    (h0 : γ 0 = C.vertex) (h1 : γ 1 = C.vertex) :
    polygon4gPathBoundary γ = 0 := by
  rw [polygon4gPathBoundary, h0, h1, sub_self]

/-- The singular zero-chain at the unique cellular vertex. -/
noncomputable def polygon4gSingularVertexChain
    {g : ℕ} (C : Polygon4gCellularModel g) : Polygon4gSingularC0 g :=
  Finsupp.single C.vertex (1 : ℤ)

/-- The singular one-chain associated to the cellular boundary word:
the abelianised word coefficients on the recorded edge-path generators. -/
def polygon4gBoundaryWordChain
    {g : ℕ} {C : Polygon4gCellularModel g}
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gSingularC1 g C D :=
  ⟨edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord⟩

/-- The cellular-to-singular chain map and the singular proxy
boundaries used by the polygon comparison.  This is deliberately
chain-level: the fields are maps between chain modules and explicit
boundary operators, not propositions about endpoints alone. -/
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
  /-- On every one-cell generator, the singular boundary is target minus
  source for the corresponding path. -/
  boundaryC1_on_basis :
    ∀ e : Fin (2 * g),
      singularBoundaryC1 (mapC1 (polygon4gCellularBasis e)) =
        polygon4gPathBoundary (D.oneCells.edgePath e)
  /-- The characteristic disk boundary is represented by the boundary-word
  one-chain. -/
  boundaryC2_on_face :
    singularBoundaryC2 (mapC2 polygon4gCellularC2Face) =
      polygon4gBoundaryWordChain D

/-- The concrete cellular-to-singular chain map carried by the project-side
polygon data. -/
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

/-- The concrete cellular-to-singular map sends a cellular one-cell
generator to the actual singular edge chain after realizing the project
side `Polygon4gSingularC1` wrapper as concrete singular chains. -/
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

/-- The zero-skeleton of the standard polygonal cellular model. -/
def Polygon4gZeroSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  x = C.vertex

/-- The one-skeleton of the standard polygonal cellular model, represented
project-side by the unique vertex and the points on the recorded one-cell
loops. -/
def Polygon4gOneSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  x = C.vertex ∨ ∃ e : Fin (2 * g), ∃ t : Set.Icc (0 : ℝ) 1, C.oneCellPath e t = x

/-- The two-skeleton of the standard polygonal cellular model, represented
project-side as the image of the quotient disk map. -/
def Polygon4gTwoSkeleton
    (g : ℕ) (_C : Polygon4gCellularModel g) (x : Polygon4g g) : Prop :=
  ∃ z : DiskC, Polygon4g.mk g z = x

/-- Every point of `Polygon4g g` lies in the project-side two-skeleton. -/
theorem polygon4g_mem_twoSkeleton
    (g : ℕ) (C : Polygon4gCellularModel g) (x : Polygon4g g) :
    Polygon4gTwoSkeleton g C x := by
  induction x using Quotient.inductionOn with
  | h z => exact ⟨z, rfl⟩

/-- Chain-level support predicates for the singular chains used in the
filtered comparison.  The predicates are stated on chains, not just on
individual cellular attaching maps. -/
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

/-- The associated-graded degree-one comparison as a real linear
equivalence from cellular one-generators to the singular edge-chain
wrapper.  This is intentionally not a reflexive equivalence between
aliases. -/
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

/-- Degree-zero correctness of the comparison data: the unique
zero-cell maps to the singular class of the polygon vertex. -/
structure Polygon4gCellularSingularChainMapDegreeZero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop where
  /-- The comparison's zero-cell representative is the model vertex. -/
  vertex_eq_model : D.zeroCell.vertex = C.vertex
  /-- The zero-cell representative lies in the zero-skeleton. -/
  vertex_mem_zeroSkeleton :
    Polygon4gZeroSkeleton g C D.zeroCell.vertex

/-- Degree-one correctness of the comparison data: each oriented
one-cell maps to the corresponding singular edge path, and its singular
boundary agrees with the zero cellular boundary at the unique vertex. -/
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
  /-- There is a concrete chain map whose degree-one singular boundary is
  the path-chain boundary on each cellular one-cell generator. -/
  singular_path_boundary_formula :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      ∀ e : Fin (2 * g),
        M.singularBoundaryC1 (M.mapC1 (polygon4gCellularBasis e)) =
          polygon4gPathBoundary (D.oneCells.edgePath e)
  /-- Since the edge representatives are based loops, their singular
  path-chain boundaries vanish. -/
  singular_path_boundary_zero :
    ∀ e : Fin (2 * g), polygon4gPathBoundary (D.oneCells.edgePath e) = 0
  /-- Consequently the chain-level singular boundary of each mapped one-cell
  generator vanishes. -/
  singular_chain_boundary_zero :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      ∀ e : Fin (2 * g),
        M.singularBoundaryC1 (M.mapC1 (polygon4gCellularBasis e)) = 0
  /-- Every point of each comparison edge is supported on the one-skeleton. -/
  edgePath_mem_oneSkeleton :
    ∀ e : Fin (2 * g), ∀ t : Set.Icc (0 : ℝ) 1,
      Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)

/-- Degree-two correctness of the comparison data: the two-cell
attaching map is sent to the singular boundary represented by the
surface word, whose abelianised boundary is the cellular formula. -/
structure Polygon4gCellularSingularChainMapDegreeTwoAttaching
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop where
  /-- The comparison's two-cell characteristic map is the quotient map. -/
  characteristic_eq_mk :
    ∀ z, D.twoCell.characteristic.characteristic z =
      Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z)
  /-- The comparison's two-cell characteristic map agrees pointwise with
  the cellular model's characteristic map. -/
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
  /-- The singular boundary of the mapped characteristic disk is the
  boundary-word one-chain. -/
  singular_disk_boundary_formula :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      M.singularBoundaryC2 (M.mapC2 polygon4gCellularC2Face) =
        polygon4gBoundaryWordChain D
  /-- The boundary-word one-chain has exactly the abelianised word
  coefficients. -/
  boundaryWord_chain_coefficients :
    (polygon4gBoundaryWordChain D).coeff =
      edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord
  /-- The boundary-word singular one-chain vanishes because the surface
  relator abelianises to zero. -/
  boundaryWord_chain_zero : polygon4gBoundaryWordChain D = 0
  /-- The model cellular two-boundary formula is available. -/
  cellular_two_boundary_formula : Polygon4gTwoCellBoundaryAbelianizedRelator g C

/-- **Comparison leaf 2a.** The comparison data is correct in degree
zero. -/
theorem polygon4g_cellular_singular_chain_map_degree_zero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D :=
  ⟨D.zeroCell.vertex_eq_model, D.zeroCell.vertex_eq_model⟩

/-- **Comparison leaf 2b.** The comparison data is compatible with the
one-cell boundary calculation. -/
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

/-- **Comparison leaf 2c.** The comparison data is compatible with the
two-cell attaching map. -/
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

/-- Correctness of the comparison data: it is compatible with the
cellular and singular differentials and computes the intended attaching
maps in dimensions `0`, `1`, and `2`. -/
abbrev Polygon4gCellularSingularChainMapCorrect
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) : Prop :=
  Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D ∧
    Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D ∧
      Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D

/-- **Comparison assembly 2.** The chosen comparison data gives the
correct chain-level cellular-to-singular comparison map.  This is now
assembled from the degree `0`, `1`, and `2` correctness leaves. -/
theorem polygon4g_cellular_singular_chain_map_correct
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapCorrect g C h_boundary D :=
by
  exact ⟨polygon4g_cellular_singular_chain_map_degree_zero g C h_boundary D,
    polygon4g_cellular_singular_chain_map_degree_one_boundary g C h_boundary D,
    polygon4g_cellular_singular_chain_map_degree_two_attaching g C h_boundary D⟩

/-- The comparison map respects the cellular filtration on singular
chains.  For the polygon this says cells in the `n`-skeleton map into
singular chains supported on the `n`-skeleton, for `n = 0, 1, 2`. -/
structure Polygon4gCellularSingularFiltrationCompatible
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D) : Prop where
  /-- A concrete chain map, chain-level support predicates, filtered image
  statements, and boundary-preservation statements for the singular-chain
  filtration. -/
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
  /-- The zero-cell image is supported on the zero-skeleton. -/
  zeroCell_supported : Polygon4gZeroSkeleton g C D.zeroCell.vertex
  /-- The one-cell images are supported on the one-skeleton. -/
  oneCells_supported :
    ∀ e : Fin (2 * g), ∀ t : Set.Icc (0 : ℝ) 1,
      Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)
  /-- The two-cell image is supported on the two-skeleton. -/
  twoCell_supported :
    ∀ z : C.disk.diskSource.carrier,
      Polygon4gTwoSkeleton g C (D.twoCell.characteristic.characteristic z)

/-- The associated graded map of the cellular-to-singular comparison is
the identity on the cellular generators in degrees relevant to `H₁`.
This packages the local relative-homology calculation for each open
cell. -/
structure Polygon4gCellularSingularAssociatedGradedH1Iso
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D)
    (_h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C _h_boundary D h_correct) :
    Prop where
  /-- The associated graded degree-zero generator is represented by the
  model vertex. -/
  graded_zero_generator : D.zeroCell.vertex = C.vertex
  /-- The associated graded degree-one generators are represented by the
  model one-cell loops. -/
  graded_one_generators : D.oneCells.edgePath = C.oneCellPath
  /-- The concrete associated-graded degree-one map is the degree-one
  component of a real cellular-to-singular chain map. -/
  graded_one_map_eq_chainMap :
    ∃ M : Polygon4gCellularToSingularChainMap g C D,
      (polygon4g_cellularH1_to_singularC1_equiv g C D).toLinearMap = M.mapC1
  /-- The associated graded degree-two boundary is the abelianised surface
  relator, hence zero in cellular one-chains. -/
  graded_two_boundary_zero :
    edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord = 0
  /-- The project-side degree-one associated-graded map is an isomorphism
  from cellular `H₁` generators to singular edge-chain generators. -/
  graded_one_isomorphism :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] Polygon4gSingularC1 g C D)

/-- A concrete bridge from the project-side singular one-chain wrapper
used by the polygon comparison to Mathlib's actual singular `H₁`.
This is the precise topological input still missing from the current
API: the filtered/five-lemma argument must construct this equivalence
from the chain map and filtration data, not by definitional equality. -/
structure Polygon4gSingularC1RealizesSingularH1
    (g : ℕ) (C : Polygon4gCellularModel g)
    (D : Polygon4gCellularSingularComparisonData g C) where
  /-- The resulting equivalence between the project-side edge-chain
  associated-graded model and Mathlib singular homology. -/
  equiv : Polygon4gSingularC1 g C D ≃ₗ[ℤ] singularH1 (Polygon4g g)
  /-- The chain-level comparison whose degree-one component gives the
  project-side edge-chain model. -/
  chainMap : Polygon4gCellularToSingularChainMap g C D
  /-- The chain map realizes the associated-graded degree-one comparison,
  so the bridge is tied to the cellular-to-singular chain data rather than
  to an arbitrary algebraic isomorphism. -/
  chainMap_degree_one :
    chainMap.mapC1 = (polygon4g_cellularH1_to_singularC1_equiv g C D).toLinearMap

/-- If the concrete linear edge-chain class map is bijective, it gives
the realization data required by the filtered Hurewicz comparison.
This isolates the remaining topological content as bijectivity of the
actual edge-chain map into Mathlib singular `H₁`. -/
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

/-- Conditional form of the filtered comparison: once the project-side
singular edge-chain wrapper is identified with Mathlib `singularH1`
by a chain-level realization, the existing associated-graded cellular
isomorphism gives the desired cellular-to-singular `H₁` equivalence. -/
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

/-- Conditional concrete comparison via the actual linear edge-chain map
into Mathlib singular `H₁`.  This is the same Hurewicz conclusion as the
frontier theorem below, with the remaining topological content isolated
as bijectivity of `Polygon4gSingularC1.toSingularH1LinearMap`. -/
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

/-- Concrete frontier theorem: a cellular-to-singular comparison with
inspectable chain-level boundary compatibility, skeleton support, and
associated-graded generator identifications induces the expected
isomorphism on first homology.

This is the remaining missing theorem boundary: it is the filtered
cellular/singular comparison in degree `1`, specialized to the standard
two-dimensional `Polygon4g` cellular model and stated over concrete
project-side data rather than opaque predicates. -/
theorem polygon4g_cellular_to_singular_H1_iso_from_concrete_comparison
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h0 : Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D)
    (h1 : Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D)
    (h2 : Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D)
    (h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C h_boundary D ⟨h0, h1, h2⟩)
    (_h_graded :
      Polygon4gCellularSingularAssociatedGradedH1Iso
        g C h_boundary D ⟨h0, h1, h2⟩ h_filtration) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  -- Frontier: the concrete comparison data above is enough to state the
  -- usual cellular-to-singular theorem for this finite CW model, but the
  -- project still lacks the filtered singular-chain comparison/five-lemma
  -- implementation that turns those fields into an actual `singularH1` iso.
  sorry

/-- **Comparison leaf 3a.** The correct comparison map is compatible
with the cellular filtration. -/
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

/-- **Comparison leaf 3b.** The associated graded comparison is an
isomorphism in the degrees that control first homology. -/
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

/-- **Comparison leaf 3c.** A filtration-compatible comparison whose
associated graded map is an isomorphism in the relevant degrees induces
the expected isomorphism on first homology.  Bottom-up route: specialise
the cellular homology theorem / filtration spectral sequence argument
to this finite two-dimensional CW complex. -/
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

/-- **Comparison assembly 3.** A correct cellular-to-singular comparison
map induces the expected isomorphism on first homology.  This theorem is
sorry-free; the remaining filtered-comparison work is isolated in
`polygon4g_cellular_to_singular_H1_iso_from_concrete_comparison`. -/
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

/-- **Comparison assembly.** Cellular homology of the standard
polygonal CW model agrees with singular homology.  This theorem is now
sorry-free; the remaining bottom-up comparison work is isolated in the
concrete filtered-comparison frontier above. -/
theorem polygon4g_cellular_to_singularH1_comparison
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) :=
by
  obtain ⟨D⟩ := polygon4g_cellular_singular_comparison_data g C _h_boundary
  exact polygon4g_cellular_singular_H1_iso_of_chain_map g C _h_boundary D
    (polygon4g_cellular_singular_chain_map_correct g C _h_boundary D)

/-- **Hurewicz/cellular bridge assembly.** A named project-side
comparison from the computed cellular group to singular `H₁`. -/
theorem polygon4g_cellularH1_to_singularH1 (g : ℕ) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact polygon4g_cellular_to_singularH1_comparison g C
    (polygon4g_cellular_boundary_formula g C)

end JacobianChallenge.Periods
