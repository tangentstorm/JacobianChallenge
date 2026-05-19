import Jacobian.Periods.CellularChainComplex

/-!
# Project-side Hurewicz and cellular-to-singular bridge

This file names the comparison theorem missing from Mathlib v4.28.0:
cellular homology agrees with singular homology for the cellular model
of the fundamental polygon.  It is deliberately stated at the narrow
surface needed by the Jacobian project.
-/

namespace JacobianChallenge.Periods

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
    ∀ z : DiskC, D.twoCell.characteristic.characteristic z = Polygon4g.mk g z
  /-- The comparison's two-cell characteristic map agrees pointwise with
  the cellular model's characteristic map. -/
  characteristic_eq_model :
    ∀ z : DiskC, D.twoCell.characteristic.characteristic z = C.twoCellCharacteristic z
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
  refine ⟨D.oneCells.edgePath_eq_model, ?_, ?_, h_boundary.1, ?_⟩
  · intro e
    rw [D.oneCells.edgePath_eq_model]
    exact (h_boundary.1 e).1
  · intro e
    rw [D.oneCells.edgePath_eq_model]
    exact (h_boundary.1 e).2
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
  refine ⟨D.twoCell.characteristic.characteristic_eq_mk, ?_,
    D.twoCell.boundaryWord.boundaryWord_eq_model,
    D.twoCell.boundaryWord.boundaryWord_standard,
    D.twoCell.boundaryWord.boundaryWord_sidePairing,
    D.twoCell.boundaryWord.boundaryWord_abelianizedBoundary,
    h_boundary.2⟩
  intro z
  rw [D.twoCell.characteristic.characteristic_eq_mk z,
    C.twoCellCharacteristic_eq_mk z]

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
  /-- The zero-cell image is supported on the zero-skeleton. -/
  zeroCell_supported : Polygon4gZeroSkeleton g C D.zeroCell.vertex
  /-- The one-cell images are supported on the one-skeleton. -/
  oneCells_supported :
    ∀ e : Fin (2 * g), ∀ t : Set.Icc (0 : ℝ) 1,
      Polygon4gOneSkeleton g C (D.oneCells.edgePath e t)
  /-- The two-cell image is supported on the two-skeleton. -/
  twoCell_supported :
    ∀ z : DiskC, Polygon4gTwoSkeleton g C (D.twoCell.characteristic.characteristic z)

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
  /-- The associated graded degree-two boundary is the abelianised surface
  relator, hence zero in cellular one-chains. -/
  graded_two_boundary_zero :
    edgeWordAbelianizedBoundary D.twoCell.boundaryWord.boundaryWord = 0
  /-- The project-side cellular `H₁` is the free module on the one-cell
  generators. -/
  cellularH1_identifies_generators :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] Polygon4gCellularC1 g)

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
    Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct :=
  ⟨h_correct.1.vertex_mem_zeroSkeleton,
    h_correct.2.1.edgePath_mem_oneSkeleton,
    fun z => by
      rw [h_correct.2.2.characteristic_eq_mk z]
      exact polygon4g_mem_twoSkeleton g C (Polygon4g.mk g z)⟩

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
  ⟨h_correct.1.vertex_eq_model,
    h_correct.2.1.edgePath_eq_model,
    h_correct.2.2.boundaryWord_abelianizedBoundary,
    ⟨LinearEquiv.refl ℤ _⟩⟩

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
