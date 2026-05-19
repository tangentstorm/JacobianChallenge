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

/-- Degree-zero correctness of the comparison data: the unique
zero-cell maps to the singular class of the polygon vertex. -/
opaque Polygon4gCellularSingularChainMapDegreeZero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (_D : Polygon4gCellularSingularComparisonData g C) : Prop

/-- **Comparison leaf 2a.** The comparison data is correct in degree
zero. -/
theorem polygon4g_cellular_singular_chain_map_degree_zero
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeZero g C h_boundary D := by
  -- Blocker: degree-zero correctness requires evaluating the comparison map
  -- on the actual zero-cell generator and comparing it with the singular class
  -- of the polygon vertex.  The comparison data now exposes the vertex, but
  -- there is still no project-side singular chain map to evaluate.
  sorry

/-- Degree-one correctness of the comparison data: each oriented
one-cell maps to the corresponding singular edge path, and its singular
boundary agrees with the zero cellular boundary at the unique vertex. -/
opaque Polygon4gCellularSingularChainMapDegreeOneBoundary
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (_D : Polygon4gCellularSingularComparisonData g C) : Prop

/-- **Comparison leaf 2b.** The comparison data is compatible with the
one-cell boundary calculation. -/
theorem polygon4g_cellular_singular_chain_map_degree_one_boundary
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeOneBoundary g C h_boundary D := by
  -- Blocker: this is the chain-map boundary identity for each one-cell.  It
  -- needs an actual singular-chain boundary operator and comparison map.  The
  -- edge paths and endpoints are exposed by `D`, but the chain-level map is
  -- still a frontier theorem.
  sorry

/-- Degree-two correctness of the comparison data: the two-cell
attaching map is sent to the singular boundary represented by the
surface word, whose abelianised boundary is the cellular formula. -/
opaque Polygon4gCellularSingularChainMapDegreeTwoAttaching
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (_D : Polygon4gCellularSingularComparisonData g C) : Prop

/-- **Comparison leaf 2c.** The comparison data is compatible with the
two-cell attaching map. -/
theorem polygon4g_cellular_singular_chain_map_degree_two_attaching
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapDegreeTwoAttaching g C h_boundary D := by
  -- Blocker: this is the attaching-map compatibility for the two-cell.  The
  -- proof must expand the boundary of the singular disk as the labelled
  -- commutator word and compare it with the cellular two-boundary formula.
  -- The comparison record exposes the characteristic map and boundary word,
  -- but not the singular-chain computation of the disk boundary.
  sorry

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
opaque Polygon4gCellularSingularFiltrationCompatible
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D) : Prop

/-- **Comparison leaf 3a.** The correct comparison map is compatible
with the cellular filtration. -/
theorem polygon4g_cellular_singular_filtration_compatible
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D) :
    Polygon4gCellularSingularFiltrationCompatible g C h_boundary D h_correct := by
  -- Blocker: filtration compatibility is a theorem about supports in the
  -- cellular skeleta.  The present cellular/comparison data has no skeleton
  -- filtration, support predicate, or chain map whose image can be inspected.
  sorry

/-- The associated graded map of the cellular-to-singular comparison is
the identity on the cellular generators in degrees relevant to `H₁`.
This packages the local relative-homology calculation for each open
cell. -/
opaque Polygon4gCellularSingularAssociatedGradedH1Iso
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (h_correct : Polygon4gCellularSingularChainMapCorrect g C _h_boundary D)
    (_h_filtration :
      Polygon4gCellularSingularFiltrationCompatible g C _h_boundary D h_correct) : Prop

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
      g C h_boundary D h_correct h_filtration := by
  -- Blocker: associated-graded comparison needs the local relative homology
  -- calculation for each open cell and a computed map on those generators.
  -- The opaque predicate records the result but supplies no relative chain
  -- complexes or generator-level map to prove it from.
  sorry

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
  -- Blocker: this is the spectral-sequence/five-lemma comparison step from a
  -- filtration-compatible chain map with associated-graded isomorphism to an
  -- isomorphism on `H₁`.  The hypotheses are project-side opaque predicates,
  -- not an actual filtered chain map in Mathlib's homological algebra API.
  sorry

/-- **Comparison assembly 3.** A correct cellular-to-singular comparison
map induces the expected isomorphism on first homology.  This theorem is
sorry-free; the filtration-theorem work is isolated in leaves 3a--3c. -/
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
three leaves above. -/
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
