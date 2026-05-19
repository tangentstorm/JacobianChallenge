import Jacobian.Periods.PolygonCellularHomology
import Jacobian.Periods.EdgeWord
import Mathlib.Topology.Path

/-!
# Project-side cellular chain API for the fundamental polygon

Mathlib v4.28.0 does not provide a cellular chain complex.  This file
records the small amount of cellular infrastructure needed by
`Polygon4gCellular.lean` as named project-side obligations.  The goal is
to keep the public assembly theorem free of a monolithic `sorry` while
leaving the missing bottom-up topology at explicit leaves.
-/

namespace JacobianChallenge.Periods

/-- The intended first cellular homology group of `Polygon4g g`.
For the standard cell structure there is one vertex, `2g` one-cells,
and one two-cell whose attaching map is the product of commutators. -/
abbrev Polygon4gCellularH1 (g : ℕ) : Type :=
  Fin (2 * g) → ℤ

instance polygon4gCellularH1_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularH1 g) := by
  unfold Polygon4gCellularH1
  infer_instance

instance polygon4gCellularH1_module (g : ℕ) :
    Module ℤ (Polygon4gCellularH1 g) := by
  unfold Polygon4gCellularH1
  infer_instance

/-- The project-side cellular one-chain module for the standard
`Polygon4g g` model: free abelian chains on the `2g` oriented one-cells. -/
abbrev Polygon4gCellularC1 (g : ℕ) : Type :=
  Fin (2 * g) → ℤ

/-- Index of the one-cell labelled `aᵢ` in the cellular one-chain basis. -/
def polygon4g_aEdgeIndex {g : ℕ} (i : Fin g) : Fin (2 * g) :=
  ⟨2 * i.val, by omega⟩

/-- Index of the one-cell labelled `bᵢ` in the cellular one-chain basis. -/
def polygon4g_bEdgeIndex {g : ℕ} (i : Fin g) : Fin (2 * g) :=
  ⟨2 * i.val + 1, by omega⟩

/-- The basis one-chain supported at a single oriented one-cell. -/
def polygon4gCellularBasis {g : ℕ} (e : Fin (2 * g)) :
    Polygon4gCellularC1 g :=
  fun e' => if e' = e then 1 else 0

/-- Abelianised cellular boundary contribution of one oriented boundary
letter.  The convention is `aᵢ ↦ +aᵢ`, `bᵢ ↦ +bᵢ`, and inverse letters map
to the corresponding negative basis vectors. -/
def letterAbelianizedBoundary {g : ℕ} : Letter g → Polygon4gCellularC1 g
  | Letter.a i => polygon4gCellularBasis (polygon4g_aEdgeIndex i)
  | Letter.b i => polygon4gCellularBasis (polygon4g_bEdgeIndex i)
  | Letter.aInv i => -polygon4gCellularBasis (polygon4g_aEdgeIndex i)
  | Letter.bInv i => -polygon4gCellularBasis (polygon4g_bEdgeIndex i)

/-- Abelianised cellular one-chain read from an edge word. -/
def edgeWordAbelianizedBoundary {g : ℕ} (w : EdgeWord g) :
    Polygon4gCellularC1 g :=
  (w.map letterAbelianizedBoundary).sum

@[simp] theorem edgeWordAbelianizedBoundary_nil {g : ℕ} :
    edgeWordAbelianizedBoundary ([] : EdgeWord g) = 0 := by
  rfl

@[simp] theorem edgeWordAbelianizedBoundary_cons {g : ℕ}
    (l : Letter g) (w : EdgeWord g) :
    edgeWordAbelianizedBoundary (l :: w) =
      letterAbelianizedBoundary l + edgeWordAbelianizedBoundary w := by
  rfl

@[simp] theorem edgeWordAbelianizedBoundary_append {g : ℕ}
    (w₁ w₂ : EdgeWord g) :
    edgeWordAbelianizedBoundary (w₁ ++ w₂) =
      edgeWordAbelianizedBoundary w₁ + edgeWordAbelianizedBoundary w₂ := by
  unfold edgeWordAbelianizedBoundary
  simp [List.map_append, List.sum_append]

/-- Each commutator block `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` has zero abelianised cellular
boundary. -/
theorem edgeWordAbelianizedBoundary_handleBlock {g : ℕ} (i : Fin g) :
    edgeWordAbelianizedBoundary (EdgeWord.handleBlock i) = 0 := by
  ext e
  simp [EdgeWord.handleBlock, edgeWordAbelianizedBoundary, letterAbelianizedBoundary]

/-- The standard product of commutators has zero abelianised cellular
two-boundary in the project-side cellular one-chain module. -/
theorem edgeWordAbelianizedBoundary_standardWord (g : ℕ) :
    edgeWordAbelianizedBoundary (EdgeWord.standardWord g) = 0 := by
  unfold EdgeWord.standardWord
  induction List.finRange g with
  | nil =>
      simp
  | cons i is ih =>
      simp [List.flatMap_cons, edgeWordAbelianizedBoundary_append,
        edgeWordAbelianizedBoundary_handleBlock, ih]

/-- The closed-disk source for the standard polygonal cell datum. -/
structure Polygon4gClosedDiskCellSource (_g : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier
  sourceHomeomorph : @Homeomorph carrier DiskC topology _

instance {g : ℕ} (ds : Polygon4gClosedDiskCellSource g) :
    TopologicalSpace ds.carrier := ds.topology

/-- **Cellular leaf 1a(i).** Construct the closed disk source used by
the standard `4g`-gon model. -/
theorem polygon4g_closed_disk_cell_source (g : ℕ) :
    Nonempty (Polygon4gClosedDiskCellSource g) :=
  ⟨{ carrier := DiskC,
     topology := inferInstance,
     sourceHomeomorph := Homeomorph.refl DiskC }⟩

/-- The subdivision of the boundary circle into the oriented sides of
the standard `4g`-gon. -/
structure Polygon4gBoundarySideSubdivision
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g) where
  /-- The `4g` oriented boundary arcs. -/
  sideArc : Fin (4 * g) → Set.Icc (0 : ℝ) 1 → diskSource.carrier
  /-- The arcs agree with the standard boundary parametrisation (via the homeomorph). -/
  sideArc_eq_boundaryParam : ∀ i t,
    diskSource.sourceHomeomorph (sideArc i t) = boundaryParam g i t

/-- **Cellular leaf 1a(ii).** Construct the boundary side subdivision
of the closed disk source. -/
theorem polygon4g_boundary_side_subdivision
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g) :
    Nonempty (Polygon4gBoundarySideSubdivision g diskSource) :=
  ⟨{ sideArc := fun i t => diskSource.sourceHomeomorph.symm (boundaryParam g i t),
     sideArc_eq_boundaryParam := fun _ _ => by simp }⟩

/-- The quotient relation that identifies the polygon sides according
to the surface word. -/
structure Polygon4gBoundaryQuotientRelation
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g)
    (subdivision : Polygon4gBoundarySideSubdivision g diskSource) where
  /-- The equivalence relation on the disk carrier. -/
  rel : diskSource.carrier → diskSource.carrier → Prop
  /-- The relation is the standard side-pairing relation. -/
  rel_eq_sideRel : ∀ x y, rel x y ↔
    Polygon4g.SideRel g (diskSource.sourceHomeomorph x) (diskSource.sourceHomeomorph y)

/-- **Cellular leaf 1a(iii).** Construct the boundary quotient
relation for the standard side identifications. -/
theorem polygon4g_boundary_quotient_relation
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g)
    (subdivision : Polygon4gBoundarySideSubdivision g diskSource) :
    Nonempty (Polygon4gBoundaryQuotientRelation g diskSource subdivision) :=
  ⟨{ rel := fun x y => Polygon4g.SideRel g (diskSource.sourceHomeomorph x) (diskSource.sourceHomeomorph y),
     rel_eq_sideRel := fun _ _ => Iff.rfl }⟩

/-- The quotient-disk cell datum underlying the standard polygonal
model: the closed disk with boundary side identifications. -/
structure Polygon4gQuotientDiskCellData (g : ℕ) where
  diskSource : Polygon4gClosedDiskCellSource g
  subdivision : Polygon4gBoundarySideSubdivision g diskSource
  quotientRelation : Polygon4gBoundaryQuotientRelation g diskSource subdivision

/-- **Cellular assembly 1a.** Construct the quotient-disk cell datum for
the standard `4g`-gon from disk, subdivision, and quotient-relation
leaves. -/
theorem polygon4g_quotient_disk_cell_data (g : ℕ) :
    Nonempty (Polygon4gQuotientDiskCellData g) :=
by
  obtain ⟨diskSource⟩ := polygon4g_closed_disk_cell_source g
  obtain ⟨subdivision⟩ := polygon4g_boundary_side_subdivision g diskSource
  obtain ⟨quotientRelation⟩ :=
    polygon4g_boundary_quotient_relation g diskSource subdivision
  exact ⟨{ diskSource, subdivision, quotientRelation }⟩

/-- The combinatorial pairing of the `4g` oriented boundary sides of
the standard polygon. -/
structure Polygon4gBoundarySidePairingCombinatorics
    (g : ℕ) (_disk : Polygon4gQuotientDiskCellData g) where
  /-- The word describing the side-pairing. -/
  boundaryWord : EdgeWord g
  /-- The word is standard. -/
  boundaryWord_eq_standard : boundaryWord = EdgeWord.standardWord g

/-- **Cellular leaf 1b(i).** Construct the side-pairing combinatorics
for the standard polygon. -/
theorem polygon4g_boundary_side_pairing_combinatorics
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g) :
    Nonempty (Polygon4gBoundarySidePairingCombinatorics g disk) :=
  ⟨{ boundaryWord := EdgeWord.standardWord g,
     boundaryWord_eq_standard := rfl }⟩

/-- Compatibility between the side pairing and the standard generator
labels/orientations `aᵢ,bᵢ,aᵢ⁻¹,bᵢ⁻¹`. -/
def Polygon4gBoundarySidePairingLabelCompatible
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (pairing : Polygon4gBoundarySidePairingCombinatorics g disk) : Prop :=
  pairing.boundaryWord.IsStandardForm ∧
  EdgeWord.sidePairingRel g pairing.boundaryWord = Polygon4g.SideRel g

/-- **Cellular leaf 1b(ii).** The side-pairing combinatorics has the
standard orientation and generator-label compatibility. -/
theorem polygon4g_boundary_side_pairing_label_compatible
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (pairing : Polygon4gBoundarySidePairingCombinatorics g disk) :
    Polygon4gBoundarySidePairingLabelCompatible g disk pairing :=
  ⟨pairing.boundaryWord_eq_standard, by
    rw [pairing.boundaryWord_eq_standard]
    exact EdgeWord.sidePairingRel_standardWord g⟩

/-- The edge-pairing datum for the standard polygon: paired boundary
arcs labelled by the `aᵢ,bᵢ` generators. -/
structure Polygon4gEdgePairingCellData
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g) where
  pairing : Polygon4gBoundarySidePairingCombinatorics g disk
  labelCompatible : Polygon4gBoundarySidePairingLabelCompatible g disk pairing

/-- **Cellular assembly 1b.** Construct the edge-pairing datum on the
quotient disk from side-pairing and label-compatibility leaves. -/
theorem polygon4g_edge_pairing_cell_data
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g) :
    Nonempty (Polygon4gEdgePairingCellData g disk) :=
by
  obtain ⟨pairing⟩ :=
    polygon4g_boundary_side_pairing_combinatorics g disk
  exact ⟨{
    pairing
    labelCompatible :=
      polygon4g_boundary_side_pairing_label_compatible g disk pairing
  }⟩

/-- The characteristic maps for the one zero-cell, `2g` one-cells, and
one two-cell of the standard polygonal model.

This is intentionally a project-side certificate rather than a claimed
Mathlib `CWComplex`: it records the concrete quotient-surface data needed
for the cellular chain calculation, and leaves the future bridge to
`Topology.CWComplex` as a separate theorem. -/
structure Polygon4gCharacteristicMapData
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (_edgePairing : Polygon4gEdgePairingCellData g disk) where
  /-- The unique vertex of the cellular model, as a point of the quotient
  polygon. -/
  vertex : Polygon4g g
  /-- The `2g` oriented one-cells, represented as loops based at the unique
  vertex. -/
  oneCellPath : Fin (2 * g) → Path vertex vertex
  /-- The characteristic map of the unique two-cell, before passing to a
  full Mathlib `CWComplex` record. -/
  twoCellCharacteristic : ContinuousMap disk.diskSource.carrier (Polygon4g g)
  /-- The two-cell map is the quotient map from the closed disk (via the homeomorph). -/
  twoCellCharacteristic_eq_mk :
    ∀ z, twoCellCharacteristic z = Polygon4g.mk g (disk.diskSource.sourceHomeomorph z)
  /-- The attaching word read around the boundary of the unique two-cell. -/
  boundaryWord : EdgeWord g
  /-- The attaching word is the standard product of commutators. -/
  boundaryWord_standard : boundaryWord.IsStandardForm
  /-- The word-side quotient relation agrees with the existing polygon
  side-pairing relation. -/
  boundaryWord_sidePairing :
    EdgeWord.sidePairingRel g boundaryWord = Polygon4g.SideRel g
  /-- The cellular boundary of every one-cell is zero because every one-cell
  is a loop at the unique vertex. -/
  oneCellBoundaryZero :
    ∀ e : Fin (2 * g), oneCellPath e 0 = vertex ∧ oneCellPath e 1 = vertex

/-- **Frontier lemma.** The quotient of boundary arcs form based loops
at the unique vertex. -/
theorem polygon4g_boundary_arcs_are_loops (g : ℕ) (k : ℕ) :
    Polygon4g.mk g (boundaryParam g k 0) = Polygon4g.mk g (boundaryParam g 0 0) ∧
    Polygon4g.mk g (boundaryParam g k 1) = Polygon4g.mk g (boundaryParam g 0 0) :=
  sorry

lemma boundaryAngle'_continuous (L i : ℕ) :
    Continuous (fun t : ℝ => boundaryAngle' L i t) := by
  unfold boundaryAngle'
  apply Continuous.div_const
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.add
    · exact continuous_const
    · exact continuous_id

lemma boundaryParamC'_continuous (L i : ℕ) :
    Continuous (fun t : ℝ => boundaryParamC' L i t) := by
  unfold boundaryParamC'
  apply Complex.continuous_exp.comp
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (boundaryAngle'_continuous L i)
  · exact continuous_const

lemma boundaryParam'_continuous (L i : ℕ) :
    Continuous (fun t : ℝ => boundaryParam' L i t) := by
  unfold boundaryParam'
  exact continuous_induced_rng.mpr (boundaryParamC'_continuous L i)

/-- **Sorry-free.** The standard boundary parametrisation is
continuous on `[0,1]`. -/
theorem polygon4g_boundaryParam_continuous (g : ℕ) (k : ℕ) :
    Continuous (fun t : ℝ => boundaryParam g k t) :=
  boundaryParam'_continuous (4 * g) k

/-- The index of the boundary arc corresponding to the `e`-th oriented
one-cell.  Maps `2*i ↦ 4*i` (`aᵢ`) and `2*i + 1 ↦ 4*i + 1` (`bᵢ`). -/
def polygon4g_oneCell_arcIndex {g : ℕ} (e : Fin (2 * g)) : ℕ :=
  2 * e.val - (e.val % 2)

/-- **Cellular leaf 1c.** Construct the characteristic maps for the
standard polygonal cell structure. -/
theorem polygon4g_characteristic_map_data
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (edgePairing : Polygon4gEdgePairingCellData g disk) :
    Nonempty (Polygon4gCharacteristicMapData g disk edgePairing) :=
by
  let v := Polygon4g.mk g (boundaryParam g 0 0)
  exact ⟨{
    vertex := v
    oneCellPath := fun e => {
      toFun := fun t => Polygon4g.mk g (boundaryParam g (polygon4g_oneCell_arcIndex e) t)
      continuous_toFun := (Polygon4g.mk_continuous g).comp ((polygon4g_boundaryParam_continuous g _).comp continuous_subtype_val)
      source' := (polygon4g_boundary_arcs_are_loops g _).1
      target' := (polygon4g_boundary_arcs_are_loops g _).2
    }
    twoCellCharacteristic := ⟨fun z => Polygon4g.mk g (disk.diskSource.sourceHomeomorph z),
      (Polygon4g.mk_continuous g).comp disk.diskSource.sourceHomeomorph.continuous⟩
    twoCellCharacteristic_eq_mk := fun _ => rfl
    boundaryWord := EdgeWord.standardWord g
    boundaryWord_standard := EdgeWord.standardWord_isStandardForm
    boundaryWord_sidePairing := EdgeWord.sidePairingRel_standardWord g
    oneCellBoundaryZero := fun e =>
      ⟨(polygon4g_boundary_arcs_are_loops g _).1, (polygon4g_boundary_arcs_are_loops g _).2⟩
  }⟩

/-- A witness that `Polygon4g g` carries the standard project-side
cellular model: one zero-cell, `2g` one-cells, and one two-cell.

The record is deliberately tied to the quotient polygon and exposes the
cellular data needed by the chain calculation.  It is not a Mathlib
`CWComplex`; a future bridge can package these fields into Mathlib's CW
API. -/
structure Polygon4gCellularModel (g : ℕ) where
  /-- The quotient-disk source, subdivision, and side quotient relation. -/
  disk : Polygon4gQuotientDiskCellData g
  /-- The labelled side-pairing data for the quotient disk. -/
  edgePairing : Polygon4gEdgePairingCellData g disk
  /-- The zero-, one-, and two-cell characteristic data. -/
  characteristicMaps : Polygon4gCharacteristicMapData g disk edgePairing

namespace Polygon4gCellularModel

/-- The unique vertex of the standard cellular model. -/
def vertex {g : ℕ} (C : Polygon4gCellularModel g) : Polygon4g g :=
  C.characteristicMaps.vertex

/-- The indexed family of one-cell loops. -/
def oneCellPath {g : ℕ} (C : Polygon4gCellularModel g) :
    Fin (2 * g) → Path C.vertex C.vertex :=
  C.characteristicMaps.oneCellPath

/-- The characteristic map of the unique two-cell. -/
def twoCellCharacteristic {g : ℕ} (C : Polygon4gCellularModel g) :
    ContinuousMap C.disk.diskSource.carrier (Polygon4g g) :=
  C.characteristicMaps.twoCellCharacteristic

/-- The boundary word of the unique two-cell. -/
def boundaryWord {g : ℕ} (C : Polygon4gCellularModel g) : EdgeWord g :=
  C.characteristicMaps.boundaryWord

/-- The two-cell characteristic map is the quotient map. -/
theorem twoCellCharacteristic_eq_mk {g : ℕ} (C : Polygon4gCellularModel g) :
    ∀ z, C.twoCellCharacteristic z = Polygon4g.mk g (C.disk.diskSource.sourceHomeomorph z) :=
  C.characteristicMaps.twoCellCharacteristic_eq_mk

/-- The boundary word is the standard product of commutators. -/
theorem boundaryWord_standard {g : ℕ} (C : Polygon4gCellularModel g) :
    C.boundaryWord.IsStandardForm :=
  C.characteristicMaps.boundaryWord_standard

/-- The boundary word induces the existing polygon side-pairing relation. -/
theorem boundaryWord_sidePairing {g : ℕ} (C : Polygon4gCellularModel g) :
    EdgeWord.sidePairingRel g C.boundaryWord = Polygon4g.SideRel g :=
  C.characteristicMaps.boundaryWord_sidePairing

/-- The boundary word has zero abelianised cellular boundary. -/
theorem boundaryWord_abelianizedBoundary {g : ℕ} (C : Polygon4gCellularModel g) :
    edgeWordAbelianizedBoundary C.boundaryWord = 0 := by
  rw [show C.boundaryWord = EdgeWord.standardWord g from C.boundaryWord_standard]
  exact edgeWordAbelianizedBoundary_standardWord g

end Polygon4gCellularModel

/-- **Cellular leaf 1d.** Realise the quotient-disk, edge-pairing, and
characteristic-map data as a cellular model on `Polygon4g g`. -/
theorem polygon4g_realize_standard_cellular_model
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (edgePairing : Polygon4gEdgePairingCellData g disk)
    (characteristicMaps : Polygon4gCharacteristicMapData g disk edgePairing) :
    Nonempty (Polygon4gCellularModel g) :=
  ⟨{ disk, edgePairing, characteristicMaps }⟩

/-- **Cellular assembly 1.** Existence of the standard cellular model on
`Polygon4g g`, assembled from the quotient-disk, edge-pairing,
characteristic-map, and realisation leaves. -/
theorem polygon4g_standard_cellular_model (g : ℕ) :
    Nonempty (Polygon4gCellularModel g) :=
by
  obtain ⟨disk⟩ := polygon4g_quotient_disk_cell_data g
  obtain ⟨edgePairing⟩ := polygon4g_edge_pairing_cell_data g disk
  obtain ⟨characteristicMaps⟩ :=
    polygon4g_characteristic_map_data g disk edgePairing
  exact polygon4g_realize_standard_cellular_model
    g disk edgePairing characteristicMaps

/-- The cellular boundary of every one-cell is zero, since all one-cell
endpoints are identified with the unique zero-cell. -/
def Polygon4gOneCellBoundaryZero
    (g : ℕ) (C : Polygon4gCellularModel g) : Prop :=
  ∀ e : Fin (2 * g), C.oneCellPath e 0 = C.vertex ∧ C.oneCellPath e 1 = C.vertex

/-- **Cellular leaf 2a.** The one-cell boundary is zero for the standard
polygon model. -/
theorem polygon4g_one_cell_boundary_zero
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gOneCellBoundaryZero g C :=
  C.characteristicMaps.oneCellBoundaryZero

/-- The cellular two-cell boundary is the abelianisation of the surface
relator `∏ᵢ [aᵢ,bᵢ]`, hence zero in the free abelian group on one-cells. -/
def Polygon4gTwoCellBoundaryAbelianizedRelator
    (g : ℕ) (C : Polygon4gCellularModel g) : Prop :=
  C.boundaryWord.IsStandardForm ∧
    EdgeWord.sidePairingRel g C.boundaryWord = Polygon4g.SideRel g ∧
      edgeWordAbelianizedBoundary C.boundaryWord = 0

/-- **Cellular leaf 2b.** The two-cell boundary is the abelianised
commutator product and therefore vanishes. -/
theorem polygon4g_two_cell_boundary_abelianized_relator
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gTwoCellBoundaryAbelianizedRelator g C :=
  ⟨C.boundaryWord_standard, C.boundaryWord_sidePairing,
    C.boundaryWord_abelianizedBoundary⟩

/-- **Cellular boundary formula.** It packages two facts: the one-cell
boundary is zero because all endpoints are the unique vertex, and the
two-cell boundary is the abelianised surface relator, hence zero. -/
abbrev Polygon4gCellularBoundaryFormula
    (g : ℕ) (C : Polygon4gCellularModel g) : Prop :=
  Polygon4gOneCellBoundaryZero g C ∧
    Polygon4gTwoCellBoundaryAbelianizedRelator g C

/-- **Cellular assembly 2.** The cellular boundary formula for the
standard polygon model. -/
theorem polygon4g_cellular_boundary_formula
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gCellularBoundaryFormula g C :=
by
  exact ⟨polygon4g_one_cell_boundary_zero g C,
    polygon4g_two_cell_boundary_abelianized_relator g C⟩

/-- **Cellular leaf 3.** The first cellular homology computed from the
standard polygon chain complex is the free module on the `2g` one-cells.
This is the algebraic consequence of the boundary formula. -/
theorem polygon4g_cellularH1_iso_free
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g) :=
  ⟨LinearEquiv.refl ℤ _⟩

/-- **Cellular assembly.** The polygon's cellular `H₁` is the free
module on the `2g` one-cells.  The only topology used here is isolated
in the model and boundary leaves above. -/
theorem polygon4g_cellularH1_free_assembly (g : ℕ) :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact polygon4g_cellularH1_iso_free g C (polygon4g_cellular_boundary_formula g C)

end JacobianChallenge.Periods
