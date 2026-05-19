import Jacobian.Periods.PolygonCellularHomology

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

/-- The closed-disk source for the standard polygonal cell datum. -/
opaque Polygon4gClosedDiskCellSource (g : ℕ) : Type

/-- **Cellular leaf 1a(i).** Construct the closed disk source used by
the standard `4g`-gon model. -/
theorem polygon4g_closed_disk_cell_source (g : ℕ) :
    Nonempty (Polygon4gClosedDiskCellSource g) := by
  -- Blocker: `Polygon4gClosedDiskCellSource` is opaque by design.  A real
  -- proof must instantiate it with the closed disk carrying the `4g` boundary
  -- arcs; replacing the source by a placeholder witness would erase the
  -- quotient-disk topology that downstream cellular data is meant to record.
  sorry

/-- The subdivision of the boundary circle into the oriented sides of
the standard `4g`-gon. -/
opaque Polygon4gBoundarySideSubdivision
    (g : ℕ) (_diskSource : Polygon4gClosedDiskCellSource g) : Type

/-- **Cellular leaf 1a(ii).** Construct the boundary side subdivision
of the closed disk source. -/
theorem polygon4g_boundary_side_subdivision
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g) :
    Nonempty (Polygon4gBoundarySideSubdivision g diskSource) := by
  -- Blocker: this needs actual boundary parametrisation data for the chosen
  -- disk source, namely the cyclic subdivision into the `4g` oriented sides.
  -- Since `diskSource` is opaque, there is currently no boundary circle or arc
  -- API from which such a subdivision can be constructed.
  sorry

/-- The quotient relation that identifies the polygon sides according
to the surface word. -/
opaque Polygon4gBoundaryQuotientRelation
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g)
    (_subdivision : Polygon4gBoundarySideSubdivision g diskSource) : Type

/-- **Cellular leaf 1a(iii).** Construct the boundary quotient
relation for the standard side identifications. -/
theorem polygon4g_boundary_quotient_relation
    (g : ℕ) (diskSource : Polygon4gClosedDiskCellSource g)
    (subdivision : Polygon4gBoundarySideSubdivision g diskSource) :
    Nonempty (Polygon4gBoundaryQuotientRelation g diskSource subdivision) := by
  -- Blocker: the quotient relation must identify paired boundary arcs
  -- according to the surface word.  The present opaque `diskSource` and
  -- `subdivision` expose no endpoints, orientations, or side labels from which
  -- the relation can be defined.
  sorry

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
opaque Polygon4gBoundarySidePairingCombinatorics
    (g : ℕ) (_disk : Polygon4gQuotientDiskCellData g) : Type

/-- **Cellular leaf 1b(i).** Construct the side-pairing combinatorics
for the standard polygon. -/
theorem polygon4g_boundary_side_pairing_combinatorics
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g) :
    Nonempty (Polygon4gBoundarySidePairingCombinatorics g disk) := by
  -- Blocker: the pairing combinatorics should be computed from the explicit
  -- `a₁,b₁,a₁⁻¹,b₁⁻¹,...` side order on the quotient disk.  That order is not
  -- present in the opaque quotient-disk data.
  sorry

/-- Compatibility between the side pairing and the standard generator
labels/orientations `aᵢ,bᵢ,aᵢ⁻¹,bᵢ⁻¹`. -/
opaque Polygon4gBoundarySidePairingLabelCompatible
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (_pairing : Polygon4gBoundarySidePairingCombinatorics g disk) : Prop

/-- **Cellular leaf 1b(ii).** The side-pairing combinatorics has the
standard orientation and generator-label compatibility. -/
theorem polygon4g_boundary_side_pairing_label_compatible
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (pairing : Polygon4gBoundarySidePairingCombinatorics g disk) :
    Polygon4gBoundarySidePairingLabelCompatible g disk pairing := by
  -- Blocker: label compatibility is a proposition over opaque pairing data.
  -- A proof needs pairing fields naming each side label and orientation; the
  -- current type gives no eliminator exposing that combinatorics.
  sorry

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
one two-cell of the standard polygonal model. -/
opaque Polygon4gCharacteristicMapData
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (_edgePairing : Polygon4gEdgePairingCellData g disk) : Type

/-- **Cellular leaf 1c.** Construct the characteristic maps for the
standard polygonal cell structure. -/
theorem polygon4g_characteristic_map_data
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (edgePairing : Polygon4gEdgePairingCellData g disk) :
    Nonempty (Polygon4gCharacteristicMapData g disk edgePairing) := by
  -- Blocker: characteristic maps require concrete continuous maps for the
  -- unique zero-cell, the `2g` one-cells, and the two-cell attaching disk.  The
  -- quotient disk and edge-pairing records are still abstract witnesses.
  sorry

/-- A witness that `Polygon4g g` carries the standard cellular model:
one zero-cell, `2g` one-cells, and one two-cell.  The concrete CW data
and characteristic maps are the missing Mathlib-side construction. -/
opaque Polygon4gCellularModel (g : ℕ) : Type

/-- **Cellular leaf 1d.** Realise the quotient-disk, edge-pairing, and
characteristic-map data as a cellular model on `Polygon4g g`. -/
theorem polygon4g_realize_standard_cellular_model
    (g : ℕ) (disk : Polygon4gQuotientDiskCellData g)
    (edgePairing : Polygon4gEdgePairingCellData g disk)
    (_characteristicMaps : Polygon4gCharacteristicMapData g disk edgePairing) :
    Nonempty (Polygon4gCellularModel g) := by
  -- Blocker: realisation is the missing CW-structure theorem for the polygon
  -- quotient.  It must connect the quotient-disk characteristic maps with the
  -- topology of `Polygon4g g`; the current abstract data carries no such
  -- homeomorphism or cell-attachment proof.
  sorry

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
opaque Polygon4gOneCellBoundaryZero
    (g : ℕ) (_C : Polygon4gCellularModel g) : Prop

/-- **Cellular leaf 2a.** The one-cell boundary is zero for the standard
polygon model. -/
theorem polygon4g_one_cell_boundary_zero
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gOneCellBoundaryZero g C := by
  -- Blocker: this boundary calculation depends on an explicit one-vertex
  -- cellular model.  `C` is opaque, so there are no endpoint maps proving that
  -- every one-cell starts and ends at the same zero-cell.
  sorry

/-- The cellular two-cell boundary is the abelianisation of the surface
relator `∏ᵢ [aᵢ,bᵢ]`, hence zero in the free abelian group on one-cells. -/
opaque Polygon4gTwoCellBoundaryAbelianizedRelator
    (g : ℕ) (_C : Polygon4gCellularModel g) : Prop

/-- **Cellular leaf 2b.** The two-cell boundary is the abelianised
commutator product and therefore vanishes. -/
theorem polygon4g_two_cell_boundary_abelianized_relator
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gTwoCellBoundaryAbelianizedRelator g C := by
  -- Blocker: this is the abelianised attaching-word computation for
  -- `∏ᵢ [aᵢ,bᵢ]`.  A proof needs the two-cell attaching map and the labelled
  -- edge basis of `C`; neither is exposed by the opaque cellular model.
  sorry

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
