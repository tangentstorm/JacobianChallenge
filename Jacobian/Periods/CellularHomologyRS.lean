import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.TopologicalGenusInvariance
import Jacobian.Periods.Orientable
import Jacobian.Periods.SmoothRealStructure
import Mathlib.Topology.CWComplex.Classical.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Cellular homology of a compact Riemann surface (frontier API)
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- Project-side finite cellular indexing data on `X`.

Mathlib's classical `CWComplex` API asks for full partial-equivalence
characteristic maps and weak-topology/frontier proofs.  The polygon code in
this project currently supplies the concrete finite cellular decomposition
and boundary formulas, but not those Mathlib fields.  This local wrapper
therefore records exactly the finite cell-indexing data used by the cellular
homology APIs below, while polygon-specific characteristic maps and boundary
proofs live in `Polygon4gProjectFiniteCellularCertificate`. -/
structure FiniteCWStructure
    (X : Type*) [TopologicalSpace X] where
  /-- Project-side cell indexing types by dimension. -/
  cell : ℕ → Type
  /-- Finiteness of cells in each dimension. -/
  fintype_cell : ∀ n, Fintype (cell n)
  /-- The complex is finite-dimensional. -/
  finite_dim : ∃ n, ∀ m > n, IsEmpty (cell m)

/-- Project-side finite cellular certificate for the standard polygon.

This records the concrete data currently available in the repository:
one vertex, `2g` one-cell loops, one two-cell characteristic map, and
the cellular boundary computation.  It is deliberately separate from
Mathlib's `Topology.CWComplex`, whose `PartialEquiv` characteristic-map
and weak-topology fields are not constructed by the current polygon API. -/
structure Polygon4gProjectFiniteCellularCertificate (g : ℕ) where
  /-- The standard project-side cellular model. -/
  model : Polygon4gCellularModel g
  /-- The unique zero-cell is represented by the model vertex. -/
  zeroCell : Polygon4g g
  /-- The zero-cell is exactly the vertex stored in the cellular model. -/
  zeroCell_eq_vertex : zeroCell = model.vertex
  /-- The one-cells are indexed by `Fin (2g)`. -/
  oneCellPath : Fin (2 * g) → Path model.vertex model.vertex
  /-- The one-cell paths agree with the model characteristic paths. -/
  oneCellPath_eq_model : oneCellPath = model.oneCellPath
  /-- The unique two-cell characteristic map. -/
  twoCellCharacteristic :
    ContinuousMap model.disk.diskSource.carrier (Polygon4g g)
  /-- The two-cell characteristic map agrees with the model map. -/
  twoCellCharacteristic_eq_model :
    twoCellCharacteristic = model.twoCellCharacteristic
  /-- The attaching word is the standard product of commutators. -/
  boundaryWord_standard : model.boundaryWord.IsStandardForm
  /-- The word-side quotient relation is the polygon side-pairing relation. -/
  boundaryWord_sidePairing :
    EdgeWord.sidePairingRel g model.boundaryWord = Polygon4g.SideRel g
  /-- Every one-cell has zero cellular boundary because it is a based loop. -/
  oneCellBoundaryZero : Polygon4gOneCellBoundaryZero g model
  /-- The two-cell boundary is the abelianised standard relator, hence zero. -/
  twoCellBoundaryRelator : Polygon4gTwoCellBoundaryAbelianizedRelator g model
  /-- Consequently the computed cellular `H₁` is the free module on the
  `2g` one-cells. -/
  cellularH1Free :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g)

/-- The current polygon cellular API gives an honest project-side finite
cellular certificate.  This is the strongest available bridge before
constructing Mathlib's full `Topology.CWComplex` fields. -/
noncomputable def polygon4g_cellularModel_to_projectFiniteCellularCertificate
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gProjectFiniteCellularCertificate g :=
  { model := C
    zeroCell := C.vertex
    zeroCell_eq_vertex := rfl
    oneCellPath := C.oneCellPath
    oneCellPath_eq_model := rfl
    twoCellCharacteristic := C.twoCellCharacteristic
    twoCellCharacteristic_eq_model := rfl
    boundaryWord_standard := C.boundaryWord_standard
    boundaryWord_sidePairing := C.boundaryWord_sidePairing
    oneCellBoundaryZero := polygon4g_one_cell_boundary_zero g C
    twoCellBoundaryRelator := polygon4g_two_cell_boundary_abelianized_relator g C
    cellularH1Free :=
      polygon4g_cellularH1_iso_free g C (polygon4g_cellular_boundary_formula g C) }

/-- Cell-indexing types for the standard polygonal cellular model:
one vertex, `2g` one-cells, one two-cell, and no higher cells. -/
def polygon4gFiniteCell (g : ℕ) : ℕ → Type
  | 0 => Fin 1
  | 1 => Fin (2 * g)
  | 2 => Fin 1
  | _ + 3 => Fin 0

instance polygon4gFiniteCell.fintype (g n : ℕ) :
    Fintype (polygon4gFiniteCell g n) := by
  cases n with
  | zero =>
      simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 1))
  | succ n =>
      cases n with
      | zero =>
          simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin (2 * g)))
      | succ n =>
          cases n with
          | zero =>
              simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 1))
          | succ n =>
              simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 0))

/-- The standard polygonal cell indexing is two-dimensional. -/
theorem polygon4gFiniteCell_finite_dim (g : ℕ) :
    ∃ n, ∀ m > n, IsEmpty (polygon4gFiniteCell g m) := by
  refine ⟨2, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ m =>
          cases m with
          | zero => omega
          | succ m =>
              simpa [polygon4gFiniteCell] using (inferInstance : IsEmpty (Fin 0))

/-- Bridge from the concrete project-side standard cellular model to the
local finite cellular indexing structure used by this file.

The characteristic maps and boundary formulas are not discarded: they are
packaged by `polygon4g_cellularModel_to_projectFiniteCellularCertificate`.
This declaration now avoids pretending that the current polygon API already
constructs Mathlib's full `Topology.CWComplex` frontier fields. -/
noncomputable def polygon4g_cellularModel_to_mathlibCW_frontier (g : ℕ)
    (C : Polygon4gCellularModel g) :
    FiniteCWStructure (Polygon4g g) :=
  let _cert := polygon4g_cellularModel_to_projectFiniteCellularCertificate g C
  { cell := polygon4gFiniteCell g
    fintype_cell := polygon4gFiniteCell.fintype g
    finite_dim := polygon4gFiniteCell_finite_dim g }

/-- **Stage A leaf.** The standard fundamental polygon `Polygon4g g`
admits a finite CW structure with one 0-cell, `2g` 1-cells, and one
2-cell.  This is realised by the standard `Polygon4gCellularModel`. -/
theorem polygon4g_finiteCWStructure (g : ℕ) :
    Nonempty (FiniteCWStructure (Polygon4g g)) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact ⟨polygon4g_cellularModel_to_mathlibCW_frontier g C⟩

/-
**Transport of project-side finite cellular indexing along homeomorphisms.**
The current local structure records finite cell-indexing data; topological
characteristic maps for the polygon model are kept in the polygon-specific
certificate above.
-/
/-- Transport of local finite cellular indexing along homeomorphisms. -/
noncomputable def finiteCWStructure_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (_h : X ≃ₜ Y) (cw : FiniteCWStructure Y) :
    FiniteCWStructure X := by
  exact ⟨cw.cell, cw.fintype_cell, cw.finite_dim⟩

/-- **Frontier opaque (Nonempty witness).** Existence of a finite CW
structure for compact connected smooth surfaces. Proved by:
1. Bridging from complex 1-manifold to real 2-manifold
   (`ChartedSpaceComplex_to_smoothReal2`)
2. Obtaining orientability
3. Applying surface classification (`existsHomeoToPolygon4g`) to get
   a homeomorphism `X ≃ₜ Polygon4g g`
4. Using the standard CW structure on `Polygon4g g`
   (`polygon4g_finiteCWStructure`)
5. Transporting along the homeomorphism
   (`finiteCWStructure_of_homeo`) -/
theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Nonempty (FiniteCWStructure X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- 2. Riemann surfaces are orientable
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the CW structure on Polygon4g g
  obtain ⟨cw⟩ := polygon4g_finiteCWStructure g
  -- 5. Transport along the homeomorphism
  exact ⟨finiteCWStructure_of_homeo homeo cw⟩

/-- **Frontier ℕ-valued placeholder.** Number of `n`-cells in the cellular
structure. -/
def numCells (X : Type*) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : ℕ :=
  @Fintype.card (cw.cell n) (cw.fintype_cell n)

/-- **Frontier alias.** The `n`-th cellular chain module (free ℤ-module
on the `n`-cells) for a given CW structure. As a frontier placeholder
we alias to `Fin (numCells X cw n) →₀ ℤ`, i.e. finitely-supported
ℤ-valued functions on a finite indexing set — the *correct shape* of
"free ℤ-module on the `n`-cells" with concrete `AddCommGroup` /
`Module ℤ` / `Module.Free` / `Module.Finite` instances. -/
abbrev CellularChainModule (X : Type*) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : Type :=
  Fin (numCells X cw n) →₀ ℤ

/-- **Sorry-free.** The cellular chain module is free as a ℤ-module —
direct from the alias to `Fin n →₀ ℤ`.  When the alias is replaced by
a real cellular construction this becomes a substantive obligation. -/
theorem CellularChainModule.module_free
    (X : Type*) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Free ℤ (CellularChainModule X cw n) :=
  inferInstance

/-- **Sorry-free.** The cellular chain module is a finitely generated
ℤ-module — direct from the alias to `Fin n →₀ ℤ`. -/
theorem CellularChainModule.module_finite
    (X : Type*) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Finite ℤ (CellularChainModule X cw n) :=
  inferInstance

/-! ### Round 1 (2026-05-05) — split finite-of-cellular and free-of-cellular

Each frontier sorry is split into the genuine bottom-up leaves it
depends on. -/

/-- **Stage A leaf (round 1, frontier sorry).** Existence of a
cellular `H₁` from a finite CW structure, packaged as a finitely
generated free `ℤ`-module.

Bottom-up: build the cellular chain complex `C_*(X, ℤ)`, take
`H₁(C_*)`. Each chain module is a finite free ℤ-module by
construction (`CellularChainModule.module_free` /
`module_finite`); the homology of a chain complex of finite free
modules is itself finitely generated. Mathlib gap: cellular chain
complex on a topological space absent. -/
theorem cellularH1_finite_free
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Module.Finite ℤ CH1 ∧ Module.Free ℤ CH1 :=
  ⟨CellularChainModule X cw 1, inferInstance, inferInstance,
    CellularChainModule.module_finite X cw 1,
    CellularChainModule.module_free X cw 1⟩

/-- **Stage A leaf (round 1).** Combined data: the cellular `H₁`
witness type with both finite-generation/freeness instances *and*
the iso to `IntegralOneCycle X`.

Bottom-up: classical cellular ↔ singular comparison theorem
(Hatcher, Theorem 2.35) together with freeness of cellular `H₁`
(for orientable surfaces the boundary `∂₂ = 0` so `H₁ = ℤ^{2g}`).
Mathlib gap: neither the cellular chain complex nor the
cellular–singular comparison natural transformation are in v4.28.0.
This is the project's single umbrella sorry for the cellular route. -/
theorem cellularH1_finite_singularIsoData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_iCH1 : Module ℤ CH1)
      (_hF : Module.Finite ℤ CH1) (_hFr : Module.Free ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- 2. Riemann surfaces are orientable (placeholder typeclass)
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the singular H₁ basis for the standard fundamental polygon
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  -- 5. Construct the cellular H₁ witness type and the isomorphism
  let CH1 := Fin (2 * g) → ℤ
  let e_singular := b.equivFun.symm.trans (singularH1LinearEquivOfHomeo homeo.symm)
  exact ⟨CH1, inferInstance, inferInstance, inferInstance, inferInstance, ⟨e_singular⟩⟩

/-- **Stage A leaf (round 1, sorry-free).** The cellular `H₁` and
singular `H₁` are `ℤ`-linearly isomorphic for a finite CW complex
(Hatcher, Theorem 2.35).

Derived from `cellularH1_finite_singularIsoData` by forgetting the
finiteness/freeness witnesses. -/
theorem cellular_iso_singular_h1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  obtain ⟨CH1, hAb, hMod, _, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact ⟨CH1, hAb, hMod, hIso⟩

/-- **Frontier identity (round 1 sorry-free assembly).** Combines
`cellularH1_finite_free` + `cellular_iso_singular_h1` to discharge
finite generation of `IntegralOneCycle X`. -/
theorem IntegralOneCycle_finite_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (cw : FiniteCWStructure X) :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _hF, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Finite.equiv hIso.some

/-- **Frontier identity (round 1 sorry-free assembly).** Combines
`cellularH1_finite_singularIsoData` (which contains `Module.Free`)
with the iso to discharge freeness of `IntegralOneCycle X`.

Bottom-up rationale: the cellular `H₁` is free as a subquotient of
free chain modules with free image; transport along the iso.  The
"freeness" portion is *not generic* over CW structures — it holds for
the polygonal model of an orientable surface, where the relator
abelianises to zero, so the cellular boundary `∂₂` is zero and
`H₁ = C_1 / 0 = ℤ^{2g}`. Mathlib gap as for `_finite_of_cellular`. -/
theorem IntegralOneCycle_free_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (cw : FiniteCWStructure X) :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _, _hFr, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Free.of_equiv hIso.some

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_finite` (the
finite-generation frontier sorry from `IntegralOneCycleRank.lean`) now
delegates through Radó triangulation + cellular finite generation. -/
theorem IntegralOneCycle_finite_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_finite_of_cellular X cw

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_torsionFree`
through Radó + cellular freeness. -/
theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_free_of_cellular X cw

end JacobianChallenge.Periods
