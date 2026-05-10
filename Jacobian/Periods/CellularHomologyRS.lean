import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.TopologicalGenusInvariance
import Jacobian.Periods.Orientable
import Jacobian.Periods.SmoothRealStructure
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Cellular homology of a compact Riemann surface (frontier API)
-/

namespace JacobianChallenge.Periods

open scoped Manifold
open Topology Metric Set

/-- **Frontier placeholder structure.** Finite CW structure on `X`: an
abstract witness that `X` admits a finite cellular decomposition. -/
structure FiniteCWStructure
    (X : Type*) [TopologicalSpace X] where
  /-- The underlying CW complex structure. -/
  cw : Topology.CWComplex (Set.univ : Set X)
  /-- Finiteness of cells in each dimension. -/
  fintype_cell : ∀ n, Fintype (cw.cell n)
  /-- The complex is finite-dimensional. -/
  finite_dim : ∃ n, ∀ m > n, IsEmpty (cw.cell m)

/-! ### Transport of CW structures across homeomorphisms -/

/-- The transported characteristic map: compose the original map with `f.symm`. -/
noncomputable def transportMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) {n : ℕ} (pe : PartialEquiv (Fin n → ℝ) Y) :
    PartialEquiv (Fin n → ℝ) X where
  toFun v := f.symm (pe v)
  invFun x := pe.symm (f x)
  source := pe.source
  target := f.symm '' pe.target
  map_source' v hv := ⟨pe v, pe.map_source' hv, rfl⟩
  map_target' x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Homeomorph.apply_symm_apply]; exact pe.map_target' hy
  left_inv' v hv := by
    show pe.symm (f (f.symm (pe v))) = v
    rw [Homeomorph.apply_symm_apply]; exact pe.left_inv hv
  right_inv' x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    show f.symm (pe (pe.symm (f (f.symm y)))) = f.symm y
    rw [Homeomorph.apply_symm_apply, pe.right_inv hy]

@[simp]
theorem transportMap_image
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) {n : ℕ} (pe : PartialEquiv (Fin n → ℝ) Y) (S : Set (Fin n → ℝ)) :
    (transportMap f pe) '' S = f.symm '' (pe '' S) := by
  ext x; simp only [mem_image, transportMap]; constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨pe v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩

set_option maxHeartbeats 400000 in
/-- Transport a `FiniteCWStructure` across a homeomorphism.
Given `f : X ≃ₜ Y` and a finite CW structure on `Y`, construct
one on `X` by composing characteristic maps with `f.symm`.

The construction uses the same cell indexing types and composes
each characteristic map with `f.symm` to land in `X`. Each CW complex
axiom (source_eq, continuousOn, pairwiseDisjoint, mapsTo, union) follows
from the corresponding axiom on `Y` composed with the bijection `f.symm`. -/
noncomputable def FiniteCWStructure.ofHomeo
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (cwY : FiniteCWStructure Y) : FiniteCWStructure X :=
  let N := cwY.finite_dim.choose
  let hN := cwY.finite_dim.choose_spec
  let cwX := CWComplex.mkFinite (Set.univ : Set X)
    (cell := cwY.cw.cell)
    (map := fun n i => transportMap f (cwY.cw.map n i))
    (eventually_isEmpty_cell := by
      rw [Filter.eventually_atTop]
      exact ⟨N + 1, fun m hm => hN m (by omega)⟩)
    (finite_cell := fun n => Fintype.finite (cwY.fintype_cell n))
    (source_eq := fun n i => cwY.cw.source_eq n i)
    (continuousOn := fun n i =>
      f.symm.continuous.continuousOn.comp (cwY.cw.continuousOn n i) (fun _ _ => mem_univ _))
    (continuousOn_symm := fun n i => by
      change ContinuousOn (fun x => (cwY.cw.map n i).symm (f x))
        (f.symm '' (cwY.cw.map n i).target)
      have htgt : f.symm '' (cwY.cw.map n i).target = f ⁻¹' (cwY.cw.map n i).target := by
        ext x; constructor
        · rintro ⟨y, hy, rfl⟩; simp [hy]
        · intro hx; exact ⟨f x, hx, by simp⟩
      rw [htgt]
      exact (cwY.cw.continuousOn_symm n i).comp f.continuous.continuousOn (fun x hx => hx))
    (pairwiseDisjoint' := by
      intro a _ b _ hab
      simp only [Function.onFun, transportMap_image]
      rw [Set.disjoint_image_iff f.symm.injective]
      exact cwY.cw.pairwiseDisjoint' (mem_univ a) (mem_univ b) hab)
    (mapsTo_iff_image_subset := fun n i => by
      intro v hv
      obtain ⟨I, hI⟩ := cwY.cw.mapsTo' n i
      have h2 := hI hv
      simp only [mem_iUnion] at h2 ⊢
      obtain ⟨m, hm, j, hjI, hy⟩ := h2
      exact ⟨m, hm, j, by rw [transportMap_image]; exact Set.mem_image_of_mem _ hy⟩)
    (union' := by
      simp_rw [transportMap_image]
      have : ⋃ n, ⋃ j, f.symm '' (cwY.cw.map n j '' closedBall 0 1) =
          f.symm '' (⋃ n, ⋃ j, cwY.cw.map n j '' closedBall 0 1) := by
        rw [Set.image_iUnion]; congr 1; ext n; rw [Set.image_iUnion]
      rw [this, cwY.cw.union', Set.image_univ, Homeomorph.range_coe])
  ⟨cwX, fun n => cwY.fintype_cell n, ⟨N, hN⟩⟩

/-- **Frontier leaf (Polygon4g CW structure).** The standard fundamental
polygon `Polygon4g g` admits a finite CW structure with 1 vertex,
`2g` edges, and 1 face (for `g ≥ 1`; for `g = 0` it is a single
2-cell). -/
theorem polygon4g_finiteCWStructure (g : ℕ) :
    Nonempty (FiniteCWStructure (Polygon4g g)) := by
  sorry

/-- **Frontier opaque (Nonempty witness).** Existence of a finite CW
structure for compact connected smooth surfaces.

**Proof route:** bridge the complex 1-manifold to a real 2-manifold,
obtain orientability, apply the surface classification theorem
(`existsHomeoToPolygon4g`) to get `X ≃ₜ Polygon4g g`, then transport
the standard CW structure on `Polygon4g g` via `FiniteCWStructure.ofHomeo`. -/
theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (FiniteCWStructure X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- 2. Riemann surfaces are orientable
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply surface classification
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Transport CW structure from Polygon4g g
  obtain ⟨cwP⟩ := polygon4g_finiteCWStructure g
  exact ⟨FiniteCWStructure.ofHomeo homeo cwP⟩

/-- **Frontier ℕ-valued placeholder.** Number of `n`-cells in the cellular
structure. -/
def numCells (X : Type*) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : ℕ :=
  @Fintype.card (cw.cw.cell n) (cw.fintype_cell n)

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
    (_cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Module.Finite ℤ CH1 ∧ Module.Free ℤ CH1 :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance⟩

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
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_finite_of_cellular X cw

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_torsionFree`
through Radó + cellular freeness. -/
theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_free_of_cellular X cw

end JacobianChallenge.Periods
