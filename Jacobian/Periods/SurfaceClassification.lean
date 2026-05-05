import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.TopologicalGenusInvariance
import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.RadoTriangulation
import Jacobian.Periods.DualGraphCut
import Jacobian.Periods.TietzeReduction
import Jacobian.Periods.Polygon4gCellular
import Jacobian.Periods.SingularH1Homotopy
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage A umbrella: surface classification

This file states the **Stage A** obligation of `ref/plans/polygonal-model.md`:
every compact connected orientable smooth real 2-manifold `M` is
homeomorphic to the standard fundamental polygon `Polygon4g`
of its topological genus.

## Top-down role

`compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
is the named obligation that the umbrella `polygonal_model`
delegates to. It is a 3-leaf assembly:

* `existsHomeoToPolygon4g` — *some* `g' : ℕ` admits `M ≃ₜ Polygon4g g'`.
  This is the heart of the surface-classification theorem: Radó +
  combinatorial reduction + identification with `Polygon4g`.
* `topologicalGenus_polygon4g` — for `g : ℕ`, the polygon `Polygon4g g`
  has topological genus `g`. (Computational; reduces to `H₁` of the
  CW-quotient.)
* `topologicalGenus_homeo_invariant` — `topologicalGenus` is a
  homeomorphism invariant. (Pure Mathlib singular-homology functoriality.)

The umbrella body assembles these: `existsHomeoToPolygon4g` produces
some `g'` and a homeomorphism, then invariance + the polygon
computation pin down `g' = topologicalGenus M`, after which the
homeomorphism is rewritten into the canonical form.

## Bottom-up content

A canonical Lean discharge of `existsHomeoToPolygon4g` would proceed via:

* `compact_2manifold_admits_triangulation` (Radó),
* `triangulated_orientable_surface_word` (combinatorial reduction to the
  standard `a₁b₁a₁⁻¹b₁⁻¹⋯` edge word),
* `polygon_word_to_polygon4g` (identification with `Polygon4g g`).

Each leaf is itself a multi-hundred-LOC project; see
`ref/plans/polygonal-model.md` Stage A and the future
`ref/plans/surface-classification.md` for the next-level decomposition.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Stage A1 leaf (Radó).** Every compact 2-manifold admits a finite
triangulation.

**Round 47 refinement.** The body delegates to
`exists_triangulation_of_compact_2manifold_via_pl` in
`Jacobian.Periods.RadoTriangulation`, which itself decomposes into:

* `compact_2manifold_finite_chart_atlas` — finite chart atlas
  extraction.
* `finite_chart_atlas_admits_pl_refinement` — dimension-2 PL
  refinement (the Doyle–Moran/Thomassen step).
* `pl_atlas_to_triangulation` — assemble the simplicial complex from
  a compatible PL atlas.

Bottom-up content: classical Radó theorem on triangulability of
compact surfaces. Mathlib v4.28.0 has neither Radó nor the abstract
simplicial complex theory required to state it directly. -/
theorem exists_triangulation_of_compact_2manifold
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M] :
    Nonempty (Triangulation M) :=
  exists_triangulation_of_compact_2manifold_via_pl M

/-- **Stage A2.a leaf (cut along non-tree edges).** Given a finite
triangulation of a compact connected 2-manifold, the dual graph
contains a maximal spanning tree; cutting `M` along the *non-tree*
edges unfolds the surface into a single 2-cell with side identifications
encoded as an edge-pairing word. The resulting word is *not yet
standardized* — that is the job of A2.b.

Bottom-up content: dual-tree unfolding (Massey, *Algebraic Topology*,
§I.4 / Lee, *Topological Manifolds*, §6.3). -/
noncomputable def Triangulation.toEdgeWordPresentation
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (T : Triangulation M) : EdgeWordPresentation M :=
  Classical.choice (T.toEdgeWordPresentation_via_cut)

/-- **Stage A2.b leaf (Tietze reduction to standard form).** Any
edge-word presentation of an orientable 2-manifold reduces to the
standard `a₁b₁a₁⁻¹b₁⁻¹⋯` form via finitely many Tietze moves. The
resulting standard presentation is exactly a `PolygonalQuotientPresentation`.

Bottom-up content: classical Brahana / Seifert–Threlfall reduction. -/
noncomputable def EdgeWordPresentation.toPolygonalQuotient
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) : PolygonalQuotientPresentation M :=
  E.toPolygonalQuotient_via_tietze

/-- **Stage A2 leaf (combinatorial reduction).** Given a triangulation
of a compact connected orientable smooth real 2-manifold, one obtains a
polygonal-quotient presentation. Body assembles
`Triangulation.toEdgeWordPresentation` (A2.a) followed by
`EdgeWordPresentation.toPolygonalQuotient` (A2.b). -/
noncomputable def Triangulation.toPolygonalQuotient
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (T : Triangulation M) : PolygonalQuotientPresentation M :=
  T.toEdgeWordPresentation.toPolygonalQuotient

/-- **Stage A1+A2 leaf (existence of a polygonal-quotient presentation).**
Every compact connected orientable smooth real 2-manifold admits a
*polygonal-quotient presentation* in standard `4g'`-gon form.

Body: `exists_triangulation_of_compact_2manifold` + `Triangulation.toPolygonalQuotient`. -/
theorem existsPolygonalQuotientPresentation
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (PolygonalQuotientPresentation M) := by
  obtain ⟨T⟩ := exists_triangulation_of_compact_2manifold M
  exact ⟨T.toPolygonalQuotient⟩

namespace PolygonalQuotientPresentation

/-- The lift of `P.proj : DiskC → M` through the side-pairing
quotient, producing a continuous bijection `Polygon4g P.genus → M`. -/
noncomputable def qLift {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Polygon4g P.genus → M :=
  Quotient.lift P.proj (fun z w hzw => (P.kernel z w).mpr hzw)

lemma qLift_continuous {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Continuous P.qLift :=
  P.cts.quotient_lift _

lemma qLift_bijective {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Function.Bijective P.qLift := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ z =>
      induction b using Quotient.inductionOn with
      | _ w =>
        change P.proj z = P.proj w at hab
        exact Quotient.sound ((P.kernel z w).mp hab)
  · intro y
    obtain ⟨z, hz⟩ := P.surj y
    exact ⟨⟦z⟧, hz⟩

/-- The polygon-to-surface homeomorphism produced by a polygonal
quotient presentation. Compact source + T2 target + continuous
bijection → homeomorphism via `Continuous.homeoOfEquivCompactToT2`. -/
noncomputable def toHomeo {M : Type} [TopologicalSpace M]
    [CompactSpace M] [T2Space M]
    (P : PolygonalQuotientPresentation M) : Polygon4g P.genus ≃ₜ M :=
  P.qLift_continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective P.qLift P.qLift_bijective)

end PolygonalQuotientPresentation

/-- **Stage A3+A4 leaf (universal-property assembly).** A polygonal-quotient
presentation `P` of a compact T2 space `M` produces a homeomorphism
`Polygon4g P.genus ≃ₜ M`, packaged as `Nonempty` for backwards
compatibility (the underlying construction is the noncomputable
`P.toHomeo` defined above). -/
theorem polygonalQuotientPresentation_to_homeo
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (P : PolygonalQuotientPresentation M) :
    Nonempty (Polygon4g P.genus ≃ₜ M) :=
  ⟨P.toHomeo⟩

/-- **Stage A1 umbrella (existence form).** Every compact connected
orientable smooth real 2-manifold is homeomorphic to `Polygon4g g'`
for *some* `g' : ℕ`. Identification of that `g'` with the topological
genus is the Stage A umbrella body, *not* this leaf.

Body: assembled from `existsPolygonalQuotientPresentation` and
`polygonalQuotientPresentation_to_homeo`. -/
theorem existsHomeoToPolygon4g
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    ∃ g' : ℕ, Nonempty (M ≃ₜ Polygon4g g') := by
  obtain ⟨P⟩ := existsPolygonalQuotientPresentation M
  obtain ⟨homeo⟩ := polygonalQuotientPresentation_to_homeo P
  exact ⟨P.genus, ⟨homeo.symm⟩⟩

/-- The side relation `Polygon4g.SideRel 0` collapses to equality on
`DiskC`, since the underlying generator `SideGen 0` has no
constructors (the index `i : Fin 0` is uninhabited). -/
lemma polygon4g_sideRel_zero_iff_eq (a b : DiskC) :
    Polygon4g.SideRel 0 a b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ Relation.EqvGen.refl _⟩
  induction h with
  | rel _ _ hr =>
    cases hr with
    | a_pair i _ _ => exact i.elim0
    | b_pair i _ _ => exact i.elim0
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Sub-sub-sub-leaf (Polygon4g 0 ≃ₜ DiskC, real proof).** Since
`SideGen 0` has no constructors, `SideRel 0` is equality on `DiskC`,
so the quotient `Polygon4g 0` is canonically homeomorphic to `DiskC`.

Body: `Quotient.lift id` produces the inverse of `Polygon4g.mk 0` as
a continuous bijection `Polygon4g 0 → DiskC`; compactness of
`Polygon4g 0` (inherited via `Quotient.compactSpace`) and `T2Space`
of `DiskC` upgrade it to a homeomorphism via
`Continuous.homeoOfEquivCompactToT2`. -/
theorem polygon4g_zero_homeo_diskC :
    Nonempty (Polygon4g 0 ≃ₜ DiskC) := by
  let f : Polygon4g 0 → DiskC :=
    Quotient.lift id (fun a b hab => (polygon4g_sideRel_zero_iff_eq a b).mp hab)
  have hf_cts : Continuous f := continuous_id.quotient_lift _
  let e : Polygon4g 0 ≃ DiskC :=
    { toFun := f
      invFun := Polygon4g.mk 0
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ z => rfl
      right_inv := fun _ => rfl }
  exact ⟨hf_cts.homeoOfEquivCompactToT2 (f := e)⟩

/-- **Genus-zero T2 instance.** `Polygon4g 0` inherits T2 separation
from `DiskC` along the homeomorphism `polygon4g_zero_homeo_diskC`.
(For general `g ≥ 1`, T2 separation of `Polygon4g g` is folded into
the surface-classification leaf `existsPolygonalQuotientPresentation`.) -/
instance polygon4g_zero_t2Space : T2Space (Polygon4g 0) := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  exact h.symm.t2Space

/-- **Real proof.** `DiskC` is a closed ball in `ℂ` (a real
topological vector space), hence convex and nonempty, hence
contractible. -/
instance diskC_contractibleSpace : ContractibleSpace DiskC :=
  Metric.contractibleSpace_closedBall (zero_le_one)

/-- **Genus-zero contractibility instance.** `Polygon4g 0` inherits
contractibility from `DiskC` along the homeomorphism
`polygon4g_zero_homeo_diskC`. Promoted to a top-level instance so
downstream code can `[ContractibleSpace (Polygon4g 0)]` -infer
without explicit setup. -/
instance polygon4g_zero_contractibleSpace : ContractibleSpace (Polygon4g 0) := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  exact h.contractibleSpace

-- The natural follow-up corollary `Subsingleton (singularH1 (Polygon4g 0))`
-- can't be stated here (forward reference to
-- `singularH1_subsingleton_of_contractibleSpace`). It is exposed below
-- via `polygon4g_zero_singularH1_subsingleton` once the contractibility
-- chain is in scope.

/-- `Unit` is totally disconnected (it is subsingleton, so its
connected components are singletons). Local instance — not declared
globally because the project doesn't otherwise need it. -/
private instance unit_totallyDisconnected :
    TotallyDisconnectedSpace Unit :=
  ⟨fun _ _ _ => Set.subsingleton_of_subsingleton⟩

/-- **Sub-sub-leaf (singular `H₁` of `Unit` is subsingleton, real proof).**
`Unit` is totally disconnected, so by Mathlib's
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` at
`n = 1` the singular `H₁` is the zero `ModuleCat ℤ` object, hence
subsingleton via `ModuleCat.subsingleton_of_isZero`. -/
theorem singularH1_unit_subsingleton :
    Subsingleton (singularH1 Unit) :=
  ModuleCat.subsingleton_of_isZero <|
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ) (TopCat.of Unit) one_ne_zero

/-- **Frontier leaf (homotopy invariance of singular `H₁`).** A
homotopy equivalence `X ≃ₕ Y` induces a ℤ-linear isomorphism on
`singularH1`. Mathlib v4.28.0 gap — the
`AlgebraicTopology.SingularHomology` directory has no homotopy-invariance
theorem for `singularHomologyFunctor`. Once it lands (the natural
discharge is the chain-level prism construction giving a chain
homotopy between `singularChainComplexFunctor` evaluated at homotopic
maps, then descending to `homologyFunctor`), this leaf becomes a thin
wrapper around `Functor.mapIso` on a `homotopyEquiv`-derived
`TopCat`-isomorphism. -/
theorem singularH1_iso_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (singularH1 X ≃ₗ[ℤ] singularH1 Y) :=
  singularH1_iso_of_homotopyEquiv_via_prism h

/-- **Sub-leaf (singular `H₁` is invariant under homotopy
equivalence to `Unit`).** Body: lift through `singularH1_iso_of_homotopyEquiv`
to get a ℤ-linear iso with `singularH1 Unit`, then transport the
subsingleton from `singularH1_unit_subsingleton` along the iso. -/
theorem singularH1_subsingleton_of_homotopyEquivUnit
    {X : Type} [TopologicalSpace X] (h : ContinuousMap.HomotopyEquiv X Unit) :
    Subsingleton (singularH1 X) := by
  obtain ⟨e⟩ := singularH1_iso_of_homotopyEquiv h
  haveI := singularH1_unit_subsingleton
  exact e.toEquiv.subsingleton

/-- **Sub-sub-leaf (singular H₁ of a contractible space is subsingleton).**
Body: extract the homotopy equivalence with `Unit` from
`ContractibleSpace.hequiv_unit`, then apply
`singularH1_subsingleton_of_homotopyEquivUnit`. -/
theorem singularH1_subsingleton_of_contractibleSpace
    {X : Type} [TopologicalSpace X] [ContractibleSpace X] :
    Subsingleton (singularH1 X) := by
  obtain ⟨h⟩ := ContractibleSpace.hequiv_unit X
  exact singularH1_subsingleton_of_homotopyEquivUnit h

/-- **Genus-zero singular `H₁` is subsingleton (instance).** Direct
corollary of `polygon4g_zero_contractibleSpace` (Round 20) and
`singularH1_subsingleton_of_contractibleSpace` (Round 19), now wired
as a top-level instance for downstream typeclass inference. -/
instance polygon4g_zero_singularH1_subsingleton :
    Subsingleton (singularH1 (Polygon4g 0)) :=
  singularH1_subsingleton_of_contractibleSpace

/-- **Sub-sub-sub-leaf (singular H₁ of the disk is subsingleton).**
Body: `DiskC` is `ContractibleSpace` (real proof, instance above) and
the contractibility-implies-subsingleton-`H₁` leaf does the rest. -/
theorem singularH1_diskC_subsingleton :
    Subsingleton (singularH1 DiskC) :=
  singularH1_subsingleton_of_contractibleSpace

/-- **Sub-sub-sub-leaf (singular H₁ of the disk vanishes, finrank).**
Body: subsingleton singular `H₁` ⟹ rank zero by
`Module.finrank_zero_of_subsingleton`. -/
theorem singularH1_diskC_finrank_eq_zero :
    Module.finrank ℤ (singularH1 DiskC) = 0 := by
  haveI := singularH1_diskC_subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- **Sub-sub-leaf (genus-zero polygon H₁).** `Polygon4g 0` is the
closed disk (since `SideRel 0` reduces to equality — `SideGen 0` has
no constructors), hence contractible, hence its singular `H₁`
vanishes.

Body: direct corollary of the
`polygon4g_zero_singularH1_subsingleton` instance via
`Module.finrank_zero_of_subsingleton`. The earlier route through
`polygon4g_zero_homeo_diskC` + `singularH1_finrank_homeo_invariant`
+ `singularH1_diskC_finrank_eq_zero` still composes to the same thing. -/
theorem singularH1_polygon4g_zero_finrank :
    Module.finrank ℤ (singularH1 (Polygon4g 0)) = 0 :=
  Module.finrank_zero_of_subsingleton

/-- **Stage A leaf (genus ≥ 1 polygon H₁ as basis).** The first
singular homology of the standard `4(g+1)`-gon admits a ℤ-basis
indexed by `Fin (2*(g+1))`. This is the *combinatorial* heart of the
polygon-rank computation: a basis on `H₁` is the data carrying the
2(g+1) cycles `[a₀], [b₀], …, [a_g], [b_g]`.

**Round 45 refinement.** Body delegates to
`polygon4g_succ_singularH1_basis_via_hurewicz` (Hurewicz +
abelianised-surface-group route) in `Jacobian.Periods.Polygon4gCellular`.
That helper itself bottoms out in `polygon4g_fundamentalGroup_abelianized_basis`
which packages the surface-group abelianisation computation. -/
theorem polygon4g_succ_singularH1_basis (g : ℕ) :
    Nonempty (Module.Basis (Fin (2 * (g + 1))) ℤ
      (singularH1 (Polygon4g (g + 1)))) :=
  polygon4g_succ_singularH1_basis_via_hurewicz g

/-- **Sub-sub-leaf (genus ≥ 1 polygon H₁ structure).** The first
singular homology of the standard `4(g+1)`-gon is ℤ-linearly
isomorphic to the free ℤ-module `Fin (2*(g+1)) → ℤ`.

Body: extract the basis from `polygon4g_succ_singularH1_basis` and
turn it into a linear equivalence via `Basis.equivFun`. (Same
meet-in-the-middle pattern as the Stage B leaf
`singularH1_compactRiemannSurface_iso_freeZ`.)

Bottom-up routes for the underlying basis:

* **Cellular route.** CW structure on `Polygon4g (g+1)` with one vertex,
  `2(g+1)` edges (`a₀,b₀,…,a_g,b_g`), and one 2-cell whose attaching
  word is `∏ᵢ[aᵢ,bᵢ]`. The cellular boundary `∂₂` sends the 2-cell to
  the abelianized commutator product, which is zero, so
  `H₁ = ker ∂₁ / im ∂₂ = ℤ^{2(g+1)} / 0`. Mathlib v4.28.0 lacks
  cellular homology of CW complexes packaged as a `singularHomology`-
  comparable module.
* **Hurewicz route.** `H₁(X, ℤ) ≃ π₁(X)^{ab}` for path-connected `X`,
  combined with the surface-group abelianization computation. Mathlib
  v4.28.0 has `FundamentalGroup` but no Hurewicz isomorphism with
  singular homology. -/
theorem singularH1_polygon4g_succ_iso_freeZ (g : ℕ) :
    Nonempty (singularH1 (Polygon4g (g + 1)) ≃ₗ[ℤ] (Fin (2 * (g + 1)) → ℤ)) := by
  obtain ⟨b⟩ := polygon4g_succ_singularH1_basis g
  exact ⟨b.equivFun⟩

/-- **Sub-sub-leaf (genus ≥ 1 polygon H₁ rank).** Rank `2(g+1)` for
the polygon's singular `H₁`.

Body: lift through `singularH1_polygon4g_succ_iso_freeZ` to the free
ℤ-module `Fin (2*(g+1)) → ℤ`, then compute `Module.finrank` via
`LinearEquiv.finrank_eq` and `Module.finrank_pi` /
`Module.finrank_self`. -/
theorem singularH1_polygon4g_succ_finrank (g : ℕ) :
    Module.finrank ℤ (singularH1 (Polygon4g (g + 1))) = 2 * (g + 1) := by
  obtain ⟨e⟩ := singularH1_polygon4g_succ_iso_freeZ g
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- **Stage A2 unified basis (any genus).** The first singular homology
of the standard fundamental polygon admits a ℤ-basis indexed by
`Fin (2g)`, for *any* `g : ℕ`. The `g = 0` branch uses
`Module.Basis.empty` over the (proved-subsingleton) singular `H₁` of the
disk-quotient `Polygon4g 0`; the `g = g'+1` branch uses
`polygon4g_succ_singularH1_basis`. -/
theorem polygon4g_singularH1_basis (g : ℕ) :
    Nonempty (Module.Basis (Fin (2 * g)) ℤ
      (singularH1 (Polygon4g g))) := by
  cases g with
  | zero =>
    haveI : IsEmpty (Fin (2 * 0)) := by simpa using Fin.isEmpty
    exact ⟨Module.Basis.empty _⟩
  | succ g => exact polygon4g_succ_singularH1_basis g

/-- **Unified Stage A2 structural iso (any genus).** The first singular
homology of the standard fundamental polygon is ℤ-linearly isomorphic
to the free ℤ-module `Fin (2g) → ℤ` for any `g : ℕ`.

Body: extract the unified basis from `polygon4g_singularH1_basis` and
turn it into a linear equivalence via `Basis.equivFun`. (Same
meet-in-the-middle pattern as the Stage B leaf; covers both `g = 0`
and `g ≥ 1` cases via the unified basis.) -/
theorem polygon4g_singularH1_iso_freeZ (g : ℕ) :
    Nonempty (singularH1 (Polygon4g g) ≃ₗ[ℤ] (Fin (2 * g) → ℤ)) := by
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  exact ⟨b.equivFun⟩

/-- **Stage A2 sub-leaf (rank of singular `H₁` of the polygon).**
The first singular homology of the standard fundamental polygon has
ℤ-rank `2g`.

Body: extract the unified basis from `polygon4g_singularH1_basis`,
then `Module.finrank_eq_card_basis` + `Fintype.card_fin`. The case
split on `g` is folded into the basis construction, not exposed here. -/
theorem singularH1_polygon4g_finrank (g : ℕ) :
    Module.finrank ℤ (singularH1 (Polygon4g g)) = 2 * g := by
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- **Stage A2 leaf (polygon genus).** The topological genus of the
standard fundamental polygon `Polygon4g g` equals `g`.

Body: unfold `topologicalGenus`, rewrite through
`singularH1_polygon4g_finrank`, divide by 2. -/
theorem topologicalGenus_polygon4g (g : ℕ) :
    topologicalGenus (Polygon4g g) = g := by
  unfold topologicalGenus
  rw [singularH1_polygon4g_finrank g,
      Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]

/-- **Stage A3 leaf (homeomorphism invariance of `topologicalGenus`).**
A topological homeomorphism between compact connected spaces preserves
the topological genus.

Body: by `singularH1_finrank_homeo_invariant`, both sides reduce to the
same `Module.finrank ℤ (singularH1 _)`, then divide by 2. -/
theorem topologicalGenus_homeo_invariant
    {M N : Type} [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [TopologicalSpace N] [CompactSpace N] [ConnectedSpace N]
    (h : M ≃ₜ N) : topologicalGenus M = topologicalGenus N := by
  unfold topologicalGenus
  rw [singularH1_finrank_homeo_invariant h]

/-- **Stage A umbrella (surface classification).** A compact connected
orientable smooth real 2-manifold `M` is homeomorphic to the standard
fundamental polygon `Polygon4g (topologicalGenus M)`.

Body: assembled from `existsHomeoToPolygon4g`,
`topologicalGenus_polygon4g`, and `topologicalGenus_homeo_invariant`.
The proof has no own `sorry`; all three obligations are named leaves
above. -/
theorem compactOrientableSurface_homeomorph_polygon4g_topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (M ≃ₜ Polygon4g (topologicalGenus M)) := by
  obtain ⟨g', ⟨homeo⟩⟩ := existsHomeoToPolygon4g M
  have hgM : topologicalGenus M = g' := by
    have hinv : topologicalGenus M = topologicalGenus (Polygon4g g') :=
      topologicalGenus_homeo_invariant homeo
    rw [hinv, topologicalGenus_polygon4g]
  exact ⟨hgM ▸ homeo⟩

/-- **Direct corollary (M's singular H₁ is free of rank `2 * topGenus M`).**
For a compact connected orientable smooth real 2-manifold `M` whose
polygonal model is `Polygon4g (topologicalGenus M)`, singular `H₁(M, ℤ)`
is ℤ-linearly isomorphic to the free module `Fin (2 * topologicalGenus M) → ℤ`.

Body: chain `compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
through `singularH1LinearEquivOfHomeo` (Round 4 — *real proof*) and
`polygon4g_singularH1_iso_freeZ` (Round 37 — discharged via the
unified basis). -/
theorem singularH1_iso_freeZ_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (singularH1 M ≃ₗ[ℤ] (Fin (2 * topologicalGenus M) → ℤ)) := by
  obtain ⟨homeo⟩ :=
    compactOrientableSurface_homeomorph_polygon4g_topologicalGenus M
  obtain ⟨polyIso⟩ := polygon4g_singularH1_iso_freeZ (topologicalGenus M)
  exact ⟨(singularH1LinearEquivOfHomeo homeo).trans polyIso⟩

/-- **Finrank corollary.** For a compact connected orientable smooth
real 2-manifold `M`, the ℤ-rank of singular `H₁(M, ℤ)` equals
`2 * topologicalGenus M`.

Body: extract the iso from `singularH1_iso_freeZ_of_compactOrientableSurface`
and finish via `LinearEquiv.finrank_eq` + `Module.finrank_pi` +
`Fintype.card_fin`. -/
theorem singularH1_finrank_eq_two_mul_topologicalGenus_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Module.finrank ℤ (singularH1 M) = 2 * topologicalGenus M := by
  obtain ⟨e⟩ := singularH1_iso_freeZ_of_compactOrientableSurface M
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- **Singular `H₁` of a compact orientable smooth real 2-manifold
admits a ℤ-basis indexed by `Fin (2 * topologicalGenus M)`.** Public
companion to `singularH1_iso_freeZ_of_compactOrientableSurface`,
matching the basis-shaped form used by `h1_basis_of_compact_riemann_surface`
on the Riemann-surface side. -/
theorem singularH1_basis_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus M)) ℤ (singularH1 M)) := by
  obtain ⟨e⟩ := singularH1_iso_freeZ_of_compactOrientableSurface M
  exact ⟨Module.Basis.ofEquivFun e⟩

end JacobianChallenge.Periods
