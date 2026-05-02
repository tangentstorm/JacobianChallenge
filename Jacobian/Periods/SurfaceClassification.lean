import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.TopologicalGenusInvariance
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

/-- Bundled polygonal-quotient datum: a continuous surjection
`q : DiskC → M` whose fibres coincide with the side-pairing
equivalence `Polygon4g.SideRel genus`. The point of the bundle is
to make Stage A leaves and downstream constructions (universal-property
homeomorphism, period-pairing functoriality, …) parameterisable over
*one* hypothesis instead of `(genus, q, cts, surj, ker)` quintuples. -/
structure PolygonalQuotientPresentation
    (M : Type) [TopologicalSpace M] where
  /-- The genus parameter — the topological genus of the surface
  presented by this datum. -/
  genus : ℕ
  /-- The continuous surjection from the closed disk witnessing the
  presentation. -/
  proj : DiskC → M
  /-- Continuity of `proj`. -/
  cts : Continuous proj
  /-- Surjectivity of `proj` (every point of `M` is presented by some
  disk point). -/
  surj : Function.Surjective proj
  /-- Kernel: `proj z = proj w` exactly when the standard `4*genus`-gon
  side identification relates `z` and `w`. -/
  kernel : ∀ z w : DiskC, proj z = proj w ↔ Polygon4g.SideRel genus z w

/-- **Stage A1+A2 leaf (existence of a polygonal-quotient presentation).**
Every compact connected orientable smooth real 2-manifold admits a
*polygonal-quotient presentation* in standard `4g'`-gon form: there is
some `g' : ℕ` and a continuous surjection from the closed unit disk
onto `M` whose fibres coincide with the side-pairing equivalence
`Polygon4g.SideRel g'`.

This is the heart of the surface classification theorem (Radó's
triangulation + combinatorial reduction to the standard
`a₁b₁a₁⁻¹b₁⁻¹⋯` edge word). Its discharge is itself a multi-thousand-LOC
project; see `ref/plans/polygonal-model.md` Stage A. -/
theorem existsPolygonalQuotientPresentation
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (PolygonalQuotientPresentation M) := by
  sorry

/-- **Stage A3+A4 leaf (universal-property assembly).** A polygonal-quotient
presentation `(g', q)` of a compact T2 space `M` lifts through the
quotient `Polygon4g g' = DiskC / SideRel g'` to a continuous bijection
`Polygon4g g' → M`. By the compact-to-T2 theorem this is a
homeomorphism.

Body: real proof, no own `sorry`. Uses `Quotient.lift`,
`continuous_quotient_lift`, and `Continuous.homeoOfEquivCompactToT2`. -/
theorem polygonalQuotientPresentation_to_homeo
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (P : PolygonalQuotientPresentation M) :
    Nonempty (Polygon4g P.genus ≃ₜ M) := by
  -- Lift `P.proj` through the side-pairing setoid quotient.
  let qLift : Polygon4g P.genus → M :=
    Quotient.lift P.proj (fun z w hzw => (P.kernel z w).mpr hzw)
  have hqLift_cts : Continuous qLift := P.cts.quotient_lift _
  -- Bijection: surjectivity from `P.surj`, injectivity from `P.kernel`.
  have hqLift_bij : Function.Bijective qLift := by
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
  -- Compact source + T2 target + continuous bijection → homeomorphism.
  exact ⟨hqLift_cts.homeoOfEquivCompactToT2 (f := Equiv.ofBijective qLift hqLift_bij)⟩

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
`polygon4g_zero_homeo_diskC`. -/
theorem polygon4g_zero_contractibleSpace : ContractibleSpace (Polygon4g 0) := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  exact h.contractibleSpace

/-- **Frontier leaf (singular `H₁` of a contractible space is subsingleton).**
Homotopy invariance of singular homology in degree `n ≥ 1` for
contractible spaces. Mathlib v4.28.0 gap — the
`AlgebraicTopology.SingularHomology` directory currently contains only
`Basic.lean` with `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
and no homotopy-invariance theorem.

Discharge plan once homotopy invariance lands:
  * Lift `[ContractibleSpace X]` to a homotopy equivalence with `Unit`.
  * Apply functoriality of `singularHomologyFunctor` plus homotopy
    invariance to transport the vanishing of `H₁(Unit)` (an instance
    of `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
    at `n = 1`) to `H₁(X)`.
  * Subsingleton follows because the zero `ModuleCat ℤ` object is
    subsingleton. -/
theorem singularH1_subsingleton_of_contractibleSpace
    {X : Type} [TopologicalSpace X] [ContractibleSpace X] :
    Subsingleton (singularH1 X) := by
  sorry

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

Body: combine `polygon4g_zero_homeo_diskC`,
`singularH1_finrank_homeo_invariant`, and
`singularH1_diskC_finrank_eq_zero`. -/
theorem singularH1_polygon4g_zero_finrank :
    Module.finrank ℤ (singularH1 (Polygon4g 0)) = 0 := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  rw [singularH1_finrank_homeo_invariant h]
  exact singularH1_diskC_finrank_eq_zero

/-- **Frontier leaf (genus ≥ 1 polygon H₁ structure).** The first
singular homology of the standard `4(g+1)`-gon is ℤ-linearly
isomorphic to the free ℤ-module `Fin (2*(g+1)) → ℤ`.

Bottom-up routes:

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
  sorry

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

/-- **Stage A2 sub-leaf (rank of singular `H₁` of the polygon).**
The first singular homology of the standard fundamental polygon has
ℤ-rank `2g`.

Body: case split on `g`; the `g = 0` branch reduces to the disk
contractibility leaf, and the `g = g'+1` branch reduces to the
cellular-homology leaf. -/
theorem singularH1_polygon4g_finrank (g : ℕ) :
    Module.finrank ℤ (singularH1 (Polygon4g g)) = 2 * g := by
  cases g with
  | zero => simpa using singularH1_polygon4g_zero_finrank
  | succ g => exact singularH1_polygon4g_succ_finrank g

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

end JacobianChallenge.Periods
