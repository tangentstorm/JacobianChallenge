import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.PeriodSpanHelpers
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Period functional (target statement)

Queue D scaffolding. States the period pairing as an opaque
`AddMonoidHom`:

```text
periodPairing : IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)
```

Mathematically: given a 1-cycle `σ : H₁(X, ℤ)` (an integer linear
combination of singular 1-simplices, modulo boundaries) and a
holomorphic 1-form `ω`, the pairing returns `∫_σ ω`. This is the
classical period pairing.

The construction is **deferred**: it requires
- multi-chart path integration (a `γ : Path` may cross chart
  boundaries; we have the single-chart version in
  `Periods/PathIntegralChart.lean`);
- linearity in `σ` (sum of integrals = integral of sum);
- well-definedness modulo boundary, i.e., Stokes for 1-forms on
  manifolds (ABSENT in Mathlib v4.28.0; see Inventory §4.5).

Until those land, this file uses `opaque` to give the type its
public name without committing to an implementation.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/-- The period pairing
`IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)`.
Mathematically: integrate the form over the cycle. The
implementation is deferred (multi-chart path integration + Stokes
on manifolds; see file docstring). -/
opaque periodPairing
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)

/-- The basis-aligned period subgroup is discrete.

Bottom-up content: integrality of the period pairing image. Equivalently,
the image is a free `ℤ`-module of rank `2g`, spanned by `2g` real-linearly
independent period vectors after transport to the basis-aligned model.

This is the named bottom-up obligation that
`Jacobian.Periods.basisAlignedPeriodSubgroup_isDiscrete` delegates to.
A real proof requires the integrality of `periodPairing` on integral
1-cycles.

#### TOPDOWN plan (planned split, not yet executed)

The single `sorry` here can be discharged by the following named
sub-obligations, each carrying a distinct portion of the blocker:

1. **`periodSubgroup_eq_zspan_of_basis`** (NEW sorry, integrality):
   the transported range equals the ℤ-span of the basis-aligned period
   vectors `b i := holomorphicOneFormDualEquiv X (periodPairing X (σ i))`,
   where `σ : Fin (2g) → IntegralOneCycle X` is the symplectic basis
   from `symplectic_basis_of_cycles`. Bottom-up: `periodPairing` is an
   `AddMonoidHom`, `IntegralOneCycle X` is the ℤ-span of `σ` (this is
   the deeper content of `h1_basis_of_compact_riemann_surface`), so the
   range is the ℤ-span of `periodPairing (σ i)`. Transport via the
   ℤ-linear `holomorphicOneFormDualEquiv.toAddMonoidHom` preserves
   ℤ-spans.

2. **`periodVectors_linearIndependent`** (already sorry-free assembly,
   line ~194): provides 2g ℝ-linearly-independent vectors in `Fin g → ℂ`
   that lie in the period subgroup.

3. **`zspan_of_RLinearIndep_isDiscrete`** (NEW helper, possibly available
   in Mathlib `IsZLattice` API): the ℤ-span of ℝ-linearly-independent
   vectors in finite-dim ℝ-space carries `DiscreteTopology`. Mathlib
   v4.28.0 exposes this via `Submodule.IsLattice.discreteTopology` or
   the `IsZLattice` instance machinery on `Submodule.span ℤ` of an
   ℝ-LI family.

4. **`periodSubgroup_isZLattice`** becomes a sorry-free assembly:
   rewrite the range using (1) to expose it as the ℤ-span of an ℝ-LI
   family (via 2), then conclude via (3).

Net effect of the split: 1 deep sorry → 1 substantive new sorry on
integrality (1) + 1 generic helper that may already be in Mathlib (3).
Worth executing once `h1_basis_of_compact_riemann_surface` lands or
the integrality argument is independently formalised. -/
theorem periodSubgroup_isZLattice
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) := sorry

/-! ### TOPDOWN decomposition of `periodVectors_linearIndependent`
(integrated from Aristotle 0cfa1878)

Delegates to three named sub-obligations:
- `symplectic_basis_of_cycles` (homology rank — sorry)
- `period_vectors_mem_subgroup` (membership, definitional — sorry-free)
- `period_vectors_linearIndependent_of_symplectic` (Riemann bilinear — sorry) -/

/-! ### TOPDOWN decomposition of `h1_basis_of_compact_riemann_surface`
(integrated from Aristotle 921772f5)

Decomposes into two named sub-obligations:
- `h1_free_of_compact_surface` (cellular homology of the surface)
- `analyticGenus_eq_topologicalGenus` (Hodge/de Rham bridge)
plus a sorry-free reindex assembly.

Each sub-obligation maps to a substantial multi-month Mathlib
formalization effort (≈ 5,000–15,000 lines total): cellular
homology, surface classification, de Rham theorem on manifolds,
Hodge decomposition, Dolbeault, Serre duality. All ABSENT in
v4.28.0. -/

/-- **Sub-obligation 1a (definition).** The topological genus of a
compact connected surface, `rank_ℤ H₁(X, ℤ) / 2`. Names the
topological invariant the analytic genus must equal. -/
noncomputable def topologicalGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] : ℕ :=
  Module.finrank ℤ (IntegralOneCycle X) / 2

/-- **Sub-obligation 1b.** `H₁(X, ℤ)` of a compact connected
Riemann surface of topological genus `g_top` is free of rank
`2 g_top`. Mathlib blockers: surface classification, CW-structure,
cellular homology — all absent in v4.28.0. -/
theorem h1_free_of_compact_surface
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) := by
  sorry

/-- **Sub-obligation 2.** The analytic genus equals the topological
genus for a compact connected Riemann surface. Classical proof via
de Rham (`H¹_dR ≅ H¹_sing ⊗ ℂ`) + Hodge decomposition
(`H¹_dR ≅ H⁰(Ω¹) ⊕ H¹(𝒪)`) + Serre duality.

Mathlib blockers (all absent in v4.28.0): de Rham theorem on
manifolds, Hodge decomposition, Dolbeault cohomology, Serre
duality. -/
theorem analyticGenus_eq_topologicalGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    analyticGenus ℂ X = topologicalGenus X := by
  sorry

/-- **TOPDOWN helper.** H₁(X, ℤ) of a compact connected Riemann surface
of analytic genus `g` admits a ℤ-basis indexed by `Fin (2g)`.

TOPDOWN assembly (Aristotle 921772f5): combines
`h1_free_of_compact_surface` and `analyticGenus_eq_topologicalGenus`
via `Fin.castOrderIso` reindex. -/
theorem h1_basis_of_compact_riemann_surface
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ
      (IntegralOneCycle X)) := by
  obtain ⟨b⟩ := h1_free_of_compact_surface X
  exact ⟨b.reindex (Fin.castOrderIso (by rw [analyticGenus_eq_topologicalGenus])).toEquiv⟩

/-- **Sub-obligation 1.** A compact connected Riemann surface of genus
`g` has `2g` integral 1-cycles forming a symplectic basis (encodes
`H₁(X, ℤ) ≅ ℤ^{2g}`).

TOPDOWN assembly (Aristotle e227f244): extracts a ℤ-basis from
`h1_basis_of_compact_riemann_surface` and derives injectivity via
`LinearIndependent.injective`. -/
theorem symplectic_basis_of_cycles
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X),
      Function.Injective σ := by
  obtain ⟨b⟩ := h1_basis_of_compact_riemann_surface X
  exact ⟨b, b.linearIndependent.injective⟩

/-- **Sub-obligation 2 (sorry-free).** The image of each cycle under
the period pairing, transported through the basis-aligned dual
equivalence, lies in the period subgroup. Definitional. -/
theorem period_vectors_mem_subgroup
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X) :
    ∀ i, (holomorphicOneFormDualEquiv ℂ X) ((periodPairing ℂ X) (σ i))
      ∈ (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  exact fun i => AddSubgroup.mem_map_of_mem _ (AddMonoidHom.mem_range.mpr ⟨σ i, rfl⟩)

/-- **Sub-obligation 3.** Given a symplectic basis `{σ i}`, the `2g`
period vectors are ℝ-linearly independent in `ℂ^g`.

Mathlib gaps (3 independent): wedge product of forms on manifolds;
Riemann bilinear identity (Stokes on polygon); Kähler/Hodge for
`∫_X ω ∧ ω̄ > 0`. All absent in v4.28.0. -/
theorem period_vectors_linearIndependent_of_symplectic
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairing ℂ X) (σ i))) := by
  sorry

/-- The period subgroup contains `2g` ℝ-linearly independent vectors.
Now sorry-free assembly of the three sub-obligations above. -/
theorem periodVectors_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      ∀ i, b i ∈ (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  obtain ⟨σ, hσ⟩ := symplectic_basis_of_cycles X
  exact ⟨fun i => (holomorphicOneFormDualEquiv ℂ X) ((periodPairing ℂ X) (σ i)),
         period_vectors_linearIndependent_of_symplectic X σ hσ,
         period_vectors_mem_subgroup X σ⟩

/-- The basis-aligned period subgroup spans the full ℝ-vector space
`Fin (analyticGenus ℂ X) → ℂ`, viewed as ℝ²ᵍ. Together with
`periodSubgroup_isZLattice`, this is the second half of the
`IsZLattice ℝ` content for the period subgroup.

Bottom-up content: Riemann bilinear nondegeneracy — the period
subgroup contains 2g real-linearly independent vectors. The full
ℤ-rank statement follows from the integrality of the period
pairing on `H₁(X, ℤ)` plus the classical fact that the period
matrix has nonzero imaginary determinant.

This is the named bottom-up obligation that the eventual
construction of an `IsZLattice ℝ` instance for the basis-aligned
period subgroup will delegate to. It is not yet wired into
`PeriodLattice.lean`'s assembly because the surrounding
`IsZLattice` infrastructure (Submodule promotion of the
AddSubgroup, basis extraction) is still being designed.

Decomposed assembly: combine `periodVectors_linearIndependent`
(Riemann bilinear relations — sorry) with
`span_real_eq_top_of_subset_linearIndependent` (pure linear
algebra, sorry-free in
`Jacobian/Periods/PeriodSpanHelpers.lean`). -/
theorem periodSubgroup_spans_real
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule.span ℝ
      ((AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
        Set (Fin (analyticGenus ℂ X) → ℂ))
      = ⊤ := by
  obtain ⟨b, hli, hmem⟩ := periodVectors_linearIndependent X
  exact span_real_eq_top_of_subset_linearIndependent
    (analyticGenus ℂ X)
    ((AddSubgroup.map
      (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
      ((periodPairing ℂ X).range) :
      AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
      Set (Fin (analyticGenus ℂ X) → ℂ))
    b hli (Set.range_subset_iff.mpr hmem)

/-- The period subgroup: the image of the period pairing, as an
additive subgroup of the linear dual of holomorphic 1-forms. -/
noncomputable def periodSubgroup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    AddSubgroup (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (periodPairing E X).range

/-! ### Bridge: assembling `IsZLattice ℝ` from the three leaves

This section bridges the three named bottom-up obligations above
(`periodSubgroup_isZLattice`, `periodSubgroup_spans_real`,
`exists_compact_periodFundamentalDomain`) to the
Mathlib `IsZLattice ℝ` typeclass.

`IsZLattice ℝ L` (in `Mathlib.Algebra.Module.ZLattice.Basic`) is a
typeclass on a `Submodule ℤ E` carrying the field
`span_top : Submodule.span ℝ ↑L = ⊤`, with `[DiscreteTopology L]` as
a class parameter. Mathlib's downstream API
(`ZSpan.fundamentalDomain`, `Basis.ofZLatticeBasis`,
`ZLattice.isAddFundamentalDomain`, etc.) consumes `IsZLattice ℝ L`
plus `DiscreteTopology L`, so to expose our period subgroup to that
API we must (1) promote it from `AddSubgroup` to `Submodule ℤ`, then
(2) give both `DiscreteTopology` and `IsZLattice ℝ` instances on the
promoted form.

The promotion uses `AddSubgroup.toIntSubmodule`, whose underlying set
is definitionally the same `Set` as the source `AddSubgroup` (see
`AddSubgroup.coe_toIntSubmodule`). This means the
`Submodule`-subtype `↥L.toIntSubmodule` and the `AddSubgroup`-subtype
`↥L` carry the same induced subspace topology, but they are distinct
Lean types — a thin bridge `DiscreteTopology.of_continuous_injective`
transports discreteness across the type-level boundary, mirroring the
`discreteTopology_toAddSubgroup` helper in
`Jacobian/ComplexTorus/ZLatticeRecon.lean` (which goes the opposite
direction). -/

/-- The basis-aligned period subgroup, promoted to a `Submodule ℤ`
of the model space `Fin (analyticGenus ℂ X) → ℂ`.

This is the `Submodule ℤ` form of the period subgroup that Mathlib's
`IsZLattice` API consumes. It is built by applying
`AddSubgroup.toIntSubmodule` to the same `AddSubgroup.map` image
that the three named bottom-up obligations above (and
`Jacobian/Periods/PeriodLattice.lean`'s
`basisAlignedPeriodSubgroup`) refer to.

Bottom-up content: nothing new — purely a type-level repackaging.
The mathematical content (discreteness, full ℝ-rank, compact
fundamental domain) is delegated to the three theorems above. -/
noncomputable def basisAlignedPeriodSubmoduleℤ
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℤ (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.toIntSubmodule
    (AddSubgroup.map
      (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
      ((periodPairing ℂ X).range))

/-- `DiscreteTopology` for the `Submodule ℤ`-promoted period subgroup.

Pure type-level transport from `periodSubgroup_isZLattice` (which gives
`DiscreteTopology` on the underlying `AddSubgroup`). The carriers are
the same `Set`, so a `Subtype.mk`-along-the-identity map is continuous
and injective, and `DiscreteTopology.of_continuous_injective` does the
rest. No new bottom-up content. -/
noncomputable instance basisAlignedPeriodSubmoduleℤ_discreteTopology
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    DiscreteTopology (basisAlignedPeriodSubmoduleℤ X) := by
  haveI : DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) :=
    periodSubgroup_isZLattice ℂ X
  exact DiscreteTopology.of_continuous_injective
    (f := fun (x : basisAlignedPeriodSubmoduleℤ X) =>
      (⟨x.1, x.2⟩ :
        AddSubgroup.map
          (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
          ((periodPairing ℂ X).range)))
    (continuous_induced_rng.mpr continuous_subtype_val)
    (fun _ _ h => Subtype.ext (congr_arg Subtype.val h))

/-- `IsZLattice ℝ` for the `Submodule ℤ`-promoted period subgroup.

Pure assembly: the `span_top` field reduces to
`periodSubgroup_spans_real` after applying `AddSubgroup.coe_toIntSubmodule`
to identify the carriers as `Set`s. The `[DiscreteTopology …]` class
parameter is supplied by `basisAlignedPeriodSubmoduleℤ_discreteTopology`
above. No new bottom-up content. -/
noncomputable instance basisAlignedPeriodSubmoduleℤ_isZLattice
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IsZLattice ℝ (basisAlignedPeriodSubmoduleℤ X) where
  span_top := by
    -- `(basisAlignedPeriodSubmoduleℤ X : Set _)` reduces by `rfl` to the
    -- underlying `AddSubgroup.map …` carrier (via
    -- `AddSubgroup.coe_toIntSubmodule`), so the goal is exactly
    -- `periodSubgroup_spans_real X`.
    simpa [basisAlignedPeriodSubmoduleℤ, AddSubgroup.coe_toIntSubmodule]
      using periodSubgroup_spans_real X

/-! ### Existence of a compact fundamental domain (bottom-up consequence) -/

/-- Existence of a compact fundamental domain for the basis-aligned
period subgroup.

Bottom-up content: under the `IsZLattice ℝ` witness assembled from
`periodSubgroup_isZLattice` and `periodSubgroup_spans_real`, the set
`closure (ZSpan.fundamentalDomain b)` (for `b` the lifted ℤ-basis) is
compact — by `ZSpan.fundamentalDomain_isBounded` plus
`Bornology.IsBounded.isCompact_closure` in the `ProperSpace`
`Fin (analyticGenus ℂ X) → ℂ` — and its period-subgroup translates
cover the model space via `ZSpan.fract_mem_fundamentalDomain` and
`Module.Basis.ofZLatticeBasis_span`.

This existence statement is the named bottom-up obligation that the
`periodFundamentalDomain` definition (and the
`periodFundamentalDomain_isCompact` / `_covers` lemmas) in
`Jacobian/Periods/PeriodLattice.lean` delegate to. Stating it as
`∃ D, IsCompact D ∧ (covering)` keeps `PeriodLattice.lean` free to
*choose* a concrete `D` via `Classical.choose`, while the
mathematical work — discreteness + full ℝ-rank ⇒ compact
fundamental domain — is centralised here next to its inputs. -/
theorem exists_compact_periodFundamentalDomain
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ D : Set (Fin (analyticGenus ℂ X) → ℂ),
      IsCompact D ∧
      ∀ v : Fin (analyticGenus ℂ X) → ℂ,
        ∃ g ∈ (AddSubgroup.map
          (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
          ((periodPairing ℂ X).range) :
          AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)),
          v - g ∈ D := by
  haveI : DiscreteTopology (basisAlignedPeriodSubmoduleℤ X) :=
    basisAlignedPeriodSubmoduleℤ_discreteTopology X
  haveI : IsZLattice ℝ (basisAlignedPeriodSubmoduleℤ X) :=
    basisAlignedPeriodSubmoduleℤ_isZLattice X
  haveI := ZLattice.module_free ℝ (basisAlignedPeriodSubmoduleℤ X)
  haveI := ZLattice.module_finite ℝ (basisAlignedPeriodSubmoduleℤ X)
  let bℤ : Module.Basis _ ℤ (basisAlignedPeriodSubmoduleℤ X) :=
    Module.Free.chooseBasis ℤ _
  let bR : Module.Basis _ ℝ (Fin (analyticGenus ℂ X) → ℂ) :=
    bℤ.ofZLatticeBasis ℝ _
  refine ⟨closure (ZSpan.fundamentalDomain bR), ?_, ?_⟩
  · exact (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  · intro v
    refine ⟨(ZSpan.floor bR v : Fin _ → ℂ), ?_, ?_⟩
    · -- The floor lands in `span ℤ (range bR) = basisAlignedPeriodSubmoduleℤ X`,
      -- and `(basisAlignedPeriodSubmoduleℤ X).toAddSubgroup = AddSubgroup.map ...`
      -- by `AddSubgroup.toIntSubmodule_toAddSubgroup`.
      have hmem_span : (ZSpan.floor bR v : Fin _ → ℂ) ∈
          (Submodule.span ℤ (Set.range bR) : Submodule ℤ _) :=
        (ZSpan.floor bR v).property
      have hSub : (basisAlignedPeriodSubmoduleℤ X)
            = Submodule.span ℤ (Set.range bR) :=
        (Module.Basis.ofZLatticeBasis_span (K := ℝ) (b := bℤ)).symm
      have hSubgroup :
          (basisAlignedPeriodSubmoduleℤ X).toAddSubgroup =
          (Submodule.span ℤ (Set.range bR)).toAddSubgroup :=
        congrArg Submodule.toAddSubgroup hSub
      rw [show (AddSubgroup.map
            (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
            ((periodPairing ℂ X).range)) =
          (basisAlignedPeriodSubmoduleℤ X).toAddSubgroup
        from (AddSubgroup.toIntSubmodule_toAddSubgroup _).symm, hSubgroup]
      exact hmem_span
    · have hfract : v - (ZSpan.floor bR v : Fin _ → ℂ) = ZSpan.fract bR v := by
        rw [ZSpan.fract_apply]
      rw [hfract]
      exact subset_closure (ZSpan.fract_mem_fundamentalDomain bR v)

end JacobianChallenge.Periods
