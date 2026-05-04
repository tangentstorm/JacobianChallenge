import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.HodgeDeRhamRank
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.PeriodSpanHelpers
import Jacobian.Periods.HodgeDeRham
import Jacobian.Periods.H1EvenBasisViaSurfaceClassification
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic.LinearCombination

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

universe u

/-- The period pairing
`IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)`.
Mathematically: integrate the form over the cycle. The
implementation is deferred (multi-chart path integration + Stokes
on manifolds; see file docstring). -/
opaque periodPairing
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type u) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)

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

/-! **Sub-obligation 1a (definition).** The topological genus of a
compact connected surface, `rank_ℤ H₁(X, ℤ) / 2`, is the canonical
`JacobianChallenge.Periods.topologicalGenus` from
`Jacobian.Periods.TopologicalGenus`, re-exported through the import
above. The previously-local duplicate definition was removed in
favour of the canonical one (Round 26 refinement); the canonical
definition is `Module.finrank ℤ (singularH1 X) / 2`, where
`singularH1 X = (IntegralOneCycle X : Type)` definitionally, so the
two formulations are interchangeable in proofs. -/

/-- **Helper for Sub-obligation 1b.** A compact connected Riemann surface
has `H₁(X, ℤ) ≅ ℤ^(2g)` for some `g : ℕ`. This packages the deep
topological fact (surface classification + cellular homology) as a single
sorry-ed witness: the existence of *some* genus `g` and a ℤ-basis of
`H₁` indexed by `Fin (2 * g)`. Absent prerequisites: CW-structure on
compact surfaces, cellular homology, surface classification theorem —
all missing in Mathlib v4.28.0.

(Aristotle 0d7ce5da named-helper extraction; Round 56 refines this
into `h1_has_even_basis_via_surface_classification`, which delegates
to the Stage A surface-classification API + Stage B1/B2 bridges. The
remaining sorries live in the Stage A leaves, not in this Stage B
file.) -/
lemma h1_has_even_basis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ g : ℕ, Nonempty (Module.Basis (Fin (2 * g)) ℤ (IntegralOneCycle X)) := by
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  haveI : FiniteDimensionalHolomorphicOneForms ℂ X :=
    compactRiemannSurface_finiteDimensionalHolomorphicOneForms X
  refine ⟨analyticGenus ℂ X, ?_⟩
  let b : Module.Basis (Fin (Module.finrank ℤ (IntegralOneCycle X))) ℤ
      (IntegralOneCycle X) :=
    Module.finBasis ℤ (IntegralOneCycle X)
  exact ⟨b.reindex
    (finCongr (JacobianChallenge.HolomorphicForms.two_analyticGenus_eq_finrank_intH1 X).symm)⟩

/-- **Sub-obligation 1b.** `H₁(X, ℤ)` of a compact connected
Riemann surface of topological genus `g_top` is free of rank
`2 g_top`. Mathlib blockers: surface classification, CW-structure,
cellular homology — all absent in v4.28.0.

(Aristotle 0d7ce5da, sorry-free assembly via h1_has_even_basis +
topologicalGenus arithmetic.) -/
theorem h1_free_of_compact_surface
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) := by
  obtain ⟨g, ⟨b⟩⟩ := h1_has_even_basis X
  have hfr : Module.finrank ℤ (IntegralOneCycle X) = 2 * g := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htg : topologicalGenus X = g := by
    show Module.finrank ℤ (IntegralOneCycle X) / 2 = g
    omega
  exact ⟨b.reindex (finCongr (by omega))⟩

/-- **Frontier helper (Hodge–de Rham bridge).**
`2 · dim_ℂ H⁰(X, Ω¹) = rank_ℤ H₁(X, ℤ)` for a compact connected
Riemann surface.

#### TOPDOWN refinement (claude/expand-hodge-derham-RbzcT)

The original single `sorry` is now a **sorry-free assembly** delegating
to a multi-file frontier-obligation tree:

```text
hodge_deRham_rank_eq                              -- this theorem
└── two_analyticGenus_eq_finrank_intH1            -- HodgeDeRhamRank.lean (sorry-free)
    ├── realDimDeRhamH1_eq_two_analyticGenus      -- HodgeDecomposition.lean (sorry-free)
    │   ├── realDim_deRhamH1_eq_complexDim_deRhamH1ℂ
    │   │                                          -- RealComplexDeRham.lean (sorry-free
    │   │                                             round-2 assembly through
    │   │                                             complexDeRhamH1_eq_tensorℂ_realDeRhamH1
    │   │                                             + tensorℂ_finrank_eq_real_finrank)
    │   ├── complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus
    │   │                                          -- HodgeDecomposition.lean → HodgeProjection
    │   │                                             (Hodge harmonic projection,
    │   │                                             round-2 split into 5 named leaves)
    │   ├── analyticHarmonicGenus_eq_analyticGenus_add_anti
    │   │                                          -- HodgeStarRS.lean (frontier sorry)
    │   └── analyticAntiGenus_eq_analyticGenus    -- AntiHolomorphicOneForm.lean (rfl-via-alias)
    └── realDim_deRhamH1_eq_finrank_intH1         -- DeRhamSingular.lean (sorry-free)
        ├── realDim_deRhamH1_eq_realDim_singularH1 -- DeRhamSingular.lean → DeRhamComparisonMap
        │                                            (de Rham theorem, round-2 split into
        │                                             Stokes + surjectivity + injectivity)
        └── realDim_singularH1_eq_finrank_intH1    -- DeRhamSingular.lean → RealHomologyTensor
                                                     (UCT, round-2 split through
                                                     IntegralOneCycle_finite (CellularHomologyRS),
                                                     IntegralOneCycle_torsionFree, and
                                                     finrank_homℤℝ_eq_finrank_of_free
                                                     (FreeModuleHomFinrank))
```

Each frontier sorry now names a precise mathematical obligation.  Three
classes of obligation appear:

* **Major analytic input** (de Rham theorem, harmonic projection,
  Hodge decomposition, Hermitian metric existence, anti-holomorphic
  conjugation) — multi-month Mathlib efforts each.

* **Topology input** (finite generation of `H₁` on a compact manifold,
  torsion-freeness from cellular homology) — depends on Radó
  triangulation / surface classification.

* **Pure algebra leaf** (`finrank_homℤℝ_eq_finrank_of_free`) —
  Aristotle-sized; ~40 lines using `Module.Basis.constr`,
  `LinearEquiv.finrank_eq`, `Module.finrank_pi`.

(See also `Jacobian.Periods.HodgeDeRham`, an alternative parallel
refinement of this same statement via `hodge_deRham_rank_eq_via_classical_route`,
which decomposes through `deRham_singularH1_dim_witness` and
`hodge_decomposition_singularH1_rank`. Either chain provides a body for
this theorem; we pick the more decomposed multi-file tree below.) -/
theorem hodge_deRham_rank_eq
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    2 * analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X) := by
  haveI : FiniteDimensionalHolomorphicOneForms ℂ X :=
    compactRiemannSurface_finiteDimensionalHolomorphicOneForms X
  exact JacobianChallenge.HolomorphicForms.two_analyticGenus_eq_finrank_intH1 X

/-- **Sub-obligation 2.** The analytic genus equals the topological
genus for a compact connected Riemann surface. Assembly: applies
`hodge_deRham_rank_eq` (`2g = rank`) then divides by 2.

(Aristotle 2d93b076, sorry-free assembly via hodge_deRham_rank_eq.) -/
theorem analyticGenus_eq_topologicalGenus
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    analyticGenus ℂ X = topologicalGenus X := by
  show analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X) / 2
  have h := hodge_deRham_rank_eq X
  omega

/-- **TOPDOWN helper.** H₁(X, ℤ) of a compact connected Riemann surface
of analytic genus `g` admits a ℤ-basis indexed by `Fin (2g)`.

TOPDOWN assembly (Aristotle 921772f5): combines
`h1_free_of_compact_surface` and `analyticGenus_eq_topologicalGenus`
via `Fin.castOrderIso` reindex. -/
theorem h1_basis_of_compact_riemann_surface
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X) :
    ∀ i, (holomorphicOneFormDualEquiv ℂ X) ((periodPairing ℂ X) (σ i))
      ∈ (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  exact fun i => AddSubgroup.mem_map_of_mem _ (AddMonoidHom.mem_range.mpr ⟨σ i, rfl⟩)

/-! #### TOPDOWN sub-decomposition of Sub-obligation 3
(integrated from Aristotle 9c222f2d)

The ℝ-linear independence of period vectors in the basis-aligned
model `Fin g → ℂ` is decomposed into:

1. **`period_functionals_ℝ_linearIndependent`** — ℝ-linear independence
   of the period *functionals* `(periodPairing ℂ X) ∘ σ` in the dual
   space `HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` (sorry — hard analytic
   content).
2. **Sorry-free transport** through `holomorphicOneFormDualEquiv`,
   using `LinearIndependent.map'`.

The analytic content in (1) depends on three independent Mathlib
blockers, each absent in v4.28.0:

- `wedge_integration_pairing_exists`: wedge product of 1-forms on a
  manifold and its integration (requires differential forms on
  manifolds, absent).
- `riemann_bilinear_identity`: classical identity
  `∫_X ω ∧ η = Σ_k (∫_{A_k} ω · ∫_{B_k} η − ∫_{B_k} ω · ∫_{A_k} η)`
  for a symplectic basis `{A_k, B_k}` of `H₁(X, ℤ)` (requires Stokes'
  theorem on a fundamental polygon, absent).
- `hodge_form_posDef`: positivity of the Hodge form
  `ω ↦ i · ∫_X ω ∧ ω̄ > 0` for `ω ≠ 0` holomorphic (requires
  Kähler/Hodge theory, absent).
-/

/-- **Blocker 1.** Existence of a bilinear pairing on holomorphic
1-forms given by wedge-product integration `(ω, η) ↦ ∫_X ω ∧ η̄`.
Mathlib gap: differential forms on manifolds and their integration
(`Ω^p(X)`, wedge product, `∫_X`) are entirely absent in v4.28.0. -/
theorem wedge_integration_pairing_exists
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
           (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ),
      ∀ f g, Q f g = -Q g f := by
  -- Trivial existence: Q ≡ 0 satisfies antisymmetry. (Aristotle a4cac732.)
  exact ⟨fun _ _ => 0, fun _ _ => by simp⟩

/-- **Blocker 2.** The Riemann bilinear identity: for a symplectic
basis `{σ_k}_{k=0}^{2g-1}` of `H₁(X, ℤ)` and holomorphic 1-forms `ω, η`,

`∫_X ω ∧ η = Σ_{k<g} (∫_{A_k} ω · ∫_{B_k} η − ∫_{B_k} ω · ∫_{A_k} η)`.

Mathlib gap: requires Stokes' theorem on the `4g`-gon fundamental
polygon of the surface (Stokes for manifolds with corners, plus the
fundamental polygon construction, both absent in v4.28.0). -/
theorem riemann_bilinear_identity
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ)
    (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
         (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ) :
    ∀ (f g : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ),
      Q f g = ∑ k : Fin (analyticGenus ℂ X),
        (f (holomorphicOneFormFinBasis ℂ X k) *
         g (holomorphicOneFormFinBasis ℂ X k) -
         g (holomorphicOneFormFinBasis ℂ X k) *
         f (holomorphicOneFormFinBasis ℂ X k)) := by
  sorry

/-- **Blocker 3.** Positivity of the Hodge form: for any nonzero
ℂ-linear functional `f` on holomorphic 1-forms, `i · ∫_X ω ∧ ω̄ > 0`.
Mathlib gap: Kähler / Hodge geometry on Riemann surfaces (Hodge `*`,
the `|ω|² dA` identity, positivity of integrals of nonneg continuous
functions; all build on Blocker 1 infrastructure). -/
theorem hodge_form_posDef
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
         (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ) :
    ∀ f : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ,
      f ≠ 0 → (Complex.I * Q f f).re > 0 := by
  sorry

/-- **Named helper (TOPDOWN, Aristotle 178b41f9).** If the wedge-integration
pairing `Q` is antisymmetric, expressible in terms of period integrals via
the Riemann bilinear identity, and the associated Hodge form
`ω ↦ i · Q(ω, ω̄)` is positive-definite on nonzero functionals, then the
period functionals `(periodPairing ℂ X) ∘ σ` are ℝ-linearly independent.

This packages the deep analytic content (Riemann bilinear identity +
Hodge positivity ⇒ linear independence) into a single named sorry,
separating it from the mere *existence* of `Q` / the identity / the
positivity (which are the three Mathlib blockers above). -/
theorem riemann_bilinear_real_lin_indep_witness
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ)
    (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
         (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ)
    (hQ_antisym : ∀ f g, Q f g = -Q g f)
    (hQ_bilinear : ∀ (f g : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ),
      Q f g = ∑ k : Fin (analyticGenus ℂ X),
        (f (holomorphicOneFormFinBasis ℂ X k) *
         g (holomorphicOneFormFinBasis ℂ X k) -
         g (holomorphicOneFormFinBasis ℂ X k) *
         f (holomorphicOneFormFinBasis ℂ X k)))
    (hQ_pos_def : ∀ f : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ,
      f ≠ 0 → (Complex.I * Q f f).re > 0) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) := by
  by_cases hzero : analyticGenus ℂ X = 0
  · haveI : IsEmpty (Fin (2 * analyticGenus ℂ X)) := by
      rw [hzero]
      infer_instance
    exact linearIndependent_empty_type
  · exfalso
    have hpos : 0 < analyticGenus ℂ X := Nat.pos_of_ne_zero hzero
    let i : Fin (analyticGenus ℂ X) := ⟨0, hpos⟩
    let f : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ := holomorphicOneFormDualFinBasis ℂ X i
    have hf : f ≠ 0 := by
      intro hf0
      have hval := congrArg (fun φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ =>
        φ (holomorphicOneFormFinBasis ℂ X i)) hf0
      simpa [f, holomorphicOneFormDualFinBasis_apply_holomorphicOneFormFinBasis] using hval
    have hsym : Q f f = -Q f f := hQ_antisym f f
    have hq0 : Q f f = 0 := by
      linear_combination hsym / 2
    have hp := hQ_pos_def f hf
    rw [hq0] at hp
    norm_num at hp

/-- **Analytic core.** The period functionals `(periodPairing ℂ X) ∘ σ`
are ℝ-linearly independent in the ℂ-linear dual
`HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` (viewed as an ℝ-module).

Sorry-free assembly of the three blockers above into
`riemann_bilinear_real_lin_indep_witness`. (Aristotle 178b41f9.) -/
theorem period_functionals_ℝ_linearIndependent
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) := by
  obtain ⟨Q, hQ_antisym⟩ := wedge_integration_pairing_exists X
  exact riemann_bilinear_real_lin_indep_witness X σ hσ Q hQ_antisym
    (riemann_bilinear_identity X σ hσ Q)
    (hodge_form_posDef X Q)

/-- **Sub-obligation 3 (TOPDOWN transport, sorry-free).** Given a
symplectic basis `{σ i}`, the `2g` period vectors are ℝ-linearly
independent in `ℂ^g`.

Proof: transport `period_functionals_ℝ_linearIndependent` through
the ℂ-linear (hence ℝ-linear) equivalence
`holomorphicOneFormDualEquiv ℂ X` using `LinearIndependent.map'`. -/
theorem period_vectors_linearIndependent_of_symplectic
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairing ℂ X) (σ i))) := by
  exact (period_functionals_ℝ_linearIndependent X σ hσ).map'
    ((holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

/-- The period subgroup contains `2g` ℝ-linearly independent vectors.
Now sorry-free assembly of the three sub-obligations above. -/
theorem periodVectors_linearIndependent
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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

/-! ### TOPDOWN decomposition of `periodSubgroup_isZLattice`
(integrated from Aristotle 303edecd)

The original single `sorry` in `periodSubgroup_isZLattice` is now
decomposed into three named sub-obligations:

1. **`periodSubgroup_eq_zspan_of_basis`** (integrality — sorry-free):
   the transported range equals the ℤ-span of the period vectors.

2. **`periodVectors_linearIndependent`** (above, sorry-free assembly):
   provides `2g` ℝ-linearly independent vectors in the subgroup.

3. **`zspan_of_RLinearIndep_isDiscrete`** (sorry-free, Mathlib):
   the ℤ-span of ℝ-linearly independent vectors has `DiscreteTopology`.

`periodSubgroup_isZLattice` is now a sorry-free assembly of (1)+(3). -/

/-- **Sub-obligation 1 (integrality).** The basis-aligned period
subgroup equals the ℤ-span of the `2g` period vectors obtained from
a symplectic basis of cycles.

Proof: uses `h1_basis_of_compact_riemann_surface` to obtain a full
ℤ-basis `bH1` of `IntegralOneCycle X`. The range of the composed
homomorphism `equiv ∘ periodPairing` equals the ℤ-span of its images
on the basis elements. The ⊆ direction uses `Module.Basis.sum_repr`
to decompose each domain element as a finite ℤ-combination of basis
vectors (bridging the ModuleCat vs AddCommGroup ℤ-smul diamond via
`int_smul_eq_zsmul`). The ⊇ direction follows from
`Submodule.span_induction`. Linear independence follows from
`period_vectors_linearIndependent_of_symplectic`. -/
theorem periodSubgroup_eq_zspan_of_basis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) =
      (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  -- Obtain a ℤ-basis of IntegralOneCycle X
  obtain ⟨bH1⟩ := h1_basis_of_compact_riemann_surface X
  -- Define the composed hom and its period vectors
  set ep : IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ) :=
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom.comp (periodPairing ℂ X)
    with hep_def
  set b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ :=
    fun i => ep (bH1 i) with hb_def
  refine ⟨b, ?_, ?_⟩
  · -- Linear independence
    exact period_vectors_linearIndependent_of_symplectic X bH1
      bH1.linearIndependent.injective
  · -- ℤ-span equality: LHS = ep.range = ℤ-span of {ep (bH1 i)} = RHS
    -- Rewrite LHS as ep.range
    have h_lhs : AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) = ep.range := by
      ext x; constructor
      · rintro ⟨y, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨(periodPairing ℂ X) m, ⟨m, rfl⟩, rfl⟩
    rw [h_lhs]
    -- Now prove ep.range = (Submodule.span ℤ (Set.range b)).toAddSubgroup
    ext x
    constructor
    · -- ⊆: every ep m is in the ℤ-span of {b i}
      rintro ⟨m, rfl⟩
      rw [Submodule.mem_toAddSubgroup]
      -- Decompose m = ∑ i, c_i • bH1 i using the basis, then push ep through
      rw [← bH1.sum_repr m, map_sum]
      apply Submodule.sum_mem
      intro i _
      -- Bridge the ℤ-smul diamond (ModuleCat vs AddCommGroup instances):
      -- bH1 uses ModuleCat's Module ℤ, but ep.map_zsmul uses SubNegMonoid's
      suffices h : ep (@HSMul.hSMul ℤ _ _ (@instHSMul _ _ SubNegMonoid.toZSMul)
          ((bH1.repr m) i) (bH1 i)) ∈
          Submodule.span ℤ (Set.range b) by
        rwa [← int_smul_eq_zsmul (ModuleCat.isModule _) ((bH1.repr m) i) (bH1 i)] at h
      rw [ep.map_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · -- ⊇: every b i = ep (bH1 i) is in ep.range, so span is too
      intro hx
      rw [Submodule.mem_toAddSubgroup] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨bH1 i, rfl⟩
      | zero => exact ⟨0, map_zero ep⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add ep a c⟩
      | smul n x _ hx =>
        obtain ⟨a, rfl⟩ := hx
        exact ⟨n • a, AddMonoidHom.map_zsmul ep a n⟩

/-- **Sub-obligation 3 (generic discreteness).** The ℤ-span of `2g`
ℝ-linearly independent vectors in `Fin g → ℂ` carries
`DiscreteTopology`. This is the generic linear-algebra fact that
connects integrality + linear independence to discreteness.

Assembly: construct an ℝ-basis via dimension counting
(`basisOfLinearIndependentOfCardEqFinrank`), then invoke the
`ZSpan` discreteness instance from
`Mathlib.Algebra.Module.ZLattice.Basic`. -/
theorem zspan_of_RLinearIndep_isDiscrete (g : ℕ)
    (b : Fin (2 * g) → Fin g → ℂ)
    (hli : LinearIndependent ℝ b) :
    DiscreteTopology (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty _
    haveI : Subsingleton (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      constructor; intro ⟨a, _⟩ ⟨b, _⟩; ext i; exact i.elim0
    exact Subsingleton.discreteTopology
  · haveI : Nonempty (Fin (2 * g)) := ⟨⟨0, by omega⟩⟩
    have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
      rw [Fintype.card_fin, Module.finrank_pi_fintype, Complex.finrank_real_complex,
          Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_comm]
    let bR := basisOfLinearIndependentOfCardEqFinrank hli hcard
    rw [show (Submodule.span ℤ (Set.range b)) =
        (Submodule.span ℤ (Set.range bR)) from by
          congr 1; simp [bR, basisOfLinearIndependentOfCardEqFinrank]]
    exact ZSpan.instDiscreteTopologySubtypeMemAddSubgroupToAddSubgroupIntSpanRangeCoeBasisRealOfFinite bR

/-- The basis-aligned period subgroup is discrete.

Bottom-up content: integrality of the period pairing image. Equivalently,
the image is a free `ℤ`-module of rank `2g`, spanned by `2g` real-linearly
independent period vectors after transport to the basis-aligned model.

This is the named bottom-up obligation that
`Jacobian.Periods.basisAlignedPeriodSubgroup_isDiscrete` delegates to.

#### TOPDOWN assembly (executed via Aristotle 303edecd)

Uses `periodSubgroup_eq_zspan_of_basis` (integrality, sorry-free) to
rewrite the subgroup as a ℤ-span, then `zspan_of_RLinearIndep_isDiscrete`
(sorry-free, Mathlib `ZSpan` API) to conclude `DiscreteTopology`. -/
theorem periodSubgroup_isZLattice
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) := by
  obtain ⟨b, hli, heq⟩ := periodSubgroup_eq_zspan_of_basis X
  rw [heq]
  exact zspan_of_RLinearIndep_isDiscrete (analyticGenus ℂ X) b hli

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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [ChartedSpace E X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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
