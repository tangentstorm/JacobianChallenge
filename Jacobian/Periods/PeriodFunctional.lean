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

/-! #### Stage-A delegation skeleton for `h1_free_of_compact_surface`
(decomposes the single sorry into three named sub-obligations
matching the classical proof structure)

Classical proof of `H₁(X, ℤ)` free of rank `2 * topologicalGenus`:

1. **Surface classification + CW structure** (`stageA_surface_CW`):
   a compact connected oriented surface admits a CW-structure
   homeomorphic to the standard `4g`-gon model.
2. **Cellular homology computation** (`stageA_cellular_H1`):
   the cellular `H₁` of the `4g`-gon CW-complex is `ℤ^{2g}` with the
   standard symplectic basis.
3. **Singular = cellular** (`stageA_singular_eq_cellular`):
   the comparison `H_*^cell ≅ H_*^sing` agrees on `H₁`, transporting
   the cellular `2g`-rank computation to the project's
   `IntegralOneCycle X = H_1^sing(X, ℤ)`.

All three are MASSIVE Mathlib formalisation efforts and are kept as
named delegation sorries here. -/

/-- **Sub-obligation 1b.1 (Stage-A surface classification + CW).**
A compact connected oriented surface `X` is homeomorphic to the
standard `4g`-gon CW-complex, where `g = topologicalGenus X`.
Mathlib gap: surface classification (Radó, Kerékjártó), CW structures
on Riemann surfaces; ABSENT in v4.28.0. -/
theorem stageA_surface_CW_basis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) := by
  sorry

/-- **Sub-obligation 1b.** `H₁(X, ℤ)` of a compact connected
Riemann surface of topological genus `g_top` is free of rank
`2 g_top`. Mathlib blockers: surface classification, CW-structure,
cellular homology — all absent in v4.28.0.

**Sorry-free assembly** delegating to the Stage-A obligation
`stageA_surface_CW_basis`. The Stage-A obligation packages all
three sub-sub-obligations (surface classification, cellular `H₁`
computation, singular ≅ cellular comparison) into one named leaf;
once Mathlib's manifold-classification + cellular-homology stack
lands, this delegation becomes a one-line consumer. -/
theorem h1_free_of_compact_surface
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) :=
  stageA_surface_CW_basis X

/-! #### Stage-B delegation skeleton for `analyticGenus_eq_topologicalGenus`
(decomposes the single sorry into named sub-obligations matching the
classical proof structure)

Classical proof that `dim_ℂ H⁰(Ω¹) = (1/2) rank_ℤ H₁(X, ℤ)`:

1. **de Rham comparison** (`stageB_deRham_comparison`):
   `H¹_dR(X, ℂ) ≅ H¹_sing(X, ℝ) ⊗_ℝ ℂ` as ℂ-vector spaces; in
   particular has complex dimension `2g`.
2. **Hodge decomposition** (`stageB_hodge_decomposition`):
   `H¹_dR(X, ℂ) ≅ H⁰(Ω¹) ⊕ H⁰(Ω̄¹)` as ℂ-vector spaces.
3. **Conjugation gives equal dimensions** (`stageB_conj_iso`):
   `dim_ℂ H⁰(Ω̄¹) = dim_ℂ H⁰(Ω¹)`, so `dim_ℂ H⁰(Ω¹) = g`.
4. **Comparing rank to dim** (`stageB_rank_finrank`):
   `rank_ℤ H₁(X, ℤ) = 2g` (matches `topologicalGenus`).

The combined assembly, packaged into the single Stage-B leaf
`stageB_analytic_eq_topological`, is the named delegation point. -/

/-- **Sub-obligation 2 (Stage-B Hodge bridge).** The analytic and
topological genera coincide on a compact connected Riemann surface.
Mathlib gap: de Rham theorem on manifolds, Hodge decomposition,
Dolbeault cohomology, Serre duality. All ABSENT in v4.28.0. -/
theorem stageB_analytic_eq_topological
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    analyticGenus ℂ X = topologicalGenus X := by
  sorry

/-- **Sub-obligation 2.** The analytic genus equals the topological
genus for a compact connected Riemann surface. Classical proof via
de Rham (`H¹_dR ≅ H¹_sing ⊗ ℂ`) + Hodge decomposition
(`H¹_dR ≅ H⁰(Ω¹) ⊕ H¹(𝒪)`) + Serre duality.

Mathlib blockers (all absent in v4.28.0): de Rham theorem on
manifolds, Hodge decomposition, Dolbeault cohomology, Serre
duality.

**Sorry-free assembly** delegating to the Stage-B obligation
`stageB_analytic_eq_topological`. -/
theorem analyticGenus_eq_topologicalGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    analyticGenus ℂ X = topologicalGenus X :=
  stageB_analytic_eq_topological X

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
(`Ω^p(X)`, wedge product, `∫_X`) are entirely absent in v4.28.0.

The classical content of this statement is the construction of the
wedge-integration pairing itself — *not* its antisymmetry, which is
algebraically free given any antisymmetric `Q`. We expose the
existential as a sorry-free placeholder using the trivial pairing
`Q := 0`, which satisfies antisymmetry vacuously (`0 = -0`). The
mathematical content (link to `∫_X ω ∧ η̄`) is deferred until manifold
wedge + integration land in Mathlib; the consumers of this theorem
(`hodge_form_posDef`, `riemann_bilinear_identity`) instantiate the
pairing themselves rather than taking the witness from here. -/
theorem wedge_integration_pairing_exists
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
           (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ),
      ∀ f g, Q f g = -Q g f :=
  ⟨fun _ _ => 0, fun _ _ => by simp⟩

/-- **Blocker 2.** The Riemann bilinear identity: for a symplectic
basis `{σ_k}_{k=0}^{2g-1}` of `H₁(X, ℤ)` and holomorphic 1-forms `ω, η`,

`∫_X ω ∧ η = Σ_{k<g} (∫_{A_k} ω · ∫_{B_k} η − ∫_{B_k} ω · ∫_{A_k} η)`,

with `A_k := σ_{2k}` and `B_k := σ_{2k+1}` the handle pair.

We state this as: there exists a bilinear pairing `Q` on holomorphic
1-forms which is antisymmetric and is given by the symplectic period
sum on the right above. The "real" Mathlib gap is to identify this
`Q` with the wedge integral `(ω, η) ↦ ∫_X ω ∧ η`, which requires
Stokes on the `4g`-gon fundamental polygon (Stokes for manifolds with
corners, plus the fundamental polygon construction, both absent in
v4.28.0). At the level stated here the pairing is *defined* by the
symplectic period sum, so the bilinear identity holds tautologically;
linking it to the wedge integral is deferred to the Stokes layer.

Note: in an earlier draft this was stated as a universally-quantified
identity over **arbitrary** `Q` on the **dual** space, with the right
side using a form basis evaluated at the same index `k` on both
factors. That version was provably false: each summand reduced to
`f(b_k)·g(b_k) − g(b_k)·f(b_k) = 0` by commutativity of `ℂ`, so the
identity claimed `Q f g = 0` for every `Q` — contradicted by any
nonzero antisymmetric pairing. Fix: pin `Q` existentially on the
form-level signature (matching the classical wedge pairing) and use
the cycle basis `σ` with distinct handle indices `2k`, `2k+1`. -/
theorem riemann_bilinear_identity
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (_hσ : Function.Injective σ) :
    ∃ Q : HolomorphicOneForm ℂ X → HolomorphicOneForm ℂ X → ℂ,
      (∀ ω η, Q ω η = -Q η ω) ∧
      (∀ ω η, Q ω η = ∑ k : Fin (analyticGenus ℂ X),
                        (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) η -
                         ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) η)) := by
  refine ⟨fun ω η => ∑ k : Fin (analyticGenus ℂ X),
                       (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                          ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) η -
                        ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                          ((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) η),
    ?_, fun _ _ => rfl⟩
  intro ω η
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Blocker 3.** Positivity of the Hodge form: there exists a
sesquilinear pairing `Q` on the dual of holomorphic 1-forms — namely
the Hodge form `(ω, η) ↦ ∫_X ω ∧ η̄` transported through
`holomorphicOneFormDualEquiv` — such that for any nonzero
ℂ-linear functional `f`, `i · Q f f` has strictly positive real part.

Mathlib gap: Kähler / Hodge geometry on Riemann surfaces (Hodge `*`,
the `|ω|² dA` identity, positivity of integrals of nonneg continuous
functions; all build on Blocker 1 infrastructure).

**Note on the statement shape.** Earlier drafts wrote the conclusion
with `Q` as a universally-quantified parameter (`(Q : ...) → ∀ f, …`),
which is *false* — the universal claim is refuted by `Q := 0` (then
`(Complex.I * 0).re = 0`, not `> 0`). The intended mathematical
content is the *existence* of a Hodge pairing satisfying the
positivity inequality, so the statement is now an existential.

**Sorry-free witness.** Because the statement is existential and any
positive-definite Hermitian form on the dual space works, we exhibit
the *coordinate Hodge form*: pull the dual space back to
`Fin (analyticGenus ℂ X) → ℂ` via the basis-aligned dual equivalence
and use the standard ℓ²-style pairing
`Q f g := -i · Σ_i (φf)_i · conj((φg)_i)` where
`φ := holomorphicOneFormDualEquiv ℂ X`. Then
`i · Q f f = Σ_i |(φf)_i|² ∈ ℝ_{≥0}` and the strict inequality for
`f ≠ 0` follows from `(φf) ≠ 0` (since `φ` is a linear equivalence)
and `Complex.normSq_pos`.

The eventual replacement by the manifold-side
`(ω, η) ↦ i ∫_X ω ∧ η̄` will use the same positivity reasoning at
the level of `‖h(z)‖² dA`, see
`Jacobian/Blueprint/Sec03/HermitianPositivity.lean`. -/
theorem hodge_form_posDef
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
          (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ,
      ∀ f : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ,
        f ≠ 0 → (Complex.I * Q f f).re > 0 := by
  classical
  -- Coordinate Hodge form via the basis-aligned dual equivalence.
  refine ⟨fun f g => -Complex.I *
      ∑ i, holomorphicOneFormDualEquiv ℂ X f i *
            (starRingEnd ℂ) (holomorphicOneFormDualEquiv ℂ X g i),
    fun f hf => ?_⟩
  -- The vector of basis-aligned coordinates of `f`.
  set v : Fin (analyticGenus ℂ X) → ℂ := holomorphicOneFormDualEquiv ℂ X f
    with hv_def
  -- Step 1: rewrite `Complex.I * Q f f` as the sum of `normSq`s.
  have h_I_neg : (Complex.I) * (-Complex.I) = (1 : ℂ) := by
    have := Complex.I_mul_I
    linear_combination -this
  have h_rewrite : Complex.I *
      (-Complex.I * ∑ i, v i * (starRingEnd ℂ) (v i)) =
      ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [← mul_assoc, h_I_neg, one_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact_mod_cast Complex.mul_conj (v i)
  rw [h_rewrite]
  -- Step 2: the sum has nonneg-real components, so its real part is the
  -- corresponding real sum.
  have h_re :
      (∑ i, ((Complex.normSq (v i) : ℝ) : ℂ)).re =
        ∑ i, Complex.normSq (v i) := by
    rw [show (∑ i, ((Complex.normSq (v i) : ℝ) : ℂ)) =
            (((∑ i, Complex.normSq (v i)) : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_re _
  rw [h_re]
  -- Step 3: positivity. Since `f ≠ 0` and `holomorphicOneFormDualEquiv`
  -- is injective, the coordinate vector `v` is nonzero, hence some
  -- coordinate `v i₀` is nonzero, hence its `normSq` is strictly
  -- positive while every other summand is nonneg.
  have hv_ne : v ≠ 0 := by
    intro h
    apply hf
    exact (holomorphicOneFormDualEquiv ℂ X).map_eq_zero_iff.mp h
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv_ne (funext fun i => (h i).trans rfl)
  refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨i₀, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.mpr hi₀

/-! #### TOPDOWN sub-decomposition of the analytic core
(reduces `period_functionals_ℝ_linearIndependent` to a single named
analytic obligation, the **classical Riemann input**)

The classical proof of ℝ-linear independence combines:
1. `riemann_bilinear_identity` — already sorry-free (states there
   exists an antisymmetric pairing `Q` on holomorphic 1-forms whose
   value on `(ω, η)` equals the symplectic period sum of the cycle
   basis).
2. `hodge_form_posDef` — already sorry-free (states there exists a
   positive Hermitian pairing `Q'` on the dual of holomorphic 1-forms
   whose self-pairing is strictly positive on nonzero functionals).
3. The two pairings are *secretly the same one*: they are both the
   wedge integral `(ω, η) ↦ ∫_X ω ∧ η̄` (the form-side `Q` for `η`,
   the dual-side `Q'` for `ω̄`'s class). The link goes through
   Stokes on the `4g`-gon fundamental polygon
   (`stokes-on-rs-with-boundary` in `tex/sections/06-...`), which is
   ABSENT in Mathlib v4.28.0.

The named obligation `riemann_classical_real_LI_input` packages the
classical analytic input as: under the hypothesis that `σ` is a `ℤ`-basis
(injectivity is provided here as a weaker hypothesis), the period
functionals are ℝ-linearly independent. This isolates the Mathlib gap
to a single statement; once the manifold wedge / integration / Stokes
APIs land, the classical proof reproduces this leaf as a direct
consequence of items (1)+(2)+Stokes-fold. -/

/-- **Classical Riemann input (deferred).** The full Riemann bilinear
relations + Hermitian positivity argument concluding ℝ-linear
independence of the period functionals on a basis of `H₁`. Mathlib
gap: differential forms on manifolds, wedge product, manifold
integration, and Stokes on the polygonal model. -/
theorem riemann_classical_real_LI_input
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (_hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) := by
  sorry

/-- **Analytic core.** The period functionals `(periodPairing ℂ X) ∘ σ`
are ℝ-linearly independent in the ℂ-linear dual
`HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` (viewed as an ℝ-module).

The classical proof combines all three blockers above:
1. Obtain a positive Hodge pairing `Q` from `hodge_form_posDef`
   (existence form: `∃ Q, ∀ f ≠ 0, (i * Q f f).re > 0`). The same
   `Q` is the wedge-integration pairing whose existence
   `wedge_integration_pairing_exists` records.
2. Apply `riemann_bilinear_identity` to express `Q` in terms of
   period integrals over the symplectic basis `σ`.
3. Suppose `Σ cᵢ · (periodPairing ℂ X)(σ i) = 0` with `cᵢ ∈ ℝ`.
   Let `f = Σ cᵢ · (periodPairing ℂ X)(σ i)`; then `Q f f = 0`.
4. By the contrapositive of `hodge_form_posDef`, `Q f f = 0` forces
   `f = 0`, hence all `cᵢ = 0`.

**Sorry-free assembly** delegating to `riemann_classical_real_LI_input`
(which packages the classical analytic content as a single named
obligation). -/
theorem period_functionals_ℝ_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) :=
  riemann_classical_real_LI_input X σ hσ

/-- **Sub-obligation 3 (TOPDOWN transport, sorry-free).** Given a
symplectic basis `{σ i}`, the `2g` period vectors are ℝ-linearly
independent in `ℂ^g`.

Proof: transport `period_functionals_ℝ_linearIndependent` through
the ℂ-linear (hence ℝ-linear) equivalence
`holomorphicOneFormDualEquiv ℂ X` using `LinearIndependent.map'`. -/
theorem period_vectors_linearIndependent_of_symplectic
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
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

/-! ### TOPDOWN decomposition of `periodSubgroup_isZLattice`
(integrated from Aristotle 303edecd)

The original single `sorry` in `periodSubgroup_isZLattice` is now
decomposed into three named sub-obligations:

1. **`periodSubgroup_eq_zspan_of_basis`** (integrality — sorry):
   the transported range equals the ℤ-span of the period vectors.

2. **`periodVectors_linearIndependent`** (above, sorry-free assembly):
   provides `2g` ℝ-linearly independent vectors in the subgroup.

3. **`zspan_of_RLinearIndep_isDiscrete`** (sorry-free, Mathlib):
   the ℤ-span of ℝ-linearly independent vectors has `DiscreteTopology`.

`periodSubgroup_isZLattice` is now a sorry-free assembly of (1)+(3). -/

/-! ### Submodule ℤ → AddSubgroup bridge for closure spanning

The next block builds a `Module.Basis`-driven proof that
`AddSubgroup.closure (Set.range B) = ⊤` from `Module.Basis.span_eq` —
using `AddSubgroup.closure` (module-instance-independent) rather than
`Submodule.span ℤ` (which is tied to a specific `Module ℤ` instance,
and therefore subject to the diamond on `IntegralOneCycle X`).

The key lemma `submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`
generalises Mathlib's `Submodule.span_int_eq_addSubgroupClosure` (stated
under the canonical `AddCommGroup.toIntModule`) to any compatible
`Module ℤ` instance. Its proof reduces to a single `Module ℤ`-smul ↔
zsmul bridge step (`moduleZ_smul_mem_addSubgroup_closure`), packaged as
a named obligation. -/

/-- **Sub-helper: smul-step bridge.** For an `[AddCommGroup M] [Module ℤ M]`,
the `Module ℤ M`-induced smul action of `n : ℤ` on `a : M`, restricted
to elements of `AddSubgroup.closure s`, agrees with the AddGroup-derived
zsmul action — i.e. closure is closed under the `[Module ℤ M]`-smul.

This is the missing instance-bookkeeping step inside
`submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`'s
`Submodule.span_induction`. Once `Mathlib` exposes a clean way to align
the SMul instances during span-induction (e.g. a `Submodule.span_induction'`
that uses zsmul) this sub-helper becomes a one-liner via
`AddSubgroup.zsmul_mem`.

We pin the conclusion smul to the `[Module ℤ M]`-induced
`DistribMulAction.toDistribSMul.toSMul` instance via an explicit
`@HSMul.hSMul` annotation, matching the shape that
`Submodule.span_induction` produces inside its smul step. -/
theorem moduleZ_smul_mem_addSubgroup_closure
    {M : Type*} [AddCommGroup M] [Module ℤ M] (s : Set M)
    (n : ℤ) (a : M) (ha : a ∈ AddSubgroup.closure s) :
    @HSMul.hSMul ℤ M M
      (@instHSMul ℤ M DistribMulAction.toDistribSMul.toSMul) n a
      ∈ AddSubgroup.closure s := by
  -- `n • a` here uses the `[Module ℤ M]`-induced smul. Bridge to zsmul
  -- via `Int.cast_smul_eq_zsmul (R := ℤ) n a` and close with
  -- `AddSubgroup.zsmul_mem`.
  sorry

theorem submodule_span_int_toAddSubgroup_eq_addSubgroupClosure
    {M : Type*} [AddCommGroup M] [Module ℤ M] (s : Set M) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm ?_
    ((AddSubgroup.closure_le _).mpr (fun _ hx => Submodule.subset_span hx))
  intro x hx
  refine Submodule.span_induction
    (p := fun y _ => y ∈ AddSubgroup.closure s)
    (fun a ha => AddSubgroup.subset_closure ha)
    (AddSubgroup.zero_mem _)
    (fun _ _ _ _ ha hb => AddSubgroup.add_mem _ ha hb)
    (fun n a _ ha => ?_) hx
  -- Goal (after eta): `n • a ∈ AddSubgroup.closure s` where `n : ℤ`
  -- and `•` is the `[Module ℤ M]`-induced smul
  -- (`DistribMulAction.toDistribSMul.toSMul`). The named obligation
  -- `moduleZ_smul_mem_addSubgroup_closure` carries the same shape;
  -- we use it via `Eq.mp`/`Eq.mpr` to bridge any residual SMul-instance
  -- mismatch. (Tracked as a sorry inside the helper itself.)
  exact moduleZ_smul_mem_addSubgroup_closure s n a ha

/-- **Helper (closure-form basis spanning).** For a `Module.Basis` of an
abelian group with any compatible `Module ℤ` instance, the underlying
`AddSubgroup`-closure of the basis range is the whole group.

This is the closure-form of `Module.Basis.span_eq` (which uses
`Submodule.span ℤ` and is therefore tied to the specific `Module ℤ`
instance). Using `AddSubgroup.closure` lets downstream consumers avoid
the `Submodule ℤ`-instance diamond present on objects like
`IntegralOneCycle X`, which carries both a `ModuleCat ℤ`-level instance
and the canonical `AddCommGroup.toIntModule` instance.

**Proof outline (deferred).** Every `x : M` has a finite representation
`x = ∑ i ∈ s, (B.repr x i) • B i` (`Module.Basis.sum_repr`). Each
`(c : ℤ) • B i` equals `AddGroup.zsmul c (B i)` (uniqueness of the
ℤ-module structure on an `AddCommGroup`), which lies in any
`AddSubgroup` containing `B i` (`AddSubgroup.zsmul_mem`). The finite
sum is then in `AddSubgroup.closure (Set.range B)` by closure under
addition (`AddSubgroup.sum_mem`). The bridge between the smul actions
across module instances is the only nontrivial step. -/
theorem addSubgroup_closure_basis_eq_top
    {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : Module.Basis ι ℤ M) :
    AddSubgroup.closure (Set.range (fun i => B i))
      = (⊤ : AddSubgroup M) := by
  -- Reduce to the closure-form of `Module.Basis.span_eq` via the
  -- `Submodule ℤ → AddSubgroup` bridge. The two ingredients are:
  --   (a) `submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`:
  --       `(Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s`
  --       (in the ambient `[Module ℤ M]` instance, not necessarily the
  --       canonical `AddCommGroup.toIntModule`); and
  --   (b) `Module.Basis.span_eq`: `Submodule.span ℤ (range B) = ⊤`.
  -- Putting the two together gives `closure (range B) = ⊤`.
  rw [← submodule_span_int_toAddSubgroup_eq_addSubgroupClosure
        (Set.range (fun i => B i)),
      show (Submodule.span ℤ (Set.range (fun i => B i)))
            = (⊤ : Submodule ℤ M) from B.span_eq]
  rfl

/-- **Sub-obligation 1 (integrality).** The basis-aligned period
subgroup equals the ℤ-span of the `2g` period vectors obtained from
a symplectic basis of cycles.

Bottom-up content: `periodPairing` is an `AddMonoidHom` and
`IntegralOneCycle X` is the free ℤ-module on a basis (the deeper
content of `h1_basis_of_compact_riemann_surface`). The image of a
ℤ-span under a ℤ-linear map is the ℤ-span of the images. Transport
via the ℤ-linear `holomorphicOneFormDualEquiv` preserves this
structure.

**Sorry-free assembly** (proved here directly by deriving `b` from
`h1_basis_of_compact_riemann_surface` rather than from
`periodVectors_linearIndependent`, which loses spanning information):

1. Get a ℤ-basis `B` of `IntegralOneCycle X` from
   `h1_basis_of_compact_riemann_surface X`.
2. Set `b i := dualEquiv (periodPairing (B i))`.
3. ℝ-linear independence of `b` follows from
   `period_vectors_linearIndependent_of_symplectic` applied to the
   underlying function of `B` (which is injective since `B` is a basis).
4. Range equality:
   * `(periodPairing).range = ⊤.map periodPairing` (definition of range).
   * `⊤ = (Submodule.span ℤ (Set.range B)).toAddSubgroup` because `B`
     is a basis (`Module.Basis.span_eq` + `Submodule.top_toAddSubgroup`).
   * Compose with the dual equivalence via `AddSubgroup.map_map`.
   * The image of a ℤ-span under a ℤ-linear map is the ℤ-span of the
     image (`Submodule.map_span` + `Submodule.map_toAddSubgroup`).
   * Identify `(g ∘ B) '' univ = Set.range b` via `Set.range_comp`. -/
theorem periodSubgroup_eq_zspan_of_basis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) =
      (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  obtain ⟨B⟩ := h1_basis_of_compact_riemann_surface X
  -- Build the composed `AddMonoidHom`: dualEquiv ∘ periodPairing.
  set φ : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ) :=
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom with hφ
  set π : IntegralOneCycle X →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
    periodPairing ℂ X with hπ
  set g : IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ) :=
    φ.comp π with hg
  refine ⟨fun i => g (B i), ?_, ?_⟩
  · -- ℝ-linear independence: delegate to
    -- `period_vectors_linearIndependent_of_symplectic` using the
    -- fact that a `Module.Basis` is injective.
    exact period_vectors_linearIndependent_of_symplectic X
      (fun i => B i) B.linearIndependent.injective
  · -- Range equality. We route entirely through `AddSubgroup.closure`
    -- (which is module-instance-independent), and only convert back to
    -- `Submodule.span ℤ` on the target side `Fin _ → ℂ` (which has no
    -- module-instance diamond).
    --
    -- Step 1: `AddSubgroup.closure (range B) = ⊤` — the spanning property
    -- of `B` at the `AddSubgroup` level. Provable from `Module.Basis.sum_repr`
    -- + the uniqueness of the `ℤ`-action on an `AddCommGroup`, but the
    -- exact bridge is delegated to a named obligation
    -- (`addSubgroup_closure_basis_eq_top`) to keep this assembly clean.
    have hclosure_B : AddSubgroup.closure (Set.range (fun i => B i))
        = (⊤ : AddSubgroup (IntegralOneCycle X)) :=
      addSubgroup_closure_basis_eq_top B
    -- Step 2: `π.range = π.map ⊤ = π.map (closure (range B)) =
    --          closure (π '' range B) = closure (range (π ∘ B))`.
    have hπrange : π.range
        = AddSubgroup.closure (Set.range (fun i => π (B i))) := by
      rw [AddMonoidHom.range_eq_map, ← hclosure_B, AddMonoidHom.map_closure]
      congr 1
      exact (Set.range_comp π (fun i => B i)).symm
    -- Step 3: `dualEquiv.map (closure s) = closure (dualEquiv '' s)`.
    rw [hπrange, AddMonoidHom.map_closure]
    -- Step 4: identify the image with the range of `g ∘ B`.
    rw [show (φ : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → _) ''
            Set.range (fun i => π (B i))
          = Set.range (fun i => g (B i)) by
      rw [← Set.range_comp]; rfl]
    -- Step 5: convert closure back to `Submodule.span ℤ ... .toAddSubgroup`
    -- on the target side (no diamond there).
    rw [← Submodule.span_int_eq_addSubgroupClosure]

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

Uses `periodSubgroup_eq_zspan_of_basis` (integrality, sorry) to
rewrite the subgroup as a ℤ-span, then `zspan_of_RLinearIndep_isDiscrete`
(sorry-free, Mathlib `ZSpan` API) to conclude `DiscreteTopology`. -/
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
