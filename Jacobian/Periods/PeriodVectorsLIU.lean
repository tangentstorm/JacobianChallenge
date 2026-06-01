import Jacobian.Periods.H1BasisU
import Jacobian.Periods.BasisAlignedPeriodSubgroupU
import Jacobian.Periods.PeriodFunctionalU
import Jacobian.Periods.PeriodSpanHelpers
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv

/-!
# Universe-polymorphic period-vector independence and spanning

`Jacobian/Periods/PeriodFunctional.lean` builds the full-rank content of the
Type-0 period lattice through the chain
`riemann_classical_real_LI_input` → `period_functionals_ℝ_linearIndependent`
→ `period_vectors_linearIndependent_of_symplectic` →
`periodVectors_linearIndependent` → `periodSubgroup_spans_real`.

This file mirrors that chain at `Type u` for the universe-`u` period subgroup
(C2c-ii of the authorized full `Type u` generalization, Option C containment),
ending at the universe-`u` spanning fact `periodSubgroup_spans_realU`. With this
in hand, the universe-`u` `IsZLattice ℝ` and compact fundamental domain (C2c-iii)
can be assembled, completing the `FullComplexLattice` fields for the public
`Jacobian (X : Type u)`.

## Frontier obligation

The base of the chain, `riemann_classical_real_LI_inputU`, is the universe-`u`
analogue of the **existing** Type-0 `sorry` `riemann_classical_real_LI_input`
(PeriodFunctional.lean): the assertion that the period matrix of a symplectic
homology basis has ℝ-linearly independent rows. Its genuine proof requires
Riemann bilinear nondegeneracy / Hodge positivity and Stokes on the fundamental
polygon — classical content absent in Mathlib v4.28.0, tracked project-wide. It
is recorded here as a single named Periods layer-frontier sorry — NOT a sorry in
`Jacobian/Solution.lean`'s public anti-hack block, NOT an axiom — matching the
accepted Type-0 honesty level. Everything else in this file is genuine (a verbatim
mirror of the Type-0 proofs with the universe-`u` substitutions).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
**Riemann-bilinear ℝ-linear-independence input (universe-`u`, tracked frontier
obligation).** The period functionals `periodPairingComplexU X ∘ σ` of a
symplectic homology basis `σ` are ℝ-linearly independent.

Universe-`u` analogue of the existing Type-0 `sorry`
`riemann_classical_real_LI_input`; see the module docstring.
-/
theorem riemann_classical_real_LI_inputU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (periodPairingComplexU X) (σ i)) :=
  sorry

/--
The period functionals `periodPairingComplexU X ∘ σ` are ℝ-linearly independent
in the ℂ-linear dual `HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ`. Universe-`u` companion to
`period_functionals_ℝ_linearIndependent`.
-/
theorem period_functionals_ℝ_linearIndependentU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (periodPairingComplexU X) (σ i)) :=
  riemann_classical_real_LI_inputU X σ hσ

/--
The period vectors `dualEquiv ∘ periodPairingComplexU X ∘ σ` are ℝ-linearly
independent in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.
Universe-`u` companion to `period_vectors_linearIndependent_of_symplectic`;
transports `period_functionals_ℝ_linearIndependentU` through the dual equivalence.
-/
theorem period_vectors_linearIndependent_of_symplecticU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (hσ : Function.Injective σ) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairingComplexU X) (σ i))) :=
  (period_functionals_ℝ_linearIndependentU X σ hσ).map'
    ((holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

/--
A compact connected Riemann surface `X : Type u` has `2g` integral 1-cycles in
`IntegralOneCycleU X` forming an injective family. Universe-`u` companion to
`symplectic_basis_of_cycles`; extracted from the universe-`u` H₁ basis (C2c-i).
-/
theorem symplectic_basis_of_cyclesU :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X),
      Function.Injective σ := by
  obtain ⟨b⟩ := h1_basis_of_compact_riemann_surfaceU X
  exact ⟨b, b.linearIndependent.injective⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Each period vector lies in the universe-`u` basis-aligned period subgroup.
Universe-`u` companion to `period_vectors_mem_subgroup`.
-/
theorem period_vectors_mem_subgroupU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X) :
    ∀ i, (holomorphicOneFormDualEquiv ℂ X) ((periodPairingComplexU X) (σ i))
      ∈ (basisAlignedPeriodSubgroupConcreteU X :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := fun i =>
  AddSubgroup.mem_map_of_mem _ (AddMonoidHom.mem_range.mpr ⟨σ i, rfl⟩)

/--
There exist `2g` ℝ-linearly independent vectors lying in the universe-`u`
basis-aligned period subgroup. Universe-`u` companion to
`periodVectors_linearIndependent`.
-/
theorem periodVectors_linearIndependentU :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      ∀ i, b i ∈ (basisAlignedPeriodSubgroupConcreteU X :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  obtain ⟨σ, hσ⟩ := symplectic_basis_of_cyclesU X
  exact ⟨fun i => (holomorphicOneFormDualEquiv ℂ X) ((periodPairingComplexU X) (σ i)),
         period_vectors_linearIndependent_of_symplecticU X σ hσ,
         period_vectors_mem_subgroupU X σ⟩

/--
The universe-`u` basis-aligned period subgroup spans the full ℝ-vector space
`Fin (analyticGenus ℂ X) → ℂ`. Universe-`u` companion to `periodSubgroup_spans_real`;
the second half of the `IsZLattice ℝ` content. Uses the pure helper
`span_real_eq_top_of_subset_linearIndependent` as-is.
-/
theorem periodSubgroup_spans_realU :
    Submodule.span ℝ
      ((basisAlignedPeriodSubgroupConcreteU X :
        AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
        Set (Fin (analyticGenus ℂ X) → ℂ))
      = ⊤ := by
  obtain ⟨b, hli, hmem⟩ := periodVectors_linearIndependentU X
  exact span_real_eq_top_of_subset_linearIndependent
    (analyticGenus ℂ X)
    ((basisAlignedPeriodSubgroupConcreteU X :
      AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
      Set (Fin (analyticGenus ℂ X) → ℂ))
    b hli (Set.range_subset_iff.mpr hmem)

end JacobianChallenge.Periods
