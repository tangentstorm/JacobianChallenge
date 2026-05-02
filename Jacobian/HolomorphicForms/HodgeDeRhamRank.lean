import Jacobian.HolomorphicForms.HodgeDecomposition
import Jacobian.HolomorphicForms.DeRhamSingular
import Jacobian.Periods.IntegralOneCycleRank
import Jacobian.HolomorphicForms.CompactRiemannSurface

/-!
# Top-level assembly: `2g = rank ℤ H₁(X, ℤ)` (Hodge / de Rham bridge)

Sorry-free assembly of the two named ℕ-equalities supplied by

* `Jacobian.HolomorphicForms.HodgeDecomposition`
  (`realDimDeRhamH1_eq_two_analyticGenus`):
  `realDimDeRhamH1 X = 2 * analyticGenus ℂ X` — Hodge side.

* `Jacobian.HolomorphicForms.DeRhamSingular`
  (`realDim_deRhamH1_eq_finrank_intH1`):
  `realDimDeRhamH1 X = Module.finrank ℤ (IntegralOneCycle X)` —
  de Rham + UCT side.

Both equalities have `realDimDeRhamH1 X` on the LHS, so transitivity
gives `2 * analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X)`,
which is exactly the body of
`JacobianChallenge.Periods.hodge_deRham_rank_eq`.

This file consumes only the named *named-frontier-obligation* layer
above it; the actual analytic + topological content (de Rham theorem,
Hodge decomposition, Serre / conjugation, UCT, finite-CW structure on
manifolds) is concentrated in those upstream modules.

## TOPDOWN role

This is the **outermost assembly** in the top-down refinement of
`hodge_deRham_rank_eq`. It is sorry-free relative to its named
obligations.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Sorry-free top-level assembly.**
`2 * analyticGenus ℂ X = rank_ℤ H₁(X, ℤ)` for a compact connected Riemann
surface.

Combines:

1. **Hodge side.** `realDimDeRhamH1 X = 2 * analyticGenus ℂ X`
   (`realDimDeRhamH1_eq_two_analyticGenus`), itself a sorry-free
   assembly of:
   - `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (real-of-complex
     identification),
   - `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (Hodge harmonic
     projection),
   - `analyticHarmonicGenus_eq_analyticGenus_add_anti` (Hodge
     decomposition by bidegree),
   - `analyticAntiGenus_eq_analyticGenus` (conjugation isomorphism).

2. **De Rham side.** `realDimDeRhamH1 X = rank_ℤ H₁(X, ℤ)`
   (`realDim_deRhamH1_eq_finrank_intH1`), itself a sorry-free assembly
   of:
   - `realDim_deRhamH1_eq_realDim_singularH1` (de Rham theorem on
     a compact smooth manifold),
   - `realDim_singularH1_eq_finrank_intH1` (universal-coefficient +
     algebra: `dim_ℝ Hom(H₁, ℝ) = rank_ℤ H₁`).

The chain is `2g = realDim H¹_dR = rank ℤ H₁`. -/
theorem two_analyticGenus_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    2 * analyticGenus ℂ X
      = Module.finrank ℤ (JacobianChallenge.Periods.IntegralOneCycle X) := by
  rw [← realDimDeRhamH1_eq_two_analyticGenus X,
      realDim_deRhamH1_eq_finrank_intH1 X]

end JacobianChallenge.HolomorphicForms
