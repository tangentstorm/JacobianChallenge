import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Real.Basic

/-!
# Pure-algebra refinement of `finrank_homℤℝ_eq_finrank_of_free`

The claim `finrank_homℤℝ_eq_finrank_of_free` (in
`IntegralOneCycleRank.lean`) is a pure-algebra statement: for any
finitely generated free ℤ-module `M`,

dim_ℝ Hom_ℤ(M, ℝ) = rank_ℤ M.

## What this file provides

These discharge the original monolithic pure-algebra obligation using
`Module.Basis.constr`, `LinearEquiv.finrank_eq`, and Mathlib's
finite-free `Module.finBasis`.
-/

namespace JacobianChallenge.Periods

/--
**Basis-evaluation equivalence.** For a ℤ-basis
`b : Fin n → M`, the evaluation map `f ↦ (f ∘ b)` from
`Hom_ℤ(M, ℝ)` to `Fin n → ℝ` is an ℝ-linear equivalence.

This is `Module.Basis.constr` with scalar field `ℝ`, reversed.
-/
theorem homℤℝ_basis_evaluation_isLinearEquivℝ
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin n) ℤ M) :
    ∃ _ : (M →ₗ[ℤ] ℝ) ≃ₗ[ℝ] (Fin n → ℝ), True := by
  exact ⟨(b.constr ℝ).symm, trivial⟩


theorem finrank_pi_real_eq_card (n : ℕ) :
    Module.finrank ℝ (Fin n → ℝ) = n := by
  exact Module.finrank_fin_fun ℝ


theorem finrank_homℤℝ_eq_basis_card
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin n) ℤ M) :
    Module.finrank ℝ (M →ₗ[ℤ] ℝ) = n := by
  obtain ⟨e, _⟩ := homℤℝ_basis_evaluation_isLinearEquivℝ b
  rw [e.finrank_eq, finrank_pi_real_eq_card]


theorem finrank_homℤℝ_eq_finrank_of_free_via_basis
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M := by
  exact finrank_homℤℝ_eq_basis_card (Module.finBasis ℤ M)

end JacobianChallenge.Periods
