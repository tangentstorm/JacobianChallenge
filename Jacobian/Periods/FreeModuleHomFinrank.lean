import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Pure-algebra refinement of `finrank_homℤℝ_eq_finrank_of_free`

The claim `finrank_homℤℝ_eq_finrank_of_free` (in
`IntegralOneCycleRank.lean`) is a pure-algebra statement: for any
finitely generated free ℤ-module `M`,

  dim_ℝ Hom_ℤ(M, ℝ) = rank_ℤ M.

This file refines that single sorry into smaller named obligations
that closely mirror Mathlib's `Module.Basis` API.

## What this file provides (round 2 refinement)

* `homℤℝ_basis_evaluation_isLinearEquivℝ` — basis-evaluation
  equivalence:
  given a ℤ-basis `b : Fin n → M`, the evaluation map
  `Hom_ℤ(M, ℝ) → (Fin n → ℝ)` is a ℝ-linear equivalence.
* `finrank_pi_real_eq_card` — pure-Mathlib fact, sorry-free:
  `dim_ℝ (Fin n → ℝ) = n`.
* `finrank_homℤℝ_eq_basis_card` — assembled, sorry-free.
* `finrank_homℤℝ_eq_finrank_of_free_via_basis` — refined,
  sorry-free through `Module.finBasis`.

These discharge the original monolithic pure-algebra obligation using
`Module.Basis.constr`, `LinearEquiv.finrank_eq`, and Mathlib's
finite-free `Module.finBasis`.
-/

namespace JacobianChallenge.Periods

/-- **Basis-evaluation equivalence.** For a ℤ-basis
`b : Fin n → M`, the evaluation map `f ↦ (f ∘ b)` from
`Hom_ℤ(M, ℝ)` to `Fin n → ℝ` is an ℝ-linear equivalence.

This is `Module.Basis.constr` with scalar field `ℝ`, reversed. -/
theorem homℤℝ_basis_evaluation_isLinearEquivℝ
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin n) ℤ M) :
    ∃ _ : (M →ₗ[ℤ] ℝ) ≃ₗ[ℝ] (Fin n → ℝ), True := by
  exact ⟨(b.constr ℝ).symm, trivial⟩

/-- **Sorry-free Mathlib fact.** `dim_ℝ (Fin n → ℝ) = n`.

Stated as a frontier identity to avoid name-bookkeeping for the
particular Mathlib lemma that supplies it (one of
`Module.finrank_fintype_fun_eq_card`, `Module.finrank_pi`, or a
combination); a one-line proof is direct in any current Mathlib
revision. -/
theorem finrank_pi_real_eq_card (n : ℕ) :
    Module.finrank ℝ (Fin n → ℝ) = n := by
  exact Module.finrank_fin_fun ℝ

/-- **Sorry-free assembly.** From the basis-evaluation equivalence,
`dim_ℝ Hom_ℤ(M, ℝ) = n` whenever `M` has a ℤ-basis indexed by
`Fin n`. -/
theorem finrank_homℤℝ_eq_basis_card
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin n) ℤ M) :
    Module.finrank ℝ (M →ₗ[ℤ] ℝ) = n := by
  obtain ⟨e, _⟩ := homℤℝ_basis_evaluation_isLinearEquivℝ b
  rw [e.finrank_eq, finrank_pi_real_eq_card]

/-- **Round-2 sorry-free assembly.** `finrank_homℤℝ_eq_finrank_of_free`
through the named basis-evaluation equivalence and Mathlib's
finite-rank free basis indexed by `Fin (Module.finrank ℤ M)`. -/
theorem finrank_homℤℝ_eq_finrank_of_free_via_basis
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M := by
  exact finrank_homℤℝ_eq_basis_card (Module.finBasis ℤ M)

/-- **Basis-evaluation equivalence (ℂ variant).** For a ℤ-basis
`b : Fin n → M`, the evaluation map `f ↦ (f ∘ b)` from
`Hom_ℤ(M, ℂ)` to `Fin n → ℂ` is a ℂ-linear equivalence. -/
theorem homℤℂ_basis_evaluation_isLinearEquivℂ
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin n) ℤ M) :
    ∃ _ : (M →ₗ[ℤ] ℂ) ≃ₗ[ℂ] (Fin n → ℂ), True :=
  ⟨(b.constr ℂ).symm, trivial⟩

/-- `dim_ℂ (Fin n → ℂ) = n`. -/
theorem finrank_pi_complex_eq_card (n : ℕ) :
    Module.finrank ℂ (Fin n → ℂ) = n :=
  Module.finrank_fin_fun ℂ

/-- For a fg free ℤ-module `M`, `dim_ℂ Hom_ℤ(M, ℂ) = rank_ℤ M`.
ℂ-analogue of `finrank_homℤℝ_eq_finrank_of_free_via_basis`. -/
theorem finrank_homℤℂ_eq_finrank_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℂ (M →ₗ[ℤ] ℂ) = Module.finrank ℤ M := by
  obtain ⟨e, _⟩ := homℤℂ_basis_evaluation_isLinearEquivℂ (Module.finBasis ℤ M)
  rw [e.finrank_eq, finrank_pi_complex_eq_card]

-- Note: a `Hom_ℤℂ_finrank_eq_of_surjective_ker_rank_zero` general lemma is awkward
-- due to `Module ℤ` typeclass diamonds (Submodule.module vs AddCommGroup.toIntModule
-- on submodules / quotients). The consumer F.2 instead inlines the rank-nullity
-- argument over concrete `smoothOneChainCycleSubmodule X` / `IntegralOneCycle X`,
-- where the instance diamond is locally controlled. The `finrank_homℤℂ_eq_finrank_of_free`
-- helper above is the load-bearing piece F.2 consumes from this file.

end JacobianChallenge.Periods
