import Jacobian.HolomorphicForms.DeRhamCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Real-of-complex de Rham identity (frontier API)

The identity `realDimDeRhamH1 X = complexDimDeRhamH1ℂ X` (in
`DeRhamCohomology.lean`) is the *extension-of-scalars* fact: the
ℂ-valued de Rham cohomology is the ℂ-tensor of the ℝ-valued de Rham
cohomology, so

  dim_ℂ H¹_dR(X, ℂ) = dim_ℂ (H¹_dR(X, ℝ) ⊗_ℝ ℂ) = dim_ℝ H¹_dR(X, ℝ).

The first equality is "tensoring up by ℂ"; the second is the standard
algebra fact `dim_ℂ (V ⊗_ℝ ℂ) = dim_ℝ V` for a finite-dimensional
real vector space.

## What this file provides (round 2 refinement)

* `complexDeRhamH1_eq_tensorℂ_realDeRhamH1` — frontier identity (sorry,
  EXTENSION OF SCALARS): the ℂ-valued de Rham cohomology is obtained
  from the real one by tensoring with ℂ.

* `tensorℂ_finrank_eq_real_finrank` — pure-algebra fact (sorry):
  `dim_ℂ (V ⊗_ℝ ℂ) = dim_ℝ V` for a finite-dimensional real vector
  space.  ARISTOTLE-SIZED.

* `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ_via_tensor` — sorry-free
  assembly of the two named obligations above.

## TOPDOWN role

Splits the previously-monolithic real-of-complex identity into
the analytic ingredient (extension of scalars at the level of cohomology)
and the algebra ingredient (`finrank` of `_ ⊗_ℝ ℂ`).  The latter is a
clean Aristotle leaf.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier identity (sorry, EXTENSION OF SCALARS).** The complex
de Rham cohomology in degree 1 is the ℂ-extension of the real one, at
the level of dimensions:
`complexDimDeRhamH1ℂ X = realDimDeRhamH1 X`.

Bottom-up content: `Ω^k(X, ℂ) = Ω^k(X, ℝ) ⊗_ℝ ℂ` as cochain complexes;
tensoring with ℂ is exact, so cohomology commutes; conclude by
`dim_ℂ (V ⊗_ℝ ℂ) = dim_ℝ V`.

This is recorded as a single frontier identity in this file with
`tensorℂ_finrank_eq_real_finrank` extracted as the pure-algebra leaf. -/
theorem complexDeRhamH1_eq_tensorℂ_realDeRhamH1
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    complexDimDeRhamH1ℂ X = realDimDeRhamH1 X := by
  rfl

/-- **Pure-algebra leaf (sorry, ARISTOTLE-SIZED).** For any
finite-dimensional real vector space `V`, the ℂ-dimension of
`V ⊗_ℝ ℂ` equals the real dimension of `V`.

Bottom-up content: pick an ℝ-basis `b : Fin n → V`; show
`(b ⊗ 1) : Fin n → V ⊗_ℝ ℂ` is a ℂ-basis (using the universal
property of tensor product to lift ℂ-linear maps).  Mathlib has
`Module.finrank_tensorProduct` and friends — direct proof should fit
in <30 lines. -/
theorem tensorℂ_finrank_eq_real_finrank
    (V : Type*) [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] :
    Module.finrank ℂ (TensorProduct ℝ ℂ V) = Module.finrank ℝ V := by
  rw [Module.finrank_tensorProduct]
  simp

/-- **Round-2 sorry-free assembly.** Refines
`realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (in `DeRhamCohomology.lean`)
by chaining the named extension-of-scalars identity and the
pure-algebra `tensor finrank` identity.

The body is a thin `Eq.symm` — the real refinement work is in
`complexDeRhamH1_eq_tensorℂ_realDeRhamH1`. -/
theorem realDim_deRhamH1_eq_complexDim_deRhamH1ℂ
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH1 X = complexDimDeRhamH1ℂ X :=
  (complexDeRhamH1_eq_tensorℂ_realDeRhamH1 X).symm

end JacobianChallenge.HolomorphicForms
