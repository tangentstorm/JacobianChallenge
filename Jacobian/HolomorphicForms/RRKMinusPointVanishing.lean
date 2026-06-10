import Jacobian.HolomorphicForms.MeromorphicFunctionVector
import Jacobian.HolomorphicForms.Divisor

open scoped Manifold OnePoint Topology

namespace JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-- The degree of the principal divisor of any meromorphic function is zero. -/
lemma meromorphicFunction_degree_principal_eq_zero
    (f : MeromorphicFunctionType X) : Divisor.degree f.principal = 0 := by
  simp [MeromorphicFunctionType.principal, MeromorphicFunctionType.zeros, MeromorphicFunctionType.poles]

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X] [JacobianChallenge.Periods.StableChartAt ℂ X] in
/-- The degree of an effective divisor is non-negative. -/
lemma Divisor.degree_ge_zero_of_effective (D : Divisor X) (h : Divisor.Effective D) :
    0 ≤ Divisor.degree D := by
  change 0 ≤ ∑ i ∈ D.support, D i
  apply Finset.sum_nonneg
  intro i _
  exact h i

/--
A divisor of strictly negative degree has a trivial Riemann-Roch space.
-/
lemma riemannRochSpace_dim_zero_of_degree_lt_zero
    (D : Divisor X) (hD : Divisor.degree D < 0)
    (f : MeromorphicFunctionType X) (hf : MeromorphicFunctionType.MemRiemannRochSpace f D) :
    f = 0 := by
  rcases hf with rfl | heff
  · rfl
  · have h1 : 0 ≤ Divisor.degree (f.principal + D) :=
      Divisor.degree_ge_zero_of_effective _ heff
    have h2 : Divisor.degree (f.principal + D) = Divisor.degree f.principal + Divisor.degree D :=
      map_add Divisor.degree f.principal D
    rw [meromorphicFunction_degree_principal_eq_zero, zero_add] at h2
    rw [h2] at h1
    omega

/--
The Riemann-Roch space `L(K - [P])` is trivial in genus zero.
Since the genus zero canonical divisor `K` has degree -2,
`K - [P]` has degree -3 < 0.
-/
lemma genusZero_riemannRoch_K_minus_point_dim_zero
    (K : Divisor X) (hK : Divisor.degree K = -2) (P : X)
    (f : MeromorphicFunctionType X)
    (hf : MeromorphicFunctionType.MemRiemannRochSpace f (K - Divisor.point P)) :
    f = 0 := by
  apply riemannRochSpace_dim_zero_of_degree_lt_zero (K - Divisor.point P) _ f hf
  rw [map_sub, hK, Divisor.degree_point]
  omega

end JacobianChallenge.HolomorphicForms
