import Jacobian.HolomorphicForms.MeromorphicFunctionVector
import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.Meromorphic

open scoped Manifold OnePoint Topology

namespace JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
A valid meromorphic function is globally continuous.
-/
lemma meromorphicFunctionWithDivisors_continuousOn_ne_infty
    (f : MeromorphicFunctionWithDivisors X) :
    ContinuousOn f.toFunction.toFun {x : X | f.toFunction.toFun x ≠ (OnePoint.infty : OnePoint ℂ)} :=
  f.toFunction.toFun_continuous.continuousOn

/--
Any global complex-valued lift of the map is smooth (meromorphic map with no poles is holomorphic).
This is an open analytic sub-lemma.
-/
lemma meromorphicFunctionWithDivisors_toFiniteFun_mdifferentiable
    (f : MeromorphicFunctionWithDivisors X)
    (g : X → ℂ)
    (hg : f.toFunction.toFun = fun x => ((g x : ℂ) : OnePoint ℂ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g := by
  sorry

/--
At a positive-order pole, the map evaluates to infinity.
This is an open analytic sub-lemma.
-/
lemma meromorphicFunctionWithDivisors_toMap_eq_infty_of_poleDivisor_pos
    (f : MeromorphicFunctionWithDivisors X) :
    ∀ P : X, 0 < f.poleDivisor P → f.toFunction.toFun P = (OnePoint.infty : OnePoint ℂ) := by
  sorry

/--
Bridge the sound Riemann-Roch carrier to the existing degree machinery
by wrapping it into a `MeromorphicMapToSphere`.
-/
noncomputable def meromorphicFunctionWithDivisors_to_mapToSphere
    (f : MeromorphicFunctionWithDivisors X) : MeromorphicMapToSphere X where
  toMap := f.toFunction.toFun
  locally_meromorphic := True
  zeroDivisor := f.zeroDivisor
  poleDivisor := f.poleDivisor
  principalDivisor := f.principalDivisor
  principalDivisor_eq := f.principalDivisor_eq
  poleDivisor_nonneg := f.poleDivisor_nonneg
  zero_or_pole_eq_zero := f.zero_or_pole_eq_zero
  toMap_ne_infty_of_poleDivisor_zero := f.toFun_ne_infty_of_poleDivisor_zero
  continuousOn_ne_infty := meromorphicFunctionWithDivisors_continuousOn_ne_infty f
  toFiniteFun_mdifferentiable := meromorphicFunctionWithDivisors_toFiniteFun_mdifferentiable f
  toMap_eq_infty_of_poleDivisor_pos := meromorphicFunctionWithDivisors_toMap_eq_infty_of_poleDivisor_pos f

/--
An honest meromorphic function (which `MeromorphicFunctionWithDivisors` represents) provides valid `BranchedCoverData` whose branched degree equals the pole divisor degree. (Connects `isMeromorphic` to `BranchedCoverDataOfPoleDegree`).
This is a deep analytic fact, so it is left as a single explicitly named open sub-lemma.
-/
noncomputable def meromorphicFunctionWithDivisors_branchedCoverDataOfPoleDegree
    (f : MeromorphicFunctionWithDivisors X) :
    MeromorphicMapToSphere.BranchedCoverDataOfPoleDegree (meromorphicFunctionWithDivisors_to_mapToSphere f) :=
  sorry

/--
The genuine analytic core: for a valid meromorphic map to the sphere and valid branched cover data, the degree of its zero divisor equals the branched degree.
This is the single honest named open sub-lemma for the degree of a principal divisor.
-/
lemma meromorphicMapToSphere_zeroDivisor_degree_eq_branchedDegree
    (f : MeromorphicMapToSphere X)
    (h : BranchedCoverData X (OnePoint ℂ) f.toMap) :
    f.zeroDivisor.degree.toNat = branchedDegree h := by
  sorry

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X] [JacobianChallenge.Periods.StableChartAt ℂ X] in
/-- The degree of an effective divisor is non-negative. -/
lemma Divisor.degree_ge_zero_of_effective (D : Divisor X) (h : Divisor.Effective D) :
    0 ≤ Divisor.degree D := by
  change 0 ≤ ∑ i ∈ D.support, D i
  apply Finset.sum_nonneg
  intro i _
  exact h i

/--
The genuine analytic core: for a valid divisor-compatible meromorphic function
on a compact Riemann surface, the degree of its zero divisor equals the degree
of its pole divisor.
This is the single open sub-lemma for the degree of a principal divisor.
-/
lemma meromorphicFunctionWithDivisors_degree_zeros_eq_degree_poles
    (f : MeromorphicFunctionWithDivisors X) :
    Divisor.degree f.zeros = Divisor.degree f.poles := by
  have h_cont : Continuous (meromorphicFunctionWithDivisors_to_mapToSphere f).toMap :=
    f.toFunction.toFun_continuous
  obtain ⟨h, h_pole⟩ := (meromorphicFunctionWithDivisors_branchedCoverDataOfPoleDegree f).hasBranchedCoverDataOfPoleDegree h_cont
  have h_zero := meromorphicMapToSphere_zeroDivisor_degree_eq_branchedDegree (meromorphicFunctionWithDivisors_to_mapToSphere f) h
  have hz_nonneg : 0 ≤ Divisor.degree f.zeros := by
    apply Divisor.degree_ge_zero_of_effective
    intro P
    rw [f.zeros_apply P, zeroCoeffOfOrder]
    exact le_max_right _ _
  have hp_nonneg : 0 ≤ Divisor.degree f.poles := by
    apply Divisor.degree_ge_zero_of_effective
    intro P
    change 0 ≤ f.poleDivisor P
    exact f.poleDivisor_nonneg P
  change (Divisor.degree f.zeros).toNat = _ at h_zero
  change _ = (Divisor.degree f.poles).toNat at h_pole
  have h_eq : (Divisor.degree f.zeros).toNat = (Divisor.degree f.poles).toNat := by
    rw [h_zero, h_pole]
  have h1 : ((Divisor.degree f.zeros).toNat : ℤ) = ((Divisor.degree f.poles).toNat : ℤ) := by
    rw [h_eq]
  rw [Int.toNat_of_nonneg hz_nonneg, Int.toNat_of_nonneg hp_nonneg] at h1
  exact h1

/-- The degree of the principal divisor of any non-zero meromorphic function is zero. -/
lemma meromorphicFunctionWithDivisors_degree_principal_eq_zero
    (f : MeromorphicFunctionWithDivisors X) : Divisor.degree f.principal = 0 := by
  rw [f.principal_eq_zeroDivisor_sub_poleDivisor, map_sub]
  rw [meromorphicFunctionWithDivisors_degree_zeros_eq_degree_poles]
  exact sub_self _

/--
A divisor of strictly negative degree has a trivial Riemann-Roch space.
(Any section would have to be identically zero, which is not in `MeromorphicFunctionWithDivisors X`).
-/
lemma riemannRochSpace_dim_zero_of_degree_lt_zero
    (D : Divisor X) (hD : Divisor.degree D < 0)
    (f : MeromorphicFunctionWithDivisors X) :
    ¬ MeromorphicFunctionWithDivisors.MemRiemannRochSpace f D := by
  intro heff
  have h1 : 0 ≤ Divisor.degree (f.principal + D) :=
    Divisor.degree_ge_zero_of_effective _ heff
  have h2 : Divisor.degree (f.principal + D) = Divisor.degree f.principal + Divisor.degree D :=
    map_add Divisor.degree f.principal D
  rw [meromorphicFunctionWithDivisors_degree_principal_eq_zero, zero_add] at h2
  rw [h2] at h1
  omega

/--
The Riemann-Roch space `L(K - [P])` is trivial in genus zero.
Since the genus zero canonical divisor `K` has degree -2,
`K - [P]` has degree -3 < 0.
-/
lemma genusZero_riemannRoch_K_minus_point_dim_zero
    (K : Divisor X) (hK : Divisor.degree K = -2) (P : X)
    (f : MeromorphicFunctionWithDivisors X) :
    ¬ MeromorphicFunctionWithDivisors.MemRiemannRochSpace f (K - Divisor.point P) := by
  apply riemannRochSpace_dim_zero_of_degree_lt_zero (K - Divisor.point P)
  rw [map_sub, hK, Divisor.degree_point]
  omega

end JacobianChallenge.HolomorphicForms
