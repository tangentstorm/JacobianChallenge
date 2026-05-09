import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.CMfldBumpStub
import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open Set
open Classical

variable {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- f(x) = cMfldBump(Q,x) / ((chartAt ℂ Q).toFun(x) - φ(Q))  on chart, 0 off,
    with f(Q) := ∞. -/
noncomputable def singlePoleSphereLift (Q : X) (x : X) : OnePoint ℂ :=
  if x = Q then
    OnePoint.infty
  else if x ∈ (chartAt ℂ Q).source then
    let φ := chartAt ℂ Q
    let val : ℂ := (cMfldBump Q x : ℝ) / (φ x - φ Q)
    (val : OnePoint ℂ)
  else
    ((0 : ℂ) : OnePoint ℂ)

/-- Local complex-valued lift for the single-pole function, used in the
modulus-divergence axiom. -/
noncomputable def singlePoleLocalLift (Q : X) (x : X) : ℂ :=
  if x ∈ (chartAt ℂ Q).source then
    if x = Q then (0 : ℂ) else
    (cMfldBump Q x : ℝ) / (chartAt ℂ Q x - chartAt ℂ Q Q)
  else
    0

/-- Shared obligation for BranchedCoverData, permitted to be sorry.
/-! TODO: Discharge via Riemann-Roch and algebraic degree theory. -/ -/
lemma honestMeromorphic_branchedCoverData_obligation
    (f : X → OnePoint ℂ) (D : Divisor X) :
    Continuous f →
    ∃ (h : BranchedCoverData X (OnePoint ℂ) f),
      branchedDegree h = D.degree.toNat := by
  sorry

/-- A meromorphic map with a single simple pole at Q. -/
noncomputable def singlePoleMeromorphicMap (Q : X) : MeromorphicMapToSphere X :=
  { toMap := singlePoleSphereLift Q
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q
    principalDivisor := -Divisor.point Q
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun x => by
      classical
      exact Divisor.effective_point Q x
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun x hx => by
      have hne : x ≠ Q := by
        intro h
        rw [h, Divisor.point_apply_self] at hx
        exact zero_ne_one hx.symm
      unfold singlePoleSphereLift
      split_ifs with heq hsrc
      · contradiction
      · exact OnePoint.coe_ne_infty _
      · exact OnePoint.coe_ne_infty _
    continuousOn_ne_infty := by sorry
    toFiniteFun_mdifferentiable := fun _ _ => by sorry
    toMap_eq_infty_of_poleDivisor_pos := fun x hx => by
      have heq : x = Q := by
        by_contra hne
        rw [Divisor.point_apply_ne hne] at hx
        exact (lt_irrefl _) hx
      unfold singlePoleSphereLift
      rw [if_pos heq]
    exists_modulus_atTop_at_pole := fun _ _ => by sorry
    hasBranchedCoverDataOfPoleDegree := honestMeromorphic_branchedCoverData_obligation _ _ }

/-- A single-pole map is non-constant. -/
theorem singlePoleMeromorphicMap_nonconstant (Q : X) [Nontrivial X] :
    (singlePoleMeromorphicMap Q).Nonconstant := by
  intro ⟨c, hc⟩
  obtain ⟨r, hr⟩ := exists_ne Q
  have h1 := hc Q
  have h2 := hc r
  unfold singlePoleMeromorphicMap at h1 h2
  simp [singlePoleSphereLift] at h1
  subst h1
  simp [singlePoleSphereLift, hr] at h2
  split_ifs at h2
  · exact OnePoint.coe_ne_infty _ h2
  · exact OnePoint.coe_ne_infty _ h2

/-- A meromorphic map with two simple poles at Q1 and Q2. -/
noncomputable def twoPointMeromorphicMap (Q1 Q2 : X) (hne : Q1 ≠ Q2) : MeromorphicMapToSphere X :=
  { toMap := fun x => if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q1 + Divisor.point Q2
    principalDivisor := -(Divisor.point Q1 + Divisor.point Q2)
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun x => by
      classical
      apply add_nonneg
      · exact Divisor.effective_point Q1 x
      · exact Divisor.effective_point Q2 x
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun x hx => by
      have hne1 : x ≠ Q1 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q1 + (Divisor.point Q2) Q1 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q2 Q1
        linarith
      have hne2 : x ≠ Q2 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q2 + (Divisor.point Q2) Q2 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q1 Q2
        linarith
      split_ifs with heq
      · rcases heq with heq1 | heq2
        · contradiction
        · contradiction
      · exact OnePoint.coe_ne_infty _
    continuousOn_ne_infty := by sorry
    toFiniteFun_mdifferentiable := fun _ _ => by sorry
    toMap_eq_infty_of_poleDivisor_pos := fun x hx => by
      have heq : x = Q1 ∨ x = Q2 := by
        by_contra h_nor
        push_neg at h_nor
        have hx' : 0 < (Divisor.point Q1) x + (Divisor.point Q2) x := hx
        have hzero : (Divisor.point Q1) x + (Divisor.point Q2) x = 0 := by
          rw [Divisor.point_apply_ne h_nor.1, Divisor.point_apply_ne h_nor.2, add_zero]
        rw [hzero] at hx'
        exact lt_irrefl _ hx'
      rw [if_pos heq]
    exists_modulus_atTop_at_pole := fun _ _ => by sorry
    hasBranchedCoverDataOfPoleDegree := honestMeromorphic_branchedCoverData_obligation _ _ }

/-- A two-pole map is non-constant. -/
theorem twoPointMeromorphicMap_nonconstant [Nonempty X] (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    (twoPointMeromorphicMap Q1 Q2 hne).Nonconstant := by
  intro ⟨c, hc⟩
  have h1 := hc Q1
  -- I need a point that is not a pole.
  obtain ⟨r, hr1, hr2⟩ := exists_distinct_from_pair_of_chartedSpaceComplex (X := X) Q1 Q2
  have hr := hc r
  unfold twoPointMeromorphicMap at h1 hr
  simp at h1
  subst h1
  simp [hr1, hr2] at hr

end JacobianChallenge.HolomorphicForms
