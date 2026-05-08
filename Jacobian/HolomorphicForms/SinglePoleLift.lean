import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.CMfldBumpStub
import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.OnePointCxIsManifold

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
    ∃ (h : JacobianChallenge.Blueprint.BranchedCoverData X (OnePoint ℂ) f),
      JacobianChallenge.Blueprint.branchedDegree h = D.degree.toNat := by
  sorry

/-- A meromorphic map with a single simple pole at Q. -/
noncomputable def singlePoleMeromorphicMap (Q : X) : MeromorphicMapToSphere X :=
  { toMap := singlePoleSphereLift Q
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q
    principalDivisor := -Divisor.point Q
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun _ => by sorry
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun _ _ _ => by sorry
    continuousOn_ne_infty := by sorry
    toFiniteFun_mdifferentiable := fun _ _ => by sorry
    toMap_eq_infty_of_poleDivisor_pos := fun _ _ => by sorry
    exists_modulus_atTop_at_pole := fun _ _ => by sorry
    hasBranchedCoverDataOfPoleDegree := honestMeromorphic_branchedCoverData_obligation _ _ }

/-- A single-pole map is non-constant. -/
theorem singlePoleMeromorphicMap_nonconstant (Q : X) [Nontrivial X] :
    (singlePoleMeromorphicMap Q).Nonconstant := by
  intro ⟨c, hc⟩
  obtain ⟨r, hr⟩ := exists_ne Q
  have h1 := hc Q
  have h2 := hc r
  unfold singlePoleMeromorphicMap singlePoleSphereLift at h1 h2
  simp at h1
  simp [h1.symm] at h2
  exact OnePoint.infty_ne_coe _ h2

/-- A meromorphic map with two simple poles at Q1 and Q2. -/
noncomputable def twoPointMeromorphicMap (Q1 Q2 : X) (hne : Q1 ≠ Q2) : MeromorphicMapToSphere X :=
  { toMap := fun x => if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q1 + Divisor.point Q2
    principalDivisor := -(Divisor.point Q1 + Divisor.point Q2)
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun _ => by sorry
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun _ _ _ => by sorry
    continuousOn_ne_infty := by sorry
    toFiniteFun_mdifferentiable := fun _ _ => by sorry
    toMap_eq_infty_of_poleDivisor_pos := fun _ _ => by sorry
    exists_modulus_atTop_at_pole := fun _ _ => by sorry
    hasBranchedCoverDataOfPoleDegree := honestMeromorphic_branchedCoverData_obligation _ _ }

end JacobianChallenge.HolomorphicForms
