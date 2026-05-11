import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Defs

/-!
# Chart-trivialization for cotangent sections

Proves that the local representative of a smooth cotangent section
in the identity chart, evaluated at the constant tangent vector `1`,
is a smooth (`ContDiff`) function on `ℂ`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint
open Bundle

private lemma onePointCx_identityChart_symm_apply' (z : ℂ) :
    (identityChart.symm : ℂ → OnePoint ℂ) z = OnePoint.some z := by
  rw [identityChart]
  simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

/-- The chart at a finite point of OnePoint ℂ is identityChart. -/
private lemma chartAt_onePoint_some (z : ℂ) :
    chartAt ℂ (OnePoint.some z : OnePoint ℂ) = identityChart := by
  rfl

/-
The tangent bundle trivialization at a finite point OnePoint.some z₀,
applied to a tangent vector at another finite point OnePoint.some z,
is the identity on tangent fibers.
-/
private lemma tangent_triv_identity (z₀ z : ℂ)
    (v : TangentSpace (modelWithCornersSelf ℂ ℂ) (OnePoint.some z)) :
    (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) (OnePoint.some z₀)
      (TotalSpace.mk (OnePoint.some z) v)).2 = v := by
  erw [ TangentBundle.trivializationAt_apply ];
  simp +decide [ fderivWithin_univ, chartAt_onePoint_some ];
  erw [ show ( identityChart ∘ identityChart.symm : ℂ → ℂ ) = id from funext fun x => ?_ ];
  · erw [ deriv_id ] ; norm_num;
  · unfold identityChart;
    simp +decide [ Topology.IsOpenEmbedding.toOpenPartialHomeomorph ];
    unfold Function.invFunOn; aesop

/-
The trivial bundle trivialization at any point, applied to a fiber element
at any other point, is the identity.
-/
private lemma trivial_triv_identity (z₀ : ℂ)
    (x : OnePoint ℂ) (v : (Bundle.Trivial (OnePoint ℂ) ℂ) x) :
    (trivializationAt ℂ (Bundle.Trivial (OnePoint ℂ) ℂ) (OnePoint.some z₀)
      (TotalSpace.mk x v)).2 = v := by
  cases x <;> simp_all +decide [ Trivial ]

/-
The trivialized cotangent section value equals the section value for
points in the identity chart domain.
-/
private lemma cotangent_triv_eq_section
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z₀ z : ℂ) :
    (trivializationAt (CotangentModelFiber ℂ)
        (CotangentSpace ℂ (OnePoint ℂ)) (OnePoint.some z₀)
      (TotalSpace.mk' (CotangentModelFiber ℂ)
        (OnePoint.some z) (ω.toFun (OnePoint.some z)))).2
      = ω.toFun (OnePoint.some z) := by
  erw [ Trivialization.continuousLinearMap_apply ];
  ext; simp [Trivialization.continuousLinearMapAt, Trivialization.symmL];
  congr! 1;
  convert tangent_triv_identity z₀ z 1 using 1;
  rw [ Trivialization.symm_apply ];
  all_goals norm_num [ trivializationAt ];
  · congr;
  · simp +decide [ chartAt ];
    simp +decide [ ChartedSpace.chartAt ];
    simp +decide [ identityChart ]

/-
The trivialized section is ContDiffAt at each point.
-/
private lemma trivialized_section_contDiffAt
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z₀ : ℂ) :
    ContDiffAt ℂ ⊤
      (fun z => (trivializationAt (CotangentModelFiber ℂ)
          (CotangentSpace ℂ (OnePoint ℂ)) (OnePoint.some z₀)
        (TotalSpace.mk' (CotangentModelFiber ℂ)
          (OnePoint.some z) (ω.toFun (OnePoint.some z)))).2)
      z₀ := by
  have h_cont_diff : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CotangentModelFiber ℂ)) ⊤ (fun x => (trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ)) (OnePoint.some z₀)
      (TotalSpace.mk' (CotangentModelFiber ℂ) x (ω.toFun x))).2) (OnePoint.some z₀) := by
        convert Bundle.contMDiffAt_section ( OnePoint.some z₀ ) |> fun h => h.mp ω.contMDiff_toFun.contMDiffAt;
  rw [ contMDiffAt_iff ] at h_cont_diff;
  rw [ contDiffWithinAt_iff_contDiffAt ] at h_cont_diff;
  · convert h_cont_diff.2 using 1;
    simp +decide [ extChartAt ];
    rw [ chartAt_onePoint_some ] ; norm_num [ identityChart ];
    exact OnePoint.coe_injective
      ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
          (fun x : ℂ => (x : OnePoint ℂ)) OnePoint.isOpenEmbedding_coe
          (Set.mem_range_self z₀)).symm)
  · exact Filter.univ_mem' fun x => ⟨ x, rfl ⟩

theorem contMDiffSection_localRepr_identityChart_contDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) fun z =>
      ω.toFun (identityChart.symm z)
        (show TangentSpace (modelWithCornersSelf ℂ ℂ)
          (identityChart.symm z) from (1 : ℂ)) := by
  rw [ contDiff_iff_contDiffAt ];
  intro z;
  convert ( trivialized_section_contDiffAt ω z |> ContDiffAt.clm_apply <| contDiffAt_const ) using 1;
  swap;
  exact 1;
  ext; simp +decide [ cotangent_triv_eq_section ] ;
  congr! 2

end JacobianChallenge.HolomorphicForms
