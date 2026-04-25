import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.TransitionContDiffOn
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# `IsManifold` instance on the complex torus

Queue B sibling. Combines the `ChartedSpace` instance and the
`ContDiffOn ℂ ω` chart-transition lemma into a manifold structure.

The `HasGroupoid` obligation reduces, via
`mem_groupoid_of_pregroupoid` and the `modelWithCornersSelf`
simplifications, to two `ContDiffOn ℂ ω` checks for chart
transitions in both directions. Both are direct applications of
`TransitionContDiffOn.contDiffOn_localSection_mk` after exposing
`chartAtPoint`'s `(δ, hδpos, hr_lt, hiso)` data via
`Classical.choose_spec`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- `HasGroupoid` instance for the complex torus over `contDiffGroupoid ω`.
The substantive content is in `contDiffOn_localSection_mk`. -/
noncomputable instance complexTorusHasGroupoid (Λ : FullComplexLattice V) :
    HasGroupoid (quotient V Λ)
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℂ V)) := by
  refine ⟨?_⟩
  rintro e e' ⟨q1, rfl⟩ ⟨q2, rfl⟩
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  -- Now: contDiffPregroupoid.property f f.source ∧ ... f.symm f.target
  -- where f = chartAtPoint Λ q1.symm.trans (chartAtPoint Λ q2)
  -- For I = modelWithCornersSelf, I = id and I.symm = id, so
  -- property f s simplifies to ContDiffOn 𝕜 n f s.
  set v₁ := Function.surjInv (mk_surjective V Λ) q1 with v₁_def
  set v₂ := Function.surjInv (mk_surjective V Λ) q2 with v₂_def
  set data := exists_pos_le_norm_of_discreteTopology (V := V) Λ.subgroup with data_def
  obtain ⟨δpos, hiso⟩ := data.choose_spec
  set δ : ℝ := data.choose with δ_def
  have hδpos : 0 < δ := δpos
  have hr_lt : (δ : ℝ) / 4 < δ / 2 := by linarith
  refine ⟨?_, ?_⟩
  · -- toFun direction:
    -- `(chartAtPoint Λ q1).symm.trans (chartAtPoint Λ q2)`'s toFun
    -- on its source = `localSection Λ v₂ (δ/4) ∘ mk V Λ` on
    -- `Metric.ball v₁ (δ/4) ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ (δ/4))`.
    show ContDiffOn ℂ (⊤ : WithTop ℕ∞)
        (modelWithCornersSelf ℂ V ∘ _ ∘ (modelWithCornersSelf ℂ V).symm) _
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    exact contDiffOn_localSection_mk Λ v₁ v₂ hδpos hr_lt hiso
  · -- invFun direction (transition's `symm` toFun on its target):
    -- `localSection Λ v₁ (δ/4) ∘ mk V Λ` on
    -- `Metric.ball v₂ (δ/4) ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₁ (δ/4))`.
    show ContDiffOn ℂ (⊤ : WithTop ℕ∞)
        (modelWithCornersSelf ℂ V ∘ _ ∘ (modelWithCornersSelf ℂ V).symm) _
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    exact contDiffOn_localSection_mk Λ v₂ v₁ hδpos hr_lt hiso

/-- The complex torus is an analytic manifold modeled on the ambient
finite-dimensional complex vector space. -/
noncomputable instance complexTorusIsManifold (Λ : FullComplexLattice V) :
    IsManifold (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (quotient V Λ) where

end JacobianChallenge.ComplexTorus
