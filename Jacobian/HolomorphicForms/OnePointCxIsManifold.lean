import Jacobian.HolomorphicForms.OnePointCxChartedSpace

/-!
# Complex manifold structure on `OnePoint ℂ`

This file installs the `IsManifold 𝓘(ℂ,ℂ) ⊤ (OnePoint ℂ)` instance on top
of the two-chart `ChartedSpace ℂ (OnePoint ℂ)` constructed in
`OnePointCxChartedSpace.lean`.

## Bottom-up content

The atlas has two charts (`identityChart`, `inversionChart`); there are
four chart transitions to verify lie in `contDiffGroupoid ⊤ 𝓘(ℂ,ℂ)`:

* `identityChart.symm ≫ₕ identityChart` — identity-on-target.
* `inversionChart.symm ≫ₕ inversionChart` — identity-on-target.
* `identityChart.symm ≫ₕ inversionChart` — `z ↦ z⁻¹` on `ℂ \ {0}`,
  smooth by `contDiffOn_inv`.
* `inversionChart.symm ≫ₕ identityChart` — `z ↦ z⁻¹` on `ℂ \ {0}`,
  smooth by `contDiffOn_inv`.

Read through the trivial model `𝓘(ℂ,ℂ)` (which is the identity), the
non-trivial transitions reduce to `ContDiffOn ℂ ⊤ Inv.inv ({0}ᶜ : Set ℂ)`.
-/

open scoped Topology OnePoint Manifold
open Set Filter OnePoint

namespace JacobianChallenge.HolomorphicForms

/-! ### Convenience equalities for the chart maps

These reduce the chart functions to their underlying expressions
(`(↑·) : ℂ → OnePoint ℂ` and `invFwd`/`invBwd`). They are private to this
file. -/

private lemma identityChart_symm_apply (z : ℂ) :
    (identityChart.symm : ℂ → OnePoint ℂ) z = ↑z := by
  simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma identityChart_apply_coe (z : ℂ) :
    (identityChart : OnePoint ℂ → ℂ) ↑z = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

private lemma identityChart_source :
    identityChart.source = (range ((↑) : ℂ → OnePoint ℂ)) := by
  simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma identityChart_symm_source :
    identityChart.symm.source = (univ : Set ℂ) := by
  simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma identityChart_target :
    identityChart.target = (univ : Set ℂ) := by
  simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma inversionChart_symm_apply (w : ℂ) :
    (inversionChart.symm : ℂ → OnePoint ℂ) w = invBwd w := rfl

private lemma inversionChart_apply (x : OnePoint ℂ) :
    (inversionChart : OnePoint ℂ → ℂ) x = invFwd x := rfl

private lemma inversionChart_source_eq :
    inversionChart.source = ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ)) := rfl

private lemma inversionChart_target_eq :
    inversionChart.target = (univ : Set ℂ) := rfl

/-! ### The two non-trivial transition functions -/

/-- The composition `identityChart.symm ≫ₕ inversionChart` agrees with
`Inv.inv` on its source. -/
private lemma identityChart_trans_inversionChart_eqOn :
    EqOn ((identityChart.symm ≫ₕ inversionChart : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      Inv.inv (identityChart.symm ≫ₕ inversionChart).source := by
  intro z _
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    identityChart_symm_apply, inversionChart_apply, invFwd_coe]

/-- The source of `identityChart.symm ≫ₕ inversionChart` is the punctured
plane `{(0 : ℂ)}ᶜ`. -/
private lemma identityChart_trans_inversionChart_source :
    (identityChart.symm ≫ₕ inversionChart).source = ({(0 : ℂ)}ᶜ : Set ℂ) := by
  rw [OpenPartialHomeomorph.trans_source, identityChart_symm_source]
  ext z
  simp only [univ_inter, mem_preimage, mem_compl_iff, mem_singleton_iff,
    identityChart_symm_apply, inversionChart_source_eq]
  exact ⟨fun h h0 => h (by rw [h0]), fun h h' => h (OnePoint.coe_injective h')⟩

/-- The composition `inversionChart.symm ≫ₕ identityChart` agrees with
`Inv.inv` on its source. -/
private lemma inversionChart_trans_identityChart_eqOn :
    EqOn ((inversionChart.symm ≫ₕ identityChart : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      Inv.inv (inversionChart.symm ≫ₕ identityChart).source := by
  intro w hw
  rw [OpenPartialHomeomorph.trans_source] at hw
  obtain ⟨_hw1, hw2⟩ := hw
  -- hw2 : inversionChart.symm w ∈ identityChart.source = range coe
  have hw_ne : w ≠ 0 := by
    intro hw0
    rw [mem_preimage, inversionChart_symm_apply, hw0, invBwd_zero,
      identityChart_source] at hw2
    exact OnePoint.infty_notMem_range_coe hw2
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    inversionChart_symm_apply, invBwd_ne_zero hw_ne, identityChart_apply_coe]

/-- The source of `inversionChart.symm ≫ₕ identityChart` is the punctured
plane `{(0 : ℂ)}ᶜ`. -/
private lemma inversionChart_trans_identityChart_source :
    (inversionChart.symm ≫ₕ identityChart).source = ({(0 : ℂ)}ᶜ : Set ℂ) := by
  rw [OpenPartialHomeomorph.trans_source]
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff,
    inversionChart_symm_apply, identityChart_source]
  constructor
  · rintro ⟨_, hw⟩ hw0
    rw [hw0, invBwd_zero] at hw
    exact OnePoint.infty_notMem_range_coe hw
  · intro hw
    refine ⟨?_, ?_⟩
    · -- source of inversionChart.symm = inversionChart.target = univ
      change w ∈ inversionChart.target
      rw [inversionChart_target_eq]; trivial
    · rw [invBwd_ne_zero hw]
      exact mem_range_self _

/-! ### `ContDiffOn` of the non-trivial transitions -/

/-- The transition `identityChart.symm ≫ₕ inversionChart` is `C^∞`. -/
private lemma identityChart_trans_inversionChart_contDiffOn :
    ContDiffOn ℂ ⊤
      ((modelWithCornersSelf ℂ ℂ) ∘ (identityChart.symm ≫ₕ inversionChart) ∘
        (modelWithCornersSelf ℂ ℂ).symm)
      ((modelWithCornersSelf ℂ ℂ).symm ⁻¹' (identityChart.symm ≫ₕ inversionChart).source ∩
        range (modelWithCornersSelf ℂ ℂ)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  rw [identityChart_trans_inversionChart_source]
  refine ContDiffOn.congr (contDiffOn_inv ℂ) ?_
  intro z hz
  have heq := identityChart_trans_inversionChart_eqOn (x := z)
  rw [identityChart_trans_inversionChart_source] at heq
  exact heq hz

/-- The transition `inversionChart.symm ≫ₕ identityChart` is `C^∞`. -/
private lemma inversionChart_trans_identityChart_contDiffOn :
    ContDiffOn ℂ ⊤
      ((modelWithCornersSelf ℂ ℂ) ∘ (inversionChart.symm ≫ₕ identityChart) ∘
        (modelWithCornersSelf ℂ ℂ).symm)
      ((modelWithCornersSelf ℂ ℂ).symm ⁻¹' (inversionChart.symm ≫ₕ identityChart).source ∩
        range (modelWithCornersSelf ℂ ℂ)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  rw [inversionChart_trans_identityChart_source]
  refine ContDiffOn.congr (contDiffOn_inv ℂ) ?_
  intro w hw
  have heq := inversionChart_trans_identityChart_eqOn (x := w)
  rw [inversionChart_trans_identityChart_source] at heq
  exact heq hw

/-! ### The diagonal transitions

For the diagonal cases `e = e'` the composition `e.symm ≫ₕ e` is the
identity on the target of `e`. We discharge each via direct computation. -/

/-- The transition `identityChart.symm ≫ₕ identityChart` is `C^∞`. -/
private lemma identityChart_diag_contDiffOn :
    ContDiffOn ℂ ⊤
      ((modelWithCornersSelf ℂ ℂ) ∘ (identityChart.symm ≫ₕ identityChart) ∘
        (modelWithCornersSelf ℂ ℂ).symm)
      ((modelWithCornersSelf ℂ ℂ).symm ⁻¹'
          (identityChart.symm ≫ₕ identityChart).source ∩
        range (modelWithCornersSelf ℂ ℂ)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  refine ContDiffOn.congr (s := (identityChart.symm ≫ₕ identityChart).source)
    contDiffOn_id ?_
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  obtain ⟨_hz1, _hz2⟩ := hz
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    identityChart_symm_apply, identityChart_apply_coe]
  rfl

/-- The transition `inversionChart.symm ≫ₕ inversionChart` is `C^∞`. -/
private lemma inversionChart_diag_contDiffOn :
    ContDiffOn ℂ ⊤
      ((modelWithCornersSelf ℂ ℂ) ∘ (inversionChart.symm ≫ₕ inversionChart) ∘
        (modelWithCornersSelf ℂ ℂ).symm)
      ((modelWithCornersSelf ℂ ℂ).symm ⁻¹'
          (inversionChart.symm ≫ₕ inversionChart).source ∩
        range (modelWithCornersSelf ℂ ℂ)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  refine ContDiffOn.congr (s := (inversionChart.symm ≫ₕ inversionChart).source)
    contDiffOn_id ?_
  intro w _hw
  -- The composition equals `invFwd ∘ invBwd`, and `invFwd_invBwd` says it's `id` for all `w`.
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    inversionChart_symm_apply, inversionChart_apply, invFwd_invBwd]
  rfl

/-! ### The `IsManifold` instance -/

/-- `OnePoint ℂ` (= ℂℙ¹) is a complex manifold with the two-chart
atlas {identityChart, inversionChart} from `OnePointCxChartedSpace`.

Bottom-up content: chart transitions are `z ↦ z⁻¹` on `ℂ \ {0}`, which
is C^∞ (in fact analytic) by `contDiffOn_inv ℂ`. -/
noncomputable instance : IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with rfl | he
  · rcases he' with rfl | he'
    · exact identityChart_diag_contDiffOn
    · rcases he' with rfl
      exact identityChart_trans_inversionChart_contDiffOn
  · rcases he with rfl
    rcases he' with rfl | he'
    · exact inversionChart_trans_identityChart_contDiffOn
    · rcases he' with rfl
      exact inversionChart_diag_contDiffOn

end JacobianChallenge.HolomorphicForms
