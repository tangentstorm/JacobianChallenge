import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Complex charted space structure on `OnePoint ℂ`

This file constructs a `ChartedSpace ℂ (OnePoint ℂ)` instance via a two-chart atlas:

* **Identity chart** (`identityChart`): the open embedding `(↑) : ℂ → OnePoint ℂ`
  packaged as an `OpenPartialHomeomorph` with source `{∞}ᶜ` and target `Set.univ`.

* **Inversion chart** (`inversionChart`): forward map `∞ ↦ 0`, `↑z ↦ z⁻¹`;
  inverse map `0 ↦ ∞`, `w ↦ ↑(w⁻¹)` for `w ≠ 0`.  Source `{↑0}ᶜ`, target `Set.univ`.

The two chart sources cover `OnePoint ℂ`: every finite `↑z` is in `identityChart.source`,
and `∞` is in `inversionChart.source`.
-/

open scoped Topology OnePoint
open Set Filter OnePoint

namespace JacobianChallenge.HolomorphicForms

/-! ### Forward and inverse maps for the inversion chart -/

/-- Forward map of the inversion chart: `∞ ↦ 0`, `↑z ↦ z⁻¹`. -/
noncomputable def invFwd : OnePoint ℂ → ℂ :=
  fun x => x.elim 0 (·⁻¹)

/-- Inverse map of the inversion chart: `0 ↦ ∞`, `w ↦ ↑(w⁻¹)` for `w ≠ 0`. -/
noncomputable def invBwd : ℂ → OnePoint ℂ :=
  fun w => if w = 0 then ∞ else ↑(w⁻¹)

/-! ### Basic properties of the forward/inverse maps -/

@[simp] lemma invFwd_infty : invFwd ∞ = 0 := by unfold invFwd; rfl

@[simp] lemma invFwd_coe (z : ℂ) : invFwd ↑z = z⁻¹ := by unfold invFwd; rfl

@[simp] lemma invBwd_zero : invBwd 0 = ∞ := by unfold invBwd; simp

@[simp] lemma invBwd_ne_zero {w : ℂ} (hw : w ≠ 0) : invBwd w = ↑(w⁻¹) := by
  unfold invBwd; simp [hw]

lemma invBwd_invFwd {x : OnePoint ℂ} (hx : x ∈ ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ))) :
    invBwd (invFwd x) = x := by
  cases x with
  | infty => simp [invFwd, invBwd]
  | coe z =>
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    have hz : z ≠ 0 := fun h => hx (congrArg _ h)
    simp [inv_ne_zero hz]

lemma invFwd_invBwd (w : ℂ) : invFwd (invBwd w) = w := by
  by_cases hw : w = 0
  · subst hw; simp [invBwd, invFwd]
  · simp [hw, inv_inv]

lemma invBwd_mem_source (w : ℂ) :
    invBwd w ∈ ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ)) := by
  unfold invBwd
  by_cases hw : w = 0
  · simp [hw]
  · simp [hw, inv_ne_zero hw]

/-! ### Continuity of the forward map -/

/-- `Inv.inv` tends to `0` along `coclosedCompact ℂ`. -/
lemma tendsto_inv_zero_coclosedCompact :
    Tendsto Inv.inv (coclosedCompact ℂ) (nhds 0) := by
  rw [coclosedCompact_eq_cocompact]
  rw [← Metric.cobounded_eq_cocompact]
  exact Filter.tendsto_inv₀_cobounded

/-
The forward map `invFwd` is continuous on `{↑0}ᶜ`.
-/
lemma continuousOn_invFwd :
    ContinuousOn invFwd ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ)) := by
  intro x hx;
  cases x using OnePoint.rec <;> simp_all +decide [ ContinuousWithinAt ];
  · have h_cont : Tendsto invFwd (nhds ∞) (nhds 0) := by
      rw [ OnePoint.tendsto_nhds_infty' ];
      exact ⟨ tendsto_pure_nhds _ _, by simpa [ Function.comp_def ] using tendsto_inv_zero_coclosedCompact ⟩;
    exact h_cont.mono_left inf_le_left;
  · convert Tendsto.comp ( show Tendsto ( fun z : ℂ => z⁻¹ ) ( 𝓝 _ ) ( 𝓝 _ ) from ContinuousAt.inv₀ ( continuousAt_id ) hx ) _ using 2;
    rotate_left;
    exact fun x => x.elim 0 ( fun z => z );
    · refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
      rw [ OnePoint.nhds_coe_eq ];
      exact Filter.tendsto_map;
    · exact funext fun x => by cases x <;> simp +decide [ invFwd ] ;

/-! ### Continuity of the inverse map -/

/-
The inverse map `invBwd` is continuous on `Set.univ`.
-/
lemma continuousOn_invBwd : ContinuousOn invBwd univ := by
  intro w hw;
  by_cases hw : w = 0 <;> simp_all +decide [ ContinuousWithinAt ];
  · convert OnePoint.tendsto_nhds_infty.mpr _;
    rotate_left;
    exact ℂ;
    exact inferInstance;
    exact String.Pos.Raw;
    exact fun _ => 0;
    exact ⊤;
    · exact fun s hs => ⟨ by aesop, ∅, isClosed_empty, isCompact_empty, fun x hx => by aesop ⟩;
    · simp +decide [ Filter.tendsto_def ];
      intro s hs; rw [ OnePoint.nhds_infty_eq ] at hs; simp_all +decide [ Filter.mem_map, Set.preimage ] ;
      rw [ mem_cocompact ] at hs;
      obtain ⟨ ⟨ t, ht₁, ht₂ ⟩, ht₃ ⟩ := hs;
      rw [ Metric.mem_nhds_iff ];
      obtain ⟨ M, hM ⟩ := ht₁.isBounded.exists_pos_norm_le;
      refine' ⟨ M⁻¹, inv_pos.mpr hM.1, fun x hx => _ ⟩ ; by_cases hx' : x = 0 <;> simp_all +decide [ Set.subset_def ];
      exact ht₂ _ fun h => by have := hM.2 _ h; rw [ norm_inv ] at this; nlinarith [ norm_pos_iff.mpr hx', mul_inv_cancel₀ ( ne_of_gt hM.1 ), mul_inv_cancel₀ ( ne_of_gt ( norm_pos_iff.mpr hx' ) ) ] ;
  · refine' Filter.Tendsto.congr' _ _;
    exact fun z => OnePoint.some ( z⁻¹ );
    · filter_upwards [ IsOpen.mem_nhds isOpen_ne hw ] with z hz using by unfold invBwd; aesop;
    · exact OnePoint.continuous_coe.continuousAt.comp ( continuousAt_id.inv₀ hw )

/-! ### The inversion chart -/

/-- Inversion chart for `OnePoint ℂ`: source `{(↑0 : OnePoint ℂ)}ᶜ`,
    target `Set.univ`, forward map `∞ ↦ 0` and `↑z ↦ z⁻¹`, inverse
    map `0 ↦ ∞` and `w ↦ ↑(w⁻¹)` for `w ≠ 0`. -/
noncomputable def inversionChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ where
  toPartialEquiv := {
    toFun := invFwd
    invFun := invBwd
    source := {(↑(0 : ℂ))}ᶜ
    target := univ
    map_source' := fun _ _ => mem_univ _
    map_target' := fun _ _ => invBwd_mem_source _
    left_inv' := fun _ hx => invBwd_invFwd hx
    right_inv' := fun w _ => invFwd_invBwd w
  }
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_invFwd
  continuousOn_invFun := continuousOn_invBwd

/-! ### The identity chart -/

/-- Identity chart for `OnePoint ℂ`: open embedding `(↑) : ℂ → OnePoint ℂ`
    packaged as a partial homeomorphism with source `{∞}ᶜ` and target
    `Set.univ`. -/
noncomputable def identityChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (isOpenEmbedding_coe.toOpenPartialHomeomorph (↑·)).symm

/-! ### The `ChartedSpace` instance -/

/-- The atlas {identityChart, inversionChart} covers `OnePoint ℂ` and gives
    `ChartedSpace ℂ`. -/
noncomputable instance : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {identityChart, inversionChart}
  chartAt := fun x => x.elim inversionChart (fun _ => identityChart)
  mem_chart_source := by
    intro x
    cases x with
    | infty =>
      dsimp [OnePoint.elim, Option.elim]
      simp [inversionChart]
    | coe z =>
      dsimp [OnePoint.elim, Option.elim]
      simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]
  chart_mem_atlas := by
    intro x
    cases x with
    | infty =>
      dsimp [OnePoint.elim, Option.elim]
      exact Or.inr rfl
    | coe z =>
      dsimp [OnePoint.elim, Option.elim]
      exact Or.inl rfl

end JacobianChallenge.HolomorphicForms
