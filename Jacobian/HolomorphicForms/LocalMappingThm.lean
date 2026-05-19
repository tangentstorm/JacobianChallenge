import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.Blueprint.Sec02.WeightedFiberCardConst
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Cases

/-! # Local Mapping Theorem for ℂ → ℂ Analytic Functions

Core analytic content for the k-fold fiber counting: if a ℂ → ℂ
function is locally conjugate to z ↦ z^k, then nearby nonzero fibers
have exactly k simple preimages. -/

namespace JacobianChallenge.HolomorphicForms.LocalMappingThm

open scoped Manifold Topology
open Set Filter Complex

/-- The polynomial z^k - w has exactly k distinct roots in ℂ for w ≠ 0. -/
theorem pow_sub_const_roots_card {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : w ≠ 0) :
    (Polynomial.X ^ k - Polynomial.C w : Polynomial ℂ).roots.toFinset.card = k := by
  have h_distinct : Multiset.Nodup (Polynomial.roots (Polynomial.X ^ k - Polynomial.C w)) := by
    refine' Polynomial.nodup_roots _
    exact Polynomial.separable_X_pow_sub_C w (by aesop) (by aesop)
  rw [Multiset.toFinset_card_of_nodup h_distinct]
  have h_card : Multiset.card (Polynomial.roots (Polynomial.X ^ k - Polynomial.C w)) =
    Polynomial.natDegree (Polynomial.X ^ k - Polynomial.C w) := by
      exact IsAlgClosed.card_roots_eq_natDegree
  rw [h_card, Polynomial.natDegree_X_pow_sub_C]

/-- Each root of z^k - w has analyticOrderNatAt = 1. -/
theorem pow_sub_const_simple_root {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : w ≠ 0)
    {ζ : ℂ} (hζ : ζ ^ k = w) :
    analyticOrderNatAt (fun z => z ^ k - w) ζ = 1 := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt]
  split_ifs <;> simp_all +decide [sub_eq_iff_eq_add]
  · have h_inf_roots : Set.Infinite {z : ℂ | z ^ k = w} := by
      rw [Metric.eventually_nhds_iff] at *
      obtain ⟨ε, ε_pos, hε⟩ := ‹_›
      have h_inf_roots : Set.Infinite (Set.image (fun t : ℝ => ζ + t * Complex.I)
          (Set.Ioo 0 ε)) := by
        exact Set.Infinite.image (fun t => by simp +decide [Complex.ext_iff])
          (Set.Ioo_infinite ε_pos)
      exact h_inf_roots.mono <| Set.image_subset_iff.mpr fun t ht =>
        hε <| by simpa [abs_of_pos ht.1] using ht.2
    have h_poly_roots : Set.Finite {z : ℂ | z ^ k = w} := by
      refine' Set.Finite.subset (Set.toFinite (Multiset.toFinset
        (Polynomial.roots (Polynomial.X ^ k - Polynomial.C w)))) _
      intro z hz; simp_all +decide [sub_eq_iff_eq_add]
      exact ne_of_apply_ne Polynomial.natDegree
        (by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]; aesop)
    contradiction
  · have := Exists.choose_spec (show ∃ n : ℕ, 0 < n ∧ (deriv (fun z : ℂ => z ^ k - w) ζ) ≠ 0
        from ⟨1, by norm_num, by aesop⟩)
    all_goals generalize_proofs at *
    rename_i h₁ h₂
    have := h₂.choose_spec.choose_spec.2.2
    have h_deriv : deriv (fun z => z ^ k - w) ζ =
        deriv (fun z => (z - ζ) ^ h₂.choose * h₂.choose_spec.choose z) ζ := by
      exact Filter.EventuallyEq.deriv_eq
        (by filter_upwards [this] with z hz; rw [hz]; ring)
    have h_deriv : deriv (fun z => (z - ζ) ^ h₂.choose * h₂.choose_spec.choose z) ζ =
        h₂.choose * (ζ - ζ) ^ (h₂.choose - 1) * h₂.choose_spec.choose ζ +
        (ζ - ζ) ^ h₂.choose * deriv h₂.choose_spec.choose ζ := by
      convert HasDerivAt.deriv (HasDerivAt.mul
        (HasDerivAt.comp ζ (hasDerivAt_pow _ _) (HasDerivAt.sub (hasDerivAt_id ζ)
        (hasDerivAt_const _ _))) (h₂.choose_spec.choose_spec.1.differentiableAt.hasDerivAt))
        using 1; norm_num
    rcases n : h₂.choose with (_ | _ | n) <;> simp_all +decide [pow_succ']
    have := h₂.choose_spec.choose_spec.2.2.self_of_nhds
    simp_all +decide [sub_eq_iff_eq_add]
    exact h₂.choose_spec.choose_spec.2.1 hζ
  · exact ‹¬AnalyticAt ℂ (fun z => z ^ k - w) ζ›
      (by apply_rules [AnalyticAt.sub, AnalyticAt.pow, analyticAt_id, analyticAt_const])

/-- For an analytic local biholomorphism φ near z₀ with φ(z₀) = 0 and
deriv φ z₀ ≠ 0, there exist r > 0 and δ > 0 such that φ maps
ball(z₀, r) injectively onto a set containing ball(0, δ). -/
theorem local_biholo_ball {φ : ℂ → ℂ} {z₀ : ℂ}
    (hφ : AnalyticAt ℂ φ z₀) (hφ0 : φ z₀ = 0) (hφ' : deriv φ z₀ ≠ 0) :
    ∃ r > 0, ∃ δ > 0,
      Set.InjOn φ (Metric.ball z₀ r) ∧
      Metric.ball 0 δ ⊆ φ '' (Metric.ball z₀ r) ∧
      (∀ t ∈ Metric.ball z₀ r, AnalyticAt ℂ φ t) ∧
      (∀ t ∈ Metric.ball z₀ r, deriv φ t ≠ 0) ∧
      (∀ t ∈ Metric.ball z₀ r, deriv φ t ≠ 0 →
        analyticOrderNatAt (fun s => φ s - φ t) t = 1) := by
  obtain ⟨r, hr⟩ : ∃ r > 0, Set.InjOn φ (Metric.ball z₀ r) ∧
      (∀ t ∈ Metric.ball z₀ r, AnalyticAt ℂ φ t) ∧
      (∀ t ∈ Metric.ball z₀ r, deriv φ t ≠ 0) := by
    have h_inj : ∃ r > 0, Set.InjOn φ (Metric.ball z₀ r) := by
      have h_inj : ∃ r > 0, ∀ x ∈ Metric.ball z₀ r, ∀ y ∈ Metric.ball z₀ r,
          φ x = φ y → x = y := by
        have h_deriv_ne_zero : HasStrictDerivAt φ (deriv φ z₀) z₀ := by
          exact hφ.hasStrictFDerivAt.hasStrictDerivAt
        have := h_deriv_ne_zero.isLittleO.tendsto_div_nhds_zero
        have := Metric.tendsto_nhds_nhds.1 this
        obtain ⟨δ, δ_pos, H⟩ := this (‖deriv φ z₀‖) (norm_pos_iff.mpr hφ')
        use δ / 2, half_pos δ_pos; intros x hx y hy hxy
        specialize H (show Dist.dist (x, y) (z₀, z₀) < δ from
          max_lt (by simpa using hx.trans_le (by linarith))
            (by simpa using hy.trans_le (by linarith)))
        simp_all +decide [div_eq_mul_inv]
        by_cases h : x = y <;> simp_all +decide [mul_comm, sub_eq_iff_eq_add]
      exact ⟨h_inj.choose, h_inj.choose_spec.1,
        fun x hx y hy hxy => h_inj.choose_spec.2 x hx y hy hxy⟩
    obtain ⟨r₁, hr₁⟩ : ∃ r₁ > 0, ∀ t ∈ Metric.ball z₀ r₁, AnalyticAt ℂ φ t := by
      exact Metric.mem_nhds_iff.mp (hφ.eventually_analyticAt)
    obtain ⟨r₂, hr₂⟩ : ∃ r₂ > 0, ∀ t ∈ Metric.ball z₀ r₂, deriv φ t ≠ 0 := by
      have h_deriv_ne_zero : ContinuousAt (deriv φ) z₀ := by
        exact hφ.deriv.continuousAt
      exact Metric.mem_nhds_iff.mp (h_deriv_ne_zero.eventually_ne hφ')
    use min (min h_inj.choose r₁) r₂
    simp [hr₁, hr₂, h_inj.choose_spec]
    exact ⟨h_inj.choose_spec.2.mono (Metric.ball_subset_ball (by aesop)),
      fun t ht₁ ht₂ ht₃ => hr₁.2 t (by aesop),
      fun t ht₁ ht₂ ht₃ => hr₂.2 t (by aesop)⟩
  obtain ⟨δ, hδ⟩ : ∃ δ > 0, Metric.ball 0 δ ⊆ φ '' Metric.ball z₀ r := by
    have h_image : φ '' Metric.ball z₀ r ∈ nhds (φ z₀) := by
      have := hφ.eventually_constant_or_nhds_le_map_nhds
      cases' this with h h
      · exact False.elim <| hφ' <| by
          rw [show deriv φ z₀ = 0 from HasDerivAt.deriv <| by
            exact HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const _ _) h]
      · exact h (Filter.image_mem_map (Metric.ball_mem_nhds _ hr.1))
    exact Metric.mem_nhds_iff.mp (hφ0 ▸ h_image)
  refine' ⟨r, hr.1, δ, hδ.1, hr.2.1, hδ.2, hr.2.2.1, hr.2.2.2, _⟩
  intro t ht h't; exact (by
    have h_order : analyticOrderAt (fun s => φ s - φ t) t = 1 := by
      grind +suggestions
    convert h_order using 1
    simp +decide [analyticOrderNatAt, analyticOrderAt])

/-
Composition formula: if φ is analytic with nonzero derivative at t,
then analyticOrderNatAt (h ∘ φ - h(φ(t))) t = analyticOrderNatAt (h - h(φ t)) (φ t).
-/
theorem analyticOrderNatAt_comp_of_biholo {φ h : ℂ → ℂ} {t : ℂ}
    (hφ_an : AnalyticAt ℂ φ t) (hφ' : deriv φ t ≠ 0)
    (_hh_an : AnalyticAt ℂ h (φ t)) :
    analyticOrderNatAt (fun u => h (φ u) - h (φ t)) t =
    analyticOrderNatAt (fun z => h z - h (φ t)) (φ t) := by
  unfold analyticOrderNatAt;
  rw [ show ( fun u => h ( φ u ) - h ( φ t ) ) = ( fun z => h z - h ( φ t ) ) ∘ φ by ext; rfl, analyticOrderAt_comp_of_deriv_ne_zero ] ; aesop;
  exact hφ'

/-
All k-th roots of a nonzero complex number have norm equal to ‖w‖^(1/k).
-/
theorem kth_root_norm {k : ℕ} (hk : 0 < k) {w ζ : ℂ} (_hw : w ≠ 0) (hζ : ζ ^ k = w) :
    ‖ζ‖ = ‖w‖ ^ ((1 : ℝ) / k) := by
  norm_num [ ← hζ, hk.ne' ];
  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ]

/-
Lifting polynomial roots through a local biholomorphism: given an injective φ on
ball(z₀, r) with ball(0, δ) ⊆ φ '' ball(z₀, r), and given a finset of roots in ball(0, δ),
there is a finset of preimages of the same cardinality.
-/
theorem lift_roots_through_biholo {φ : ℂ → ℂ} {z₀ : ℂ} {r δ : ℝ}
    (h_inj : Set.InjOn φ (Metric.ball z₀ r))
    (h_surj : Metric.ball 0 δ ⊆ φ '' Metric.ball z₀ r)
    (roots : Finset ℂ) (h_roots_in : ∀ ζ ∈ roots, ζ ∈ Metric.ball (0 : ℂ) δ) :
    ∃ preimages : Finset ℂ,
      preimages.card = roots.card ∧
      (↑preimages : Set ℂ) ⊆ Metric.ball z₀ r ∧
      (∀ t ∈ preimages, φ t ∈ roots) ∧
      (∀ t ∈ Metric.ball z₀ r, φ t ∈ roots → t ∈ preimages) := by
  choose! f hf_mem hf_eq using fun x hx => h_surj ( h_roots_in x hx );
  refine' ⟨ Finset.image f roots, _, _, _, _ ⟩ <;> simp_all +decide;
  · exact Finset.card_image_of_injOn fun x hx y hy hxy => by have := hf_eq x hx; have := hf_eq y hy; aesop;
  · exact fun x hx => hf_mem x hx;
  · exact fun t ht ht' => ⟨ φ t, ht', h_inj ( hf_mem _ ht' ) ht ( by aesop ) ⟩

/-
The analytic order of φ(·)^k - w at a preimage t where φ(t) = ζ and ζ^k = w
is 1, when φ has nonzero derivative at t.
-/
theorem order_of_pow_comp_biholo_eq_one {k : ℕ} (hk : 0 < k)
    {φ : ℂ → ℂ} {t : ℂ}
    (hφ_an : AnalyticAt ℂ φ t) (hφ' : deriv φ t ≠ 0)
    {w : ℂ} (hw : w ≠ 0) (hζ : φ t ^ k = w) :
    analyticOrderNatAt (fun u => φ u ^ k - w) t = 1 := by
  have h_analytic_order : analyticOrderNatAt (fun u => (φ u) ^ k - w) t = analyticOrderNatAt (fun z => z ^ k - w) (φ t) := by
    convert analyticOrderNatAt_comp_of_biholo _ _ _ using 1;
    rotate_left;
    rotate_left;
    exact φ;
    exact fun z => z ^ k;
    exacts [ t, hφ_an, hφ', by apply_rules [ AnalyticAt.pow, analyticAt_id ], by simp +decide [ hζ ], by simp +decide [ hζ ] ];
  rw [ h_analytic_order, pow_sub_const_simple_root hk hw hζ ]

/-
Auxiliary: given φ continuous on ball(z₀, R) with φ z₀ = 0 and φ injective,
for any ε ≤ R there exists δ > 0 such that ‖φ t‖ < δ and t ∈ ball(z₀, R)
implies t ∈ ball(z₀, ε).
-/
theorem preimage_near_center {φ : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ_cont : ContinuousOn φ (Metric.closedBall z₀ R))
    (hφ0 : φ z₀ = 0)
    (h_inj : Set.InjOn φ (Metric.closedBall z₀ R))
    {ε : ℝ} (hε : 0 < ε) (_hεR : ε ≤ R) :
    ∃ δ > 0, ∀ t ∈ Metric.ball z₀ R, ‖φ t‖ < δ → t ∈ Metric.ball z₀ ε := by
  -- Consider the set S = closedBall(z₀, R) \ ball(z₀, ε). S is compact.
  set S : Set ℂ := Metric.closedBall z₀ R \ Metric.ball z₀ ε
  have hS_compact : IsCompact S := by
    exact IsCompact.diff ( ProperSpace.isCompact_closedBall _ _ ) ( Metric.isOpen_ball );
  -- Since $0 \notin \varphi(S)$, there exists $\delta > 0$ such that for all $t \in S$, $\|\varphi(t)\| \geq \delta$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ S, ‖φ t‖ ≥ δ := by
    by_cases hS_empty : S.Nonempty;
    · have hδ_pos : ∃ δ ∈ (Set.image (fun t => ‖φ t‖) S), ∀ y ∈ (Set.image (fun t => ‖φ t‖) S), δ ≤ y := by
        apply_rules [ IsCompact.exists_isLeast, hS_compact ];
        · exact hS_compact.image_of_continuousOn ( hφ_cont.norm.mono <| Set.diff_subset );
        · exact hS_empty.image _;
      obtain ⟨ δ, ⟨ t, ht, rfl ⟩, hδ ⟩ := hδ_pos;
      exact ⟨ ‖φ t‖, norm_pos_iff.mpr <| show φ t ≠ 0 from fun h => ht.2 <| by have := h_inj ( show z₀ ∈ Metric.closedBall z₀ R from by simpa using hR.le ) ( show t ∈ Metric.closedBall z₀ R from ht.1 ) ( by aesop ) ; aesop, fun x hx => hδ _ <| Set.mem_image_of_mem _ hx ⟩;
    · exact ⟨ 1, zero_lt_one, fun t ht => False.elim <| hS_empty ⟨ t, ht ⟩ ⟩;
  exact ⟨ δ, hδ_pos, fun t ht ht' => Classical.not_not.1 fun ht'' => not_lt_of_ge ( hδ t ⟨ Metric.ball_subset_closedBall ht, ht'' ⟩ ) ht' ⟩

/-
Roots of X^k - w are exactly the elements ζ with ζ^k = w.
-/
theorem mem_roots_toFinset_iff {k : ℕ} (hk : 0 < k) {w ζ : ℂ} (hw : w ≠ 0) :
    ζ ∈ (Polynomial.X ^ k - Polynomial.C w : Polynomial ℂ).roots.toFinset ↔ ζ ^ k = w := by
  simp +decide [ sub_eq_iff_eq_add ];
  exact fun h => ne_of_apply_ne Polynomial.natDegree <| by rw [ Polynomial.natDegree_X_pow, Polynomial.natDegree_C ] ; aesop;

/-
Analytic order is invariant under local equality.
-/
theorem analyticOrderNatAt_congr {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : ∀ᶠ t in 𝓝 z₀, f t = g t) :
    analyticOrderNatAt f z₀ = analyticOrderNatAt g z₀ := by
  unfold analyticOrderNatAt;
  rw [ analyticOrderAt_congr h ]

/-
The norm of a k-th root is strictly bounded by δ when ‖w‖ < δ^k.
-/
theorem kth_root_norm_lt_of_pow_norm_lt {k : ℕ} (_hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {w ζ : ℂ} (_hw : w ≠ 0) (hζ : ζ ^ k = w) (hw_bound : ‖w‖ < δ ^ k) :
    ‖ζ‖ < δ := by
  exact lt_of_pow_lt_pow_left₀ _ hδ.le ( by simpa [ ← hζ, hδ.le ] using hw_bound )

end JacobianChallenge.HolomorphicForms.LocalMappingThm
