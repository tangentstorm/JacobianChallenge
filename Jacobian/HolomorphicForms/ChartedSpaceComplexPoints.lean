import Mathlib.Geometry.Manifold.Complex

namespace JacobianChallenge.HolomorphicForms

lemma exists_two_distinct_points_of_chartedSpaceComplex
    {X : Type*} [TopologicalSpace X] [Nonempty X] [ChartedSpace ℂ X] :
    ∃ p q : X, p ≠ q := by
  let p : X := Classical.arbitrary X
  let φ := chartAt ℂ p
  have hp_src : p ∈ φ.source := mem_chart_source ℂ p
  have hφp : φ p ∈ φ.target := φ.map_source hp_src
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp φ.open_target (φ p) hφp
  set z : ℂ := φ p + ((ε / 2 : ℝ) : ℂ) with hz_def
  have hz_ne_φp : z ≠ φ p := by
    intro heq
    have h0 : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have h := sub_eq_zero.mpr heq
      rw [hz_def] at h
      simpa using h
    have h_real : (ε / 2 : ℝ) = 0 := by exact_mod_cast h0
    linarith
  have hdist : dist z (φ p) = ε / 2 := by
    rw [hz_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
  have hz_in_target : z ∈ φ.target := by
    apply hball
    rw [Metric.mem_ball, hdist]; linarith
  refine ⟨p, φ.symm z, ?_⟩
  intro hpq
  apply hz_ne_φp
  rw [hpq, φ.right_inv hz_in_target]

lemma exists_three_distinct_points_of_chartedSpaceComplex
    {X : Type*} [TopologicalSpace X] [Nonempty X] [ChartedSpace ℂ X] :
    ∃ p q r : X, p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  let p : X := Classical.arbitrary X
  let φ := chartAt ℂ p
  have hp_src : p ∈ φ.source := mem_chart_source ℂ p
  have hφp : φ p ∈ φ.target := φ.map_source hp_src
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp φ.open_target (φ p) hφp
  set z₁ : ℂ := φ p + ((ε / 2 : ℝ) : ℂ) with hz1_def
  set z₂ : ℂ := φ p + ((ε / 3 : ℝ) : ℂ) with hz2_def
  have hz1_ne_φp : z₁ ≠ φ p := by
    intro heq
    have h0 : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have h := sub_eq_zero.mpr heq
      rw [hz1_def] at h
      simpa using h
    have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h0
    linarith
  have hz2_ne_φp : z₂ ≠ φ p := by
    intro heq
    have h0 : ((ε / 3 : ℝ) : ℂ) = 0 := by
      have h := sub_eq_zero.mpr heq
      rw [hz2_def] at h
      simpa using h
    have : (ε / 3 : ℝ) = 0 := by exact_mod_cast h0
    linarith
  have hz1_ne_z2 : z₁ ≠ z₂ := by
    intro heq
    have h_diff : ((ε / 2 : ℝ) : ℂ) = ((ε / 3 : ℝ) : ℂ) := by
      have h_sub : z₁ - z₂ = 0 := sub_eq_zero.mpr heq
      have h_eq : z₁ - z₂ = ((ε / 2 : ℝ) : ℂ) - ((ε / 3 : ℝ) : ℂ) := by
        rw [hz1_def, hz2_def]; ring
      rw [h_eq] at h_sub
      exact sub_eq_zero.mp h_sub
    have : (ε / 2 : ℝ) = (ε / 3 : ℝ) := by exact_mod_cast h_diff
    linarith
  have hd1 : dist z₁ (φ p) = ε / 2 := by
    rw [hz1_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
  have hd2 : dist z₂ (φ p) = ε / 3 := by
    rw [hz2_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 3)]
  have hz1_in : z₁ ∈ φ.target := hball (by rw [Metric.mem_ball, hd1]; linarith)
  have hz2_in : z₂ ∈ φ.target := hball (by rw [Metric.mem_ball, hd2]; linarith)
  refine ⟨p, φ.symm z₁, φ.symm z₂, ?_, ?_, ?_⟩
  · intro h
    apply hz1_ne_φp
    rw [h, φ.right_inv hz1_in]
  · intro h
    apply hz2_ne_φp
    rw [h, φ.right_inv hz2_in]
  · intro h
    apply hz1_ne_z2
    have := congrArg φ h
    rw [φ.right_inv hz1_in, φ.right_inv hz2_in] at this
    exact this

lemma exists_distinct_from_pair_of_chartedSpaceComplex
    {X : Type*} [TopologicalSpace X] [Nonempty X] [ChartedSpace ℂ X]
    (p q : X) : ∃ r : X, r ≠ p ∧ r ≠ q := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    exists_three_distinct_points_of_chartedSpaceComplex (X := X)
  by_cases ha : a = p ∨ a = q
  · by_cases hb : b = p ∨ b = q
    · by_cases h_c : c = p ∨ c = q
      · -- All three of a, b, c lie in {p, q}, but they are pairwise distinct: pigeonhole.
        exfalso
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases h_c with rfl | rfl <;>
          first
            | exact hab rfl
            | exact hac rfl
            | exact hbc rfl
      · exact ⟨c, fun h => h_c (Or.inl h), fun h => h_c (Or.inr h)⟩
    · exact ⟨b, fun h => hb (Or.inl h), fun h => hb (Or.inr h)⟩
  · exact ⟨a, fun h => ha (Or.inl h), fun h => ha (Or.inr h)⟩

end JacobianChallenge.HolomorphicForms
