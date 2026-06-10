import Mathlib.Analysis.Complex.Basic
import Jacobian.HolomorphicForms.UniformizationLocal

open Set Filter Metric
open scoped Topology
open Classical

namespace JacobianChallenge.HolomorphicForms

lemma tendstoUniformlyOn_subseq
    {α β : Type*} [PseudoMetricSpace β]
    {F : ℕ → α → β} {limit : α → β} {S : Set α}
    (h : TendstoUniformlyOn F limit atTop S)
    {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    TendstoUniformlyOn (fun k => F (ψ k)) limit atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  exact hψ (h ε hε)

lemma equicontinuous_subset
    {ι X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (F : ι → X → Y) {s : Set ι} (hs : Equicontinuous (fun x : s => F x))
    {s' : Set ι} (hsub : s' ⊆ s) :
    Equicontinuous (fun x : s' => F x) := by
  intro x u hu
  filter_upwards [hs x u hu] with y h_dist ⟨i, hi⟩
  exact h_dist ⟨i, hsub hi⟩

lemma exists_subseq_tendstoUniformlyOn_closedBall_list
    {ι : Type*}
    (s : List ι)
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (r : ι → ℝ)
    (hclosed : ∀ i n, Metric.closedBall (c i) (r i) ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (z : Metric.closedBall (c i) (r i)),
      (data i n).boundedContinuousOnClosedBall (hclosed i n) z ∈ target i)
    (heq : ∀ i, Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n)) → Metric.closedBall (c i) (r i) → ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∃ limit : ℂ → ℂ,
        TendstoUniformlyOn (fun k z => (data i (φ k)).toFun z) (limit) atTop (Metric.closedBall (c i) (r i)) := by
  induction s with
  | nil =>
    use id
    constructor
    · exact strictMono_id
    · simp
  | cons i s ih =>
    rcases ih with ⟨φ_s, hφ_s_mono, hφ_s_tendsto⟩
    let data' := fun n => data i (φ_s n)
    have hclosed' : ∀ n, Metric.closedBall (c i) (r i) ⊆ Metric.ball (data' n).center ((data' n).radius : ℝ) := fun n => hclosed i (φ_s n)
    have hrange' : ∀ n (z : Metric.closedBall (c i) (r i)), (data' n).boundedContinuousOnClosedBall (hclosed' n) z ∈ target i := fun n => hrange i (φ_s n)
    have heq' : Equicontinuous ((↑) : Set.range (fun n => (data' n).boundedContinuousOnClosedBall (hclosed' n)) → Metric.closedBall (c i) (r i) → ℂ) := by
      let F_full := fun (f : BoundedContinuousFunction (Metric.closedBall (c i) (r i)) ℂ) => (f : Metric.closedBall (c i) (r i) → ℂ)
      have hsub : Set.range (fun n => (data' n).boundedContinuousOnClosedBall (hclosed' n)) ⊆ Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n)) := by
        rintro _ ⟨n, rfl⟩
        exact ⟨φ_s n, rfl⟩
      exact equicontinuous_subset F_full (heq i) hsub

    rcases ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall data' hclosed' (htarget i) hrange' heq' with
      ⟨F, hF_mem, ψ, hψ_mono, hψ_tendsto, limit, hlimit_eq, hlimit_unif⟩
    use φ_s ∘ ψ
    constructor
    · exact hφ_s_mono.comp hψ_mono
    · intro j hj
      cases hj with
      | head =>
        use limit
        exact hlimit_unif
      | tail _ hj_s =>
        rcases hφ_s_tendsto j hj_s with ⟨limit_j, hlimit_j_unif⟩
        use limit_j
        exact tendstoUniformlyOn_subseq hlimit_j_unif (StrictMono.tendsto_atTop hψ_mono)

/--
Finite-family extraction of a simultaneously convergent subsequence.
-/
theorem exists_subseq_tendstoUniformlyOn_closedBall_finite
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (r : ι → ℝ)
    (hclosed : ∀ i n, Metric.closedBall (c i) (r i) ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (z : Metric.closedBall (c i) (r i)),
      (data i n).boundedContinuousOnClosedBall (hclosed i n) z ∈ target i)
    (heq : ∀ i, Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n)) → Metric.closedBall (c i) (r i) → ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ limit : ℂ → ℂ,
        TendstoUniformlyOn (fun k z => (data i (φ k)).toFun z) (limit) atTop (Metric.closedBall (c i) (r i)) := by
  rcases exists_subseq_tendstoUniformlyOn_closedBall_list (Finset.univ.toList) data c r hclosed target htarget hrange heq with ⟨φ, hφ_mono, hφ_tendsto⟩
  use φ, hφ_mono
  intro i
  exact hφ_tendsto i (Finset.mem_toList.mpr (Finset.mem_univ i))

noncomputable def extract_step
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (R : ι → ℝ)
    (hclosed : ∀ i n (r : ℝ), r < R i → Metric.closedBall (c i) r ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (r : ℝ) (hr : r < R i) (z : Metric.closedBall (c i) r),
      (data i n).boundedContinuousOnClosedBall (hclosed i n r hr) z ∈ target i)
    (heq : ∀ i (r : ℝ) (hr : r < R i), Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n r hr)) → Metric.closedBall (c i) r → ℂ))
    (m : ℕ)
    (Φ_m : ℕ → ℕ) :
    { ψ : ℕ → ℕ // StrictMono ψ ∧
      ∀ i, ∃ limit : ℂ → ℂ,
        TendstoUniformlyOn (fun k z => (data i (Φ_m (ψ k))).toFun z) limit atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) } := by
  have hr : ∀ i, R i - 1 / (m + 1 : ℝ) < R i := by
    intro i
    linarith [show (0 : ℝ) < 1 / (m + 1 : ℝ) by positivity]
  let data_m := fun i n => data i (Φ_m n)
  have hclosed' : ∀ i n, Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) ⊆ Metric.ball (data_m i n).center ((data_m i n).radius : ℝ) := fun i n => hclosed i (Φ_m n) _ (hr i)
  have hrange' : ∀ i n z, (data_m i n).boundedContinuousOnClosedBall (hclosed' i n) z ∈ target i := fun i n => hrange i (Φ_m n) _ (hr i)
  have heq' : ∀ i, Equicontinuous ((↑) : Set.range (fun n => (data_m i n).boundedContinuousOnClosedBall (hclosed' i n)) → Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) → ℂ) := by
    intro i
    have hsub : Set.range (fun n => (data_m i n).boundedContinuousOnClosedBall (hclosed' i n)) ⊆ Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n _ (hr i))) := by
      rintro _ ⟨n, rfl⟩
      exact ⟨Φ_m n, rfl⟩
    let F_full := fun (f : BoundedContinuousFunction (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) ℂ) => (f : Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) → ℂ)
    exact equicontinuous_subset F_full (heq i _ (hr i)) hsub
  have h_ex := exists_subseq_tendstoUniformlyOn_closedBall_finite data_m c (fun i => R i - 1 / (m + 1 : ℝ)) hclosed' target htarget hrange' heq'
  exact Classical.indefiniteDescription _ h_ex

noncomputable def extraction_sequence
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (R : ι → ℝ)
    (hclosed : ∀ i n (r : ℝ), r < R i → Metric.closedBall (c i) r ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (r : ℝ) (hr : r < R i) (z : Metric.closedBall (c i) r),
      (data i n).boundedContinuousOnClosedBall (hclosed i n r hr) z ∈ target i)
    (heq : ∀ i (r : ℝ) (hr : r < R i), Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n r hr)) → Metric.closedBall (c i) r → ℂ)) :
    ℕ → { Φ : ℕ → ℕ // StrictMono Φ }
| 0 => ⟨id, strictMono_id⟩
| m + 1 =>
  let Φ_m := extraction_sequence data c R hclosed target htarget hrange heq m
  let step := extract_step data c R hclosed target htarget hrange heq m Φ_m.1
  ⟨Φ_m.1 ∘ step.1, Φ_m.2.comp step.2.1⟩

lemma tendstoLocallyUniformlyOn_of_tendstoUniformlyOn_subballs
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → (ℂ → ℂ))
    (c : ι → ℂ) (R : ι → ℝ)
    (h_unif : ∀ i (m : ℕ), ∃ L : ℂ → ℂ, TendstoUniformlyOn (fun k z => data i k z) L atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)))) :
    ∀ i, ∃ limit : ℂ → ℂ, TendstoLocallyUniformlyOn (fun k z => data i k z) limit atTop (Metric.ball (c i) (R i)) := by
  intro i
  have hl : ∀ m : ℕ, ∃ L : ℂ → ℂ, TendstoUniformlyOn (fun k z => data i k z) L atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) := fun m => h_unif i m
  let L (m : ℕ) := Classical.choose (hl m)
  have hL : ∀ (m : ℕ), TendstoUniformlyOn (fun k z => data i k z) (L m) atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) := fun m => Classical.choose_spec (hl m)
  
  have h_eq : ∀ (m n : ℕ) z, z ∈ Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) → z ∈ Metric.closedBall (c i) (R i - 1 / (n + 1 : ℝ)) → L m z = L n z := by
    intro m n z hm hn
    have h1 := TendstoUniformlyOn.tendsto_at (hL m) hm
    have h2 := TendstoUniformlyOn.tendsto_at (hL n) hn
    exact tendsto_nhds_unique h1 h2

  have exists_m : ∀ z ∈ Metric.ball (c i) (R i), ∃ m : ℕ, z ∈ Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) := by
    intro z hz
    have hd : dist z (c i) < R i := hz
    have hd2 : 0 < R i - dist z (c i) := sub_pos.mpr hd
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / (R i - dist z (c i)))
    use m
    rw [mem_closedBall]
    have hm1 : (1 : ℝ) / (R i - dist z (c i)) < ↑m + 1 := by
      calc (1 : ℝ) / (R i - dist z (c i)) < ↑m := hm
        _ < ↑m + 1 := lt_add_one (m : ℝ)
    have hpos : (0 : ℝ) < ↑m + 1 := by positivity
    have hm2 : (1 : ℝ) / (↑m + 1) < R i - dist z (c i) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hd2] at hm1
      linarith
    linarith

  let limit_fn (z : ℂ) : ℂ :=
    if hz : z ∈ Metric.ball (c i) (R i) then
      L (Nat.find (exists_m z hz)) z
    else 0

  use limit_fn
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hK_sub hK_comp
  
  have exists_m_K : ∃ m : ℕ, K ⊆ Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)) := by
    have h_cont : Continuous (fun z : ℂ => dist z (c i)) := continuous_id.dist continuous_const
    rcases K.eq_empty_or_nonempty with rfl | hK_ne
    · use 0; simp
    obtain ⟨z_max, hz_max_in, hz_max_ge⟩ := IsCompact.exists_isMaxOn hK_comp hK_ne h_cont.continuousOn
    have hd : dist z_max (c i) < R i := hK_sub hz_max_in
    obtain ⟨m, hm⟩ := exists_m z_max hd
    use m
    intro z hz
    have hm_max_ineq : dist z (c i) ≤ dist z_max (c i) := hz_max_ge hz
    rw [mem_closedBall] at hm ⊢
    linarith
    
  rcases exists_m_K with ⟨m, hm_K⟩
  
  have h_limit_eq : EqOn limit_fn (L m) K := by
    intro z hz
    have hz_ball : z ∈ Metric.ball (c i) (R i) := hK_sub hz
    simp only [limit_fn, dif_pos hz_ball]
    have hm_find := Nat.find_spec (exists_m z hz_ball)
    exact h_eq (Nat.find (exists_m z hz_ball)) m z hm_find (hm_K hz)
    
  have h_unif_K := (hL m).mono hm_K
  exact TendstoUniformlyOn.congr_right h_unif_K h_limit_eq.symm

lemma nat_strictMono_le (f : ℕ → ℕ) (h : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (h (Nat.lt_succ_self k)))

lemma diagonal_subseq_tendsto
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → (ℂ → ℂ))
    (c : ι → ℂ) (R : ι → ℝ)
    (Φ : ℕ → ℕ → ℕ)
    (step : ℕ → ℕ → ℕ)
    (h_sub : ∀ m k, Φ (m + 1) k = Φ m (step m k))
    (step_mono : ∀ m, StrictMono (step m))
    (h_unif_m : ∀ (m : ℕ) i, ∃ limit : ℂ → ℂ, TendstoUniformlyOn (fun k z => data i (Φ (m + 1) k) z) limit atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ)))) :
    ∀ i (m : ℕ), ∃ L : ℂ → ℂ, TendstoUniformlyOn (fun k z => data i (Φ k k) z) L atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) := by
  intro i m
  rcases h_unif_m m i with ⟨L, hL⟩
  use L
  have h_gj : ∀ j : ℕ, ∃ g_j : ℕ → ℕ, StrictMono g_j ∧ Φ (m + 1 + j) = Φ (m + 1) ∘ g_j := by
    intro j
    induction j with
    | zero =>
      use id
      constructor
      · exact strictMono_id
      · rfl
    | succ j ih =>
      rcases ih with ⟨g_j, hg_j_mono, hg_j_eq⟩
      use g_j ∘ step (m + 1 + j)
      constructor
      · exact StrictMono.comp hg_j_mono (step_mono (m + 1 + j))
      · funext k
        calc Φ (m + 1 + j + 1) k = Φ (m + 1 + j) (step (m + 1 + j) k) := h_sub (m + 1 + j) k
          _ = (Φ (m + 1) ∘ g_j) (step (m + 1 + j) k) := by rw [hg_j_eq]
          _ = Φ (m + 1) (g_j (step (m + 1 + j) k)) := rfl
  
  let idx := fun k : ℕ => if hk : m + 1 ≤ k then Classical.choose (h_gj (k - (m + 1))) k else 0
  have h_diag_tail : ∀ k, m + 1 ≤ k → Φ k k = Φ (m + 1) (idx k) := by
    intro k hk
    have eq_idx : idx k = Classical.choose (h_gj (k - (m + 1))) k := dif_pos hk
    have h2 : m + 1 + (k - (m + 1)) = k := Nat.add_sub_of_le hk
    have h3 := (Classical.choose_spec (h_gj (k - (m + 1)))).2
    calc Φ k k = Φ (m + 1 + (k - (m + 1))) k := by congr 1; exact h2.symm
      _ = (Φ (m + 1) ∘ Classical.choose (h_gj (k - (m + 1)))) k := congrFun h3 k
      _ = Φ (m + 1) (Classical.choose (h_gj (k - (m + 1))) k) := rfl
      _ = Φ (m + 1) (idx k) := by rw [eq_idx]

  have h_idx_tendsto : Tendsto idx atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro A
    use max (m + 1) A
    intro b hb
    have hm : m + 1 ≤ b := le_trans (le_max_left (m + 1) A) hb
    have hA : A ≤ b := le_trans (le_max_right (m + 1) A) hb
    have eq1 : idx b = Classical.choose (h_gj (b - (m + 1))) b := dif_pos hm
    rw [eq1]
    have h_g_mono : StrictMono (Classical.choose (h_gj (b - (m + 1)))) := (Classical.choose_spec (h_gj (b - (m + 1)))).1
    have h_g_le : b ≤ Classical.choose (h_gj (b - (m + 1))) b := nat_strictMono_le _ h_g_mono b
    exact le_trans hA h_g_le

  have hL_comp : TendstoUniformlyOn (fun k z => data i (Φ (m + 1) (idx k)) z) L atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) :=
    tendstoUniformlyOn_subseq hL h_idx_tendsto

  rw [Metric.tendstoUniformlyOn_iff] at hL_comp ⊢
  intro ε hε
  have h1 := hL_comp ε hε
  filter_upwards [h1, eventually_ge_atTop (m + 1)] with k hk hm_le z hz
  have heq : data i (Φ k k) z = data i (Φ (m + 1) (idx k)) z := by
    rw [h_diag_tail k hm_le]
  rw [heq]
  exact hk z hz

lemma exists_diagonal_subseq_tendstoLocallyUniformlyOn_finite
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (R : ι → ℝ)
    (hclosed : ∀ i n (r : ℝ), r < R i → Metric.closedBall (c i) r ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (r : ℝ) (hr : r < R i) (z : Metric.closedBall (c i) r),
      (data i n).boundedContinuousOnClosedBall (hclosed i n r hr) z ∈ target i)
    (heq : ∀ i (r : ℝ) (hr : r < R i), Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n r hr)) → Metric.closedBall (c i) r → ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ limit : ℂ → ℂ,
        TendstoLocallyUniformlyOn (fun k z => (data i (φ k)).toFun z) limit atTop (Metric.ball (c i) (R i)) := by
  let seq := extraction_sequence data c R hclosed target htarget hrange heq
  let Φ (m : ℕ) : ℕ → ℕ := (seq m).1
  have h_mono : ∀ m, StrictMono (Φ m) := fun m => (seq m).2
  let step (m : ℕ) : ℕ → ℕ := (extract_step data c R hclosed target htarget hrange heq m (Φ m)).1
  have h_sub : ∀ m k, Φ (m + 1) k = Φ m (step m k) := fun m k => rfl
  have step_mono : ∀ m, StrictMono (step m) := fun m => (extract_step data c R hclosed target htarget hrange heq m (Φ m)).2.1

  let diagonal (m : ℕ) := Φ m m
  have h_diag_mono : StrictMono diagonal := by
    apply strictMono_nat_of_lt_succ
    intro m
    calc Φ m m < Φ m (m + 1) := h_mono m (Nat.lt_succ_self m)
      _ ≤ Φ m (step m (m + 1)) := (h_mono m).monotone (nat_strictMono_le (step m) (step_mono m) (m + 1))
      _ = Φ (m + 1) (m + 1) := (h_sub m (m + 1)).symm

  use diagonal, h_diag_mono
  
  have h_unif : ∀ i (m : ℕ), ∃ L : ℂ → ℂ, TendstoUniformlyOn (fun k z => (data i (diagonal k)).toFun z) L atTop (Metric.closedBall (c i) (R i - 1 / (m + 1 : ℝ))) := by
    apply diagonal_subseq_tendsto (fun i k z => (data i k).toFun z) c R Φ step h_sub step_mono
    intro m i
    exact (extract_step data c R hclosed target htarget hrange heq m (Φ m)).2.2 i

  exact tendstoLocallyUniformlyOn_of_tendstoUniformlyOn_subballs (fun i k z => (data i (diagonal k)).toFun z) c R h_unif

end JacobianChallenge.HolomorphicForms

