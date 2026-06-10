import Jacobian.HolomorphicForms.UniformizationLocal

open Set Filter Metric
open scoped Topology

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

end JacobianChallenge.HolomorphicForms
