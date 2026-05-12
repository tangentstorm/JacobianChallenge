import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Archimedean

/-! # Blueprint stub: `lem:montel-compactness`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Montel compactness in sequential form: every sequence
`ω_n : ℕ → H⁰(X, Ω¹)` with `‖ω_n‖ ≤ 1` has a subsequence
`ω_{φ n}` converging in sup norm to some `ω∞ ∈ H⁰(X, Ω¹)` with
`‖ω∞‖ ≤ 1`.

NOTE FOR WORKERS: this lemma stops at the **sequential**
`Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim)) atTop (𝓝 0)`.
The downstream consumer `hone_unit_ball_compact` wants
`IsCompact (Metric.closedBall (0 : H) 1)` for a normed-space
realisation `H`. The conversion requires the metric-space bridge
"sequential compactness ⇒ topological compactness on first-countable
spaces". -/

namespace JacobianChallenge.Blueprint

open scoped Manifold Topology
open Filter JacobianChallenge.HolomorphicForms

/-- The sup norm `holomorphicSupNorm X ω = ⨆ x, ‖ω.1 x‖` is
nonnegative. -/
lemma holomorphicSupNorm_nonneg
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : HolomorphicOneForm ℂ X) :
    0 ≤ holomorphicSupNorm X ω := by
  unfold holomorphicSupNorm cotangentFiberNormAt cotangentFiberNorm
  exact Real.iSup_nonneg (fun _ => norm_nonneg _)

/-- If the fiber norm `‖ω.1 x‖` is bounded by `r ≥ 0` pointwise on
`X`, then so is the sup norm. -/
lemma holomorphicSupNorm_le_of_pointwise
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : HolomorphicOneForm ℂ X) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x, ‖ω.1 x‖ ≤ r) :
    holomorphicSupNorm X ω ≤ r := by
  unfold holomorphicSupNorm cotangentFiberNormAt cotangentFiberNorm
  exact Real.iSup_le h hr

/-! ### Connected case -/

/-- Connected case of Montel pointwise extraction. Uses the upstream
sorry-blocked Banach-data and Montel results from
`CompactRiemannSurface.lean`, which require `ConnectedSpace X`. -/
private theorem montel_pointwise_extraction_connected
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ x : X,
          ‖(ω (φ n) - ωlim).1 x‖ ≤ ε := by
  let B : HolomorphicOneFormBanachData X :=
    { toNorm := ⟨SectionSupNorm.supNorm⟩
      toMetricSpace := holomorphicOneForm_metricSpace X
      dist_eq := fun _ _ => rfl
      norm_smul_le := SectionSupNorm.supNorm_smul_le (holomorphicOneForm_hcompat X)
      complete := holomorphicOneForm_supNorm_completeSpace X
      norm_le := fun σ x =>
        le_ciSup (SectionSupNorm.bddAbove_range_norm (holomorphicOneForm_hcompat X) σ) x }
  have hσ : ∀ n, B.toNorm.norm (ω n) ≤ 1 := h_bounded
  obtain ⟨a, φ, hφ_mono, hφ_tendsto⟩ :=
    holomorphicOneForm_montel_subseq_tendsto X B ω hσ
  refine ⟨φ, hφ_mono, a, ?_, ?_⟩
  · rw [show holomorphicSupNorm X a = B.toNorm.norm a from rfl]
    exact holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le X B (ω ∘ φ) a
      (fun n => hσ (φ n)) hφ_tendsto
  · intro ε hε
    letI : MetricSpace (HolomorphicOneForm ℂ X) := B.toMetricSpace
    rw [Metric.tendsto_atTop] at hφ_tendsto
    obtain ⟨N, hN⟩ := hφ_tendsto ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hd := hN n hn
    have h_le := B.norm_le (ω (φ n) - a) x
    have h_norm_eq : B.toNorm.norm (ω (φ n) - a) = dist ((ω ∘ φ) n) a := by
      rw [B.dist_eq]; rfl
    linarith

/-! ### Main theorem -/

/-- Montel pointwise extraction. Reduces to the connected case
(`montel_pointwise_extraction_connected`) by classical case analysis.
The empty case is trivial; the nonempty case uses the fact that a
compact manifold charted over ℂ is locally connected, hence has
finitely many clopen connected components, and the classical
decidability of `ConnectedSpace X`. -/
private theorem montel_pointwise_extraction
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ x : X,
          ‖(ω (φ n) - ωlim).1 x‖ ≤ ε := by
  by_cases hne : IsEmpty X
  · -- Empty case: trivial
    refine ⟨id, strictMono_id, 0, ?_, fun ε _ => ⟨0, fun n _ x => (hne.false x).elim⟩⟩
    simp [holomorphicSupNorm, cotangentFiberNormAt, cotangentFiberNorm, Real.iSup_of_isEmpty]
  · rw [not_isEmpty_iff] at hne
    haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
    by_cases hconn : ConnectedSpace X
    · exact montel_pointwise_extraction_connected X ω _h_bounded
    · -- Non-connected case. BLOCKED on upstream `ConnectedSpace X`
      -- assumptions in `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`
      -- (outside the allowed write scope for this task).
      --
      -- Missing prerequisite, in order of preference:
      --
      --   (P1) Generalise the upstream Montel chain to drop
      --        `[ConnectedSpace X]`:
      --          * `holomorphicOneForm_closedBall_totallyBounded`
      --          * `holomorphicOneForm_montel_subseq_isCauchy`
      --          * `holomorphicOneForm_montel_subseq_tendsto`
      --          * `holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le`
      --        Then `montel_pointwise_extraction_connected` immediately
      --        proves this branch (drop the `ConnectedSpace X` instance
      --        from its hypotheses).
      --
      --   (P2) Alternatively, build section-restriction infrastructure
      --        for `HolomorphicOneForm ℂ X` to a clopen connected
      --        component `C ⊆ X` (i.e. a `ContMDiffSection` pullback
      --        along the inclusion `↥C → X` of the cotangent bundle),
      --        plus a gluing lemma reassembling sections from finitely
      --        many components. With this, restrict each `ω n` to each
      --        component, apply the connected case + a diagonal
      --        subsequence argument, then glue limits.
      --
      -- A compact charted-space-over-ℂ X is locally connected
      -- (`ChartedSpace.locallyConnectedSpace ℂ X` — already in scope
      -- via the `haveI` above), hence its connected components are
      -- clopen and finite in number — but turning that observation
      -- into a usable decomposition of `HolomorphicOneForm ℂ X`
      -- requires (P2).
      sorry

/-- Montel compactness (sequential form): the closed unit ball of
`H⁰(X, Ω¹)` is sequentially compact in the sup-norm sense. -/
theorem montel_compactness
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim))
          atTop (𝓝 0) := by
  obtain ⟨φ, hφ, ωlim, hbnd, hpt⟩ :=
    montel_pointwise_extraction X ω _h_bounded
  refine ⟨φ, hφ, ωlim, hbnd, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := hpt (ε / 2) hε2
  refine ⟨N, fun n hn => ?_⟩
  have h_pt : ∀ x, ‖(ω (φ n) - ωlim).1 x‖ ≤ ε / 2 := hN n hn
  have h_le : holomorphicSupNorm X (ω (φ n) - ωlim) ≤ ε / 2 :=
    holomorphicSupNorm_le_of_pointwise X _ (le_of_lt hε2) h_pt
  have h_nn : 0 ≤ holomorphicSupNorm X (ω (φ n) - ωlim) :=
    holomorphicSupNorm_nonneg X _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn]
  linarith

end JacobianChallenge.Blueprint
