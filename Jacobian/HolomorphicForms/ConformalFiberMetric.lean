import Jacobian.HolomorphicForms.SectionFiberNorm

/-!
# Chart-local conformal fiber norm — metric-route feasibility gate (Milestone D1)

The project's `fiberNorm σ x = ‖σ.toFun x‖` is the INTRINSIC operator norm on the
fiber, which for the cotangent bundle of a Riemann surface is frame-DEPENDENT (it
scales by the chart-transition factor) and only continuous under the `StableChartAt`
adapter. This file is the **feasibility gate** for the honest metric route: it shows
that the fiber norm READ THROUGH A FIXED TRIVIALIZATION `e` — the natural building
block of a conformal/Hermitian metric, where the global norm is glued from such
chart-local reads by a partition of unity — is `ContinuousOn e.baseSet` with **NO
`StableChartAt`**.

The key is that the trivialized read `x ↦ (e ⟨x, σ.toFun x⟩).2` is continuous on
`e.baseSet` purely from the section's smoothness and the trivialization being a
(continuous) partial homeomorphism — exactly the `StableChartAt`-free `h_cont` step
already used inside `SectionFiberNorm.continuous_fiberNorm`. We package it as a named,
reusable lemma here, add the conformal-weight multiplier, and derive `BddAbove` on a
compact subset. This is the chart-local fact the bare operator norm could not give;
the global glue (partition of unity) is Milestone D2, the re-point of `fiberNorm` /
`holomorphicOneForm_hbdd` is D3.

No `axiom`, no fake instance; nothing here imports or uses `StableChartAt`.
-/

namespace JacobianChallenge.HolomorphicForms.ConformalFiberMetric

open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*}
variable [TopologicalSpace (TotalSpace F V)]
variable [∀ x, TopologicalSpace (V x)]
variable [FiberBundle F V]

/--
**Chart-local read fiber norm.** For a fixed trivialization `e`, the fiber value of a
section `σ` read through `e` into the model fiber `F`, then normed. This is the natural
chart-`e` representative of the fiber norm; multiplying by a conformal weight and
gluing such reads by a partition of unity is how a frame-INDEPENDENT (Hermitian /
conformal) fiber norm is assembled — the metric route. -/
noncomputable def readNorm
    (e : Trivialization F (π F V)) (σ : ContMDiffSection I F ⊤ V) (x : M) : ℝ :=
  ‖(e ⟨x, σ.toFun x⟩).2‖

/--
**The chart-local read fiber norm is continuous on the trivialization's baseSet — with
NO `StableChartAt`.** This is the metric-route feasibility gate: the bare *intrinsic*
fiber norm `‖σ.toFun x‖` is frame-dependent and not chart-locally continuous without
chart stability, but the read through a *fixed* trivialization `e` is, purely from the
smooth section + the trivialization being a partial homeomorphism. -/
theorem continuousOn_readNorm
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (σ : ContMDiffSection I F ⊤ V) :
    ContinuousOn (readNorm (I := I) e σ) e.baseSet := by
  -- The trivialized read is continuous on baseSet (StableChartAt-free).
  have h_cont : ContinuousOn
      (fun y => (e (TotalSpace.mk' F y (σ.toFun y))).2) e.baseSet := by
    apply ContinuousOn.comp continuous_snd.continuousOn _ (Set.mapsTo_univ _ _)
    exact ContinuousOn.comp e.continuousOn
      (Continuous.continuousOn (SectionFiberNorm.ContMDiffSection.continuous_totalSpaceMk σ))
      (fun y hy => (Trivialization.coe_mem_source e).mpr hy)
  exact h_cont.norm

/--
**Conformal-weighted chart-local fiber norm.** The read norm times a continuous
positive weight `w` (the conformal factor in chart-`e` coordinates). Continuity is
inherited: weight × read norm, both continuous on `e.baseSet`. -/
noncomputable def weightedReadNorm
    (e : Trivialization F (π F V)) (w : M → ℝ)
    (σ : ContMDiffSection I F ⊤ V) (x : M) : ℝ :=
  w x * readNorm (I := I) e σ x

/-- The conformal-weighted chart-local fiber norm is continuous on `e.baseSet` when the
weight is continuous there — NO `StableChartAt`. -/
theorem continuousOn_weightedReadNorm
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {w : M → ℝ} (hw : ContinuousOn w e.baseSet)
    (σ : ContMDiffSection I F ⊤ V) :
    ContinuousOn (weightedReadNorm (I := I) e w σ) e.baseSet :=
  hw.mul (continuousOn_readNorm (I := I) e σ)

/--
**`BddAbove` of the chart-local read fiber norm on a compact subset of `baseSet`** —
the boundedness the metric route needs locally, NO `StableChartAt`. (Globally these
patch via a finite subcover; here is the single-chart piece.) -/
theorem bddAbove_readNorm_of_isCompact
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (σ : ContMDiffSection I F ⊤ V)
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.baseSet) :
    BddAbove (readNorm (I := I) e σ '' K) :=
  (hK.image_of_continuousOn ((continuousOn_readNorm (I := I) e σ).mono hKe)).bddAbove

end JacobianChallenge.HolomorphicForms.ConformalFiberMetric
