import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of CLM-bundle composition (project-local Mathlib addition)

Mathlib v4.28.0 (`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`) ships
`ContMDiffWithinAt.clm_apply_of_inCoordinates` (lines 179–202), which
states that *applying* a smooth CLM-bundle section to a smooth
vector-bundle section is smooth. The dual-position analogue —
*composing* two smooth CLM-bundle sections — is absent from v4.28.0.

This file fills that gap project-locally:

* `ContMDiffWithinAt.clm_compose_of_inCoordinates` — three-base
  composition smoothness, proved by mirroring Mathlib's
  `clm_apply_of_inCoordinates` proof structure (decomposing via
  `inCoordinates_eq` plus the function-level `ContMDiffWithinAt.clm_comp`).
* `ContMDiffAt.clm_compose_of_inCoordinates` — `at`-version wrapper.

These are used downstream by
`Jacobian/HolomorphicForms/PullbackBundled.lean`'s section-level
smoothness of the chain-rule pullback (which composes two smooth
CLM-bundle sections: `mfderiv f` and `η ∘ f`).
-/

open Bundle Set Topology ContinuousLinearMap
open scoped Manifold Bundle Topology

section

/- Three manifolds `B₁`, `B₂`, `B₃` (with models `IB₁`, `IB₂`, `IB₃`),
and three vector bundles `E₁`, `E₂`, `E₃` over them with model fibers
`F₁`, `F₂`, `F₃`. Also `M` — the source of all our maps. -/
variable {𝕜 F₁ F₂ F₃ B₁ B₂ B₃ M : Type*}
  {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} {E₃ : B₃ → Type*}
  [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB₁ : Type*} [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁]
  {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*} [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂]
  {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EB₃ : Type*} [NormedAddCommGroup EB₃] [NormedSpace 𝕜 EB₃]
  {HB₃ : Type*} [TopologicalSpace HB₃]
  {IB₃ : ModelWithCorners 𝕜 EB₃ HB₃} [TopologicalSpace B₃] [ChartedSpace HB₃ B₃]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : WithTop ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b₁ : M → B₁} {b₂ : M → B₂} {b₃ : M → B₃} {m₀ : M}
  {ϕ : ∀ m, E₂ (b₂ m) →L[𝕜] E₃ (b₃ m)}
  {ψ : ∀ m, E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)}
  {s : Set M}

/-- Composition of two smooth CLM-bundle sections is smooth, in
`inCoordinates` form.

This is the project-local analogue of Mathlib's
`ContMDiffWithinAt.clm_apply_of_inCoordinates`
(`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`), with CLM-application
replaced by CLM-composition. The proof structure mirrors the application
version: decompose via `inCoordinates_eq` to function-level CLMs, apply
`ContMDiffWithinAt.clm_comp`, and use the trivialization-round-trip
collapse to bridge the two sides. -/
lemma ContMDiffWithinAt.clm_compose_of_inCoordinates
    (hϕ : ContMDiffWithinAt IM 𝓘(𝕜, F₂ →L[𝕜] F₃) n
      (fun m ↦ inCoordinates F₂ E₂ F₃ E₃ (b₂ m₀) (b₂ m) (b₃ m₀) (b₃ m) (ϕ m)) s m₀)
    (hψ : ContMDiffWithinAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ψ m)) s m₀)
    (hb₁ : ContMDiffWithinAt IM IB₁ n b₁ s m₀)
    (hb₂ : ContMDiffWithinAt IM IB₂ n b₂ s m₀)
    (hb₃ : ContMDiffWithinAt IM IB₃ n b₃ s m₀) :
    ContMDiffWithinAt IM 𝓘(𝕜, F₁ →L[𝕜] F₃) n
      (fun m ↦ inCoordinates F₁ E₁ F₃ E₃ (b₁ m₀) (b₁ m) (b₃ m₀) (b₃ m)
        ((ϕ m).comp (ψ m))) s m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hψ hb₁ hb₂ hb₃ ⊢
  -- Function-level smoothness of the in-coordinates composition.
  apply (ContMDiffWithinAt.clm_comp hϕ hψ).congr_of_eventuallyEq_of_mem ?_
    (mem_insert m₀ s)
  -- Eventual base-set membership for all three bases.
  have A₁ : ∀ᶠ m in 𝓝[insert m₀ s] m₀,
      b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hb₁.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A₂ : ∀ᶠ m in 𝓝[insert m₀ s] m₀,
      b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  have A₃ : ∀ᶠ m in 𝓝[insert m₀ s] m₀,
      b₃ m ∈ (trivializationAt F₃ E₃ (b₃ m₀)).baseSet := by
    apply hb₃.continuousWithinAt
    apply (trivializationAt F₃ E₃ (b₃ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₃ m₀)
  filter_upwards [A₁, A₂, A₃] with m hm₁ hm₂ hm₃
  -- Expand both `inCoordinates` on the LHS via `inCoordinates_eq`,
  -- and the target `inCoordinates` on the RHS too.
  rw [inCoordinates_eq hm₁ hm₂, inCoordinates_eq hm₂ hm₃,
      inCoordinates_eq hm₁ hm₃]
  -- Both sides are CLM compositions; the middle round-trip
  -- e₂.cle (b₂ m) ∘ e₂.cle (b₂ m).symm collapses to identity.
  ext v
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- `ContMDiffAt` version of `ContMDiffWithinAt.clm_compose_of_inCoordinates`. -/
lemma ContMDiffAt.clm_compose_of_inCoordinates
    (hϕ : ContMDiffAt IM 𝓘(𝕜, F₂ →L[𝕜] F₃) n
      (fun m ↦ inCoordinates F₂ E₂ F₃ E₃ (b₂ m₀) (b₂ m) (b₃ m₀) (b₃ m) (ϕ m)) m₀)
    (hψ : ContMDiffAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ψ m)) m₀)
    (hb₁ : ContMDiffAt IM IB₁ n b₁ m₀)
    (hb₂ : ContMDiffAt IM IB₂ n b₂ m₀)
    (hb₃ : ContMDiffAt IM IB₃ n b₃ m₀) :
    ContMDiffAt IM 𝓘(𝕜, F₁ →L[𝕜] F₃) n
      (fun m ↦ inCoordinates F₁ E₁ F₃ E₃ (b₁ m₀) (b₁ m) (b₃ m₀) (b₃ m)
        ((ϕ m).comp (ψ m))) m₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hψ hb₁ hb₂ hb₃ ⊢
  exact ContMDiffWithinAt.clm_compose_of_inCoordinates hϕ hψ hb₁ hb₂ hb₃

end
