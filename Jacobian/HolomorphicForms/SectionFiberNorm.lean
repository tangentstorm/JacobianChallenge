import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Fiberwise norm of smooth sections

This file defines the fiberwise norm function for smooth sections of a vector bundle
whose fibers carry `NormedAddCommGroup` instances, and proves its continuity under
appropriate compatibility conditions.

This is **Step 1** of the 5-step plan laid out in
`Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` for constructing
the Banach-space data on `HolomorphicOneForm ℂ X`.

## Main definitions

* `ContMDiffSection.fiberNorm` — the function `x ↦ ‖σ.toFun x‖` for a smooth section `σ`.

## Main results

* `ContMDiffSection.continuous_fiberNorm` — continuity of the fiberwise norm, given
  that the `NormedAddCommGroup` norm on each fiber is compatible with the bundle
  trivialization (i.e., each `Trivialization.linearEquivAt` preserves the norm).

## Implementation notes

The continuity proof requires a compatibility condition between the `NormedAddCommGroup`
norm on each fiber `V x` and the model fiber norm on `F`, as mediated by the bundle
trivializations. Specifically, we require that for every trivialization `e` in the
bundle atlas and every `x ∈ e.baseSet`, the trivialization's linear equivalence
`e.linearEquivAt 𝕜 x : V x ≃ₗ[𝕜] F` preserves norms.

For the downstream application to holomorphic 1-forms on a Riemann surface, the fibers
are `CotangentSpace ℂ X x = TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] ℂ`, which carry
`NormedAddCommGroup` from the operator norm. The model fiber is `F = ℂ →L[ℂ] ℂ`.
The trivialization's linear equivalence is an isometry in this case because all fibers
are isometrically isomorphic to `ℂ` via evaluation at `1`.

### Mathlib v4.28.0 API gap

There is no `NormedVectorBundle` class in Mathlib v4.28.0. The `VectorBundle` class
only ensures continuous *linear* equivalences between fibers and the model fiber,
not *isometric* ones. A `NormedVectorBundle` class (guaranteeing isometric
trivializations) would make `continuous_fiberNorm` a consequence of the bundle
structure alone, without the extra `hcompat` hypothesis.
-/

namespace JacobianChallenge.HolomorphicForms.SectionFiberNorm

open Bundle

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

/-- Auxiliary: the total-space section map `x ↦ ⟨x, σ x⟩` is continuous. -/
theorem ContMDiffSection.continuous_totalSpaceMk
    (σ : ContMDiffSection I F ⊤ V) :
    Continuous (fun x => TotalSpace.mk' F x (σ.toFun x)) :=
  σ.contMDiff_toFun.continuous

variable [∀ x, NormedAddCommGroup (V x)]

/--
Fiberwise norm of a smooth section: `x ↦ ‖σ.toFun x‖`.

This is the building block for the sup-norm on `ContMDiffSection`
when the base is compact. Each fiber `V x` is assumed to carry a
`NormedAddCommGroup` instance, so `‖σ.toFun x‖` is the norm of
`σ x` in the fiber over `x`.
-/
noncomputable def ContMDiffSection.fiberNorm
    (σ : ContMDiffSection I F ⊤ V) (x : M) : ℝ :=
  ‖σ.toFun x‖

/--
The fiberwise norm of a smooth section is continuous, given that every trivialization
in the bundle preserves norms on fibers.

The hypothesis `hcompat` states that for every trivialization `e` and every `x` in
`e.baseSet`, the norm of `σ x` in the fiber equals the norm of the trivialized
image in the model fiber `F`. This is the key compatibility condition between the
`NormedAddCommGroup` instances on fibers and the model fiber.

For the holomorphic 1-form case, this is satisfied because the operator norm on
`ℂ →L[ℂ] ℂ` is canonical and trivializations are isometric.
-/
theorem ContMDiffSection.continuous_fiberNorm
    (σ : ContMDiffSection I F ⊤ V)
    (hcompat : ∀ (e : Trivialization F (π F V)) (x : M),
      x ∈ e.baseSet → ‖σ.toFun x‖ = ‖(e ⟨x, σ.toFun x⟩).2‖) :
    Continuous (ContMDiffSection.fiberNorm σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  set e := trivializationAt F V x
  -- The map x ↦ (e (s x)).2 is continuous on e.baseSet.
  have h_cont : ContinuousOn (fun y => (e (TotalSpace.mk' F y (σ.toFun y))).2) e.baseSet := by
    apply ContinuousOn.comp continuous_snd.continuousOn _ (Set.mapsTo_univ _ _)
    exact ContinuousOn.comp e.continuousOn
      (Continuous.continuousOn (ContMDiffSection.continuous_totalSpaceMk σ))
      (fun y hy => (Trivialization.coe_mem_source e).mpr hy)
  -- The norm of the trivialized section is continuous on e.baseSet.
  have h_norm_cont : ContinuousAt
      (fun y => ‖(e (TotalSpace.mk' F y (σ.toFun y))).2‖) x :=
    ContinuousAt.norm (h_cont.continuousAt
      (IsOpen.mem_nhds e.open_baseSet (FiberBundle.mem_baseSet_trivializationAt' x)))
  -- Use hcompat to identify fiberNorm with the trivialized norm on e.baseSet.
  exact h_norm_cont.congr
    (Filter.eventually_of_mem
      (IsOpen.mem_nhds e.open_baseSet (FiberBundle.mem_baseSet_trivializationAt F V x))
      (fun y hy => Eq.symm (hcompat e y hy)))

end JacobianChallenge.HolomorphicForms.SectionFiberNorm
