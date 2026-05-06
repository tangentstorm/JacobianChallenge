import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Operator-norm continuity of `ω.toFun` for a holomorphic 1-form

This file proves that for a holomorphic 1-form `ω` on a complex manifold `X`
modeled on a complex normed space `E` (self-model), the underlying function
`ω.toFun : X → (E →L[ℂ] ℂ)` is continuous in the operator-norm topology.

## Main result

* `holomorphicOneForm_toFun_continuous` — global operator-norm continuity
  of `b ↦ ω.toFun b : X → (E →L[ℂ] ℂ)`.

## Strategy

For each `b₀ : X` we factor continuity at `b₀` through the trivialization
of the cotangent bundle:

1. By `Trivialization.contMDiffAt_section_iff`, smoothness of the lifted
   section is equivalent to operator-norm smoothness of the trivialized
   second component, which equals `(ω.toFun b).comp (Tangent_symmL_b)`.
2. Smooth ⇒ continuous.
3. Post-compose with `Tangent_contLinMapAt_b` (which is the inverse of
   `Tangent_symmL_b` on the baseSet) to recover `ω.toFun b`.

## Mathlib-contribution status

The helpers `tangentBundle_continuousLinearMapAt_continuousAt_self` and
`tangentBundle_symmL_continuousAt_self` state operator-norm continuity at
`b₀` of the diagonal chart-overlap derivative, with value identity at `b₀`.
By `TangentBundle.continuousLinearMapAt_trivializationAt` these unfold to
`b ↦ mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) (extChartAt 𝓘(ℂ,E) b₀) b`. Mathlib's
`continuousOn_tangentCoordChange x y` gives operator-norm continuity for
**fixed** `x, y`, but the diagonal version is currently absent in
Mathlib v4.28.0. Both helpers are clearly isolated `sorry`-stubs.
-/

namespace JacobianChallenge.Periods

open scoped Manifold Topology
open Bundle JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The "tangent bundle continuous-linear-map-at" specialised to self-model:
returns an `E →L[ℂ] E` (using the definitional equality
`TangentSpace 𝓘(ℂ,E) b = E`). -/
private noncomputable def tangent_contLinMapAt (b₀ b : X) : E →L[ℂ] E :=
  (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).continuousLinearMapAt ℂ b

/-- The "tangent bundle symmL" specialised to self-model: returns an
`E →L[ℂ] E`. -/
private noncomputable def tangent_symmL (b₀ b : X) : E →L[ℂ] E :=
  (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).symmL ℂ b

/-- The cotangent value, viewed as `E →L[ℂ] ℂ` via the definitional fiber
identification. -/
private noncomputable def cotangent_value
    (ω : HolomorphicOneForm E X) (b : X) : E →L[ℂ] ℂ :=
  ω.toFun b

/-- **Diagonal chart-overlap-derivative continuity (Mathlib gap).**

For the tangent bundle of a complex manifold `X` modeled on `E` (self-model),
`b ↦ tangent_contLinMapAt b₀ b : X → (E →L[ℂ] E)` is continuous at `b₀`,
with value `id` at `b₀`.

By `TangentBundle.continuousLinearMapAt_trivializationAt`, this unfolds to
`b ↦ mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) (extChartAt 𝓘(ℂ,E) b₀) b`.

**Status (sorry):** Diagonal version of Mathlib's
`continuousOn_tangentCoordChange x y`; the diagonal is currently absent
in Mathlib v4.28.0. -/
theorem tangentBundle_continuousLinearMapAt_continuousAt_self
    (b₀ : X) :
    ContinuousAt (fun b : X => tangent_contLinMapAt (X := X) (E := E) b₀ b) b₀ := by
  sorry

/-- **Diagonal chart-overlap-derivative continuity, dual version (Mathlib gap).**
Companion to `tangentBundle_continuousLinearMapAt_continuousAt_self`. -/
theorem tangentBundle_symmL_continuousAt_self
    (b₀ : X) :
    ContinuousAt (fun b : X => tangent_symmL (X := X) (E := E) b₀ b) b₀ := by
  sorry

/-- Identification: the cotangent trivialization's fiber-second-component
equals the cotangent value composed with the tangent symmL. -/
private theorem trivCT_section_eq_comp_symmL
    (ω : HolomorphicOneForm E X) (b₀ b : X) :
    ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀)
        ⟨b, ω.toFun b⟩).snd =
      (cotangent_value ω b).comp (tangent_symmL b₀ b) := by
  rw [show (trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀) =
        (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).continuousLinearMap
          (RingHom.id ℂ)
          (trivializationAt ℂ (Bundle.Trivial X ℂ) b₀) from rfl,
      Trivialization.continuousLinearMap_apply]
  have hTrivial :
      (trivializationAt ℂ (Bundle.Trivial X ℂ) b₀).continuousLinearMapAt ℂ b =
        ContinuousLinearMap.id ℂ ℂ := by
    have heq : trivializationAt ℂ (Bundle.Trivial X ℂ) b₀ =
        Bundle.Trivial.trivialization X ℂ :=
      Bundle.Trivial.eq_trivialization X ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) b₀)
    have h₀ : (Bundle.Trivial.trivialization X ℂ).continuousLinearMapAt ℂ b
        = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ b
    have hbridge :
        (trivializationAt ℂ (Bundle.Trivial X ℂ) b₀).continuousLinearMapAt ℂ b =
          (Bundle.Trivial.trivialization X ℂ).continuousLinearMapAt ℂ b := by
      congr 1
    exact hbridge.trans h₀
  rw [hTrivial]
  rfl

/-- The trivialized cotangent section is operator-norm continuous at `b₀`. -/
private theorem ω_comp_symmL_continuousAt
    (ω : HolomorphicOneForm E X) (b₀ : X) :
    ContinuousAt (fun b : X =>
      (cotangent_value ω b).comp (tangent_symmL b₀ b)) b₀ := by
  have hb₀ :
      b₀ ∈ (trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (F := E →L[ℂ] ℂ)
      (E := CotangentSpace E X) b₀
  have hsmooth :
      ContMDiffAt (modelWithCornersSelf ℂ E) 𝓘(ℂ, E →L[ℂ] ℂ)
        (⊤ : WithTop ℕ∞)
        (fun b => ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀)
          ⟨b, ω.toFun b⟩).snd) b₀ :=
    ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀).contMDiffAt_section_iff
      hb₀).mp ω.contMDiff_toFun.contMDiffAt
  have hcont :
      ContinuousAt
        (fun b => ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀)
          ⟨b, ω.toFun b⟩).snd) b₀ :=
    hsmooth.continuousAt
  have heq : (fun b : X => ((trivializationAt (E →L[ℂ] ℂ) (CotangentSpace E X) b₀)
        ⟨b, ω.toFun b⟩).snd) =
      (fun b : X => (cotangent_value ω b).comp (tangent_symmL b₀ b)) := by
    funext b
    exact trivCT_section_eq_comp_symmL ω b₀ b
  rw [← heq]
  exact hcont

/-- The composition `cotangent_value ω b ∘ tangent_symmL b₀ b ∘ tangent_contLinMapAt b₀ b`
equals `cotangent_value ω b` on the trivialization's `baseSet`. -/
private theorem composition_eq_cotangent_value_on_baseSet
    (ω : HolomorphicOneForm E X) (b₀ b : X)
    (hb : b ∈ (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).baseSet) :
    ((cotangent_value ω b).comp (tangent_symmL b₀ b)).comp
      (tangent_contLinMapAt b₀ b) = cotangent_value ω b := by
  rw [ContinuousLinearMap.comp_assoc]
  have h_round : (tangent_symmL b₀ b).comp (tangent_contLinMapAt b₀ b)
      = ContinuousLinearMap.id ℂ E := by
    ext v
    exact Trivialization.symmL_continuousLinearMapAt _ hb v
  rw [h_round, ContinuousLinearMap.comp_id]

/-- **Main result.** The underlying function `b ↦ ω.toFun b : X → (E →L[ℂ] ℂ)`
of a holomorphic 1-form `ω` is continuous in the operator-norm topology. -/
theorem holomorphicOneForm_toFun_continuous
    (ω : HolomorphicOneForm E X) :
    Continuous (cotangent_value (X := X) (E := E) ω) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  have hsymmL_section := ω_comp_symmL_continuousAt ω b₀
  have hcontLinMapAt :=
    tangentBundle_continuousLinearMapAt_continuousAt_self (E := E) (X := X) b₀
  have hcomp_bilinear :
      Continuous (fun p : (E →L[ℂ] ℂ) × (E →L[ℂ] E) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp.continuous
  have hcomposed :
      ContinuousAt (fun b : X =>
        ((cotangent_value ω b).comp (tangent_symmL b₀ b)).comp
          (tangent_contLinMapAt b₀ b)) b₀ :=
    hcomp_bilinear.continuousAt.comp (hsymmL_section.prodMk hcontLinMapAt)
  have hbaseSet_nhd :
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).baseSet
        ∈ 𝓝 b₀ :=
    (trivializationAt E (TangentSpace (modelWithCornersSelf ℂ E)) b₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt'
        (F := E) (E := TangentSpace (modelWithCornersSelf ℂ E)) b₀)
  have h_round_trip :
      ∀ᶠ b in 𝓝 b₀,
        ((cotangent_value ω b).comp (tangent_symmL b₀ b)).comp
          (tangent_contLinMapAt b₀ b) = cotangent_value ω b := by
    filter_upwards [hbaseSet_nhd] with b hb
    exact composition_eq_cotangent_value_on_baseSet ω b₀ b hb
  exact hcomposed.congr h_round_trip

end JacobianChallenge.Periods
