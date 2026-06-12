import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Compactness.Compact
import Jacobian.HolomorphicForms.SectionFiberNorm

set_option linter.unusedSectionVars false

/-!
# Sup-norm of smooth sections over a compact base

This file defines the sup-norm of smooth sections of a normed vector bundle
over a compact base manifold, and proves the five basic algebraic properties
(zero, eq_zero_iff, triangle inequality, scalar bound, negation).

This is **Step 2** of the 5-step plan laid out in
`Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` for constructing
the Banach-space data on `HolomorphicOneForm ℂ X`.

## Main definitions

* `supNorm` — the sup-norm `⨆ x, ‖σ x‖` for a smooth section `σ`
  over a compact base.

## Main results

* `supNorm_zero` — `supNorm 0 = 0`
* `supNorm_eq_zero_iff` — `supNorm σ = 0 ↔ σ = 0` (requires `Nonempty M`)
* `supNorm_add_le` — triangle inequality
* `supNorm_smul_le` — `supNorm (c • σ) ≤ ‖c‖ * supNorm σ`
* `supNorm_neg` — `supNorm (-σ) = supNorm σ`
-/

namespace JacobianChallenge.HolomorphicForms.SectionSupNorm

open Bundle JacobianChallenge.HolomorphicForms.SectionFiberNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*}
variable [TopologicalSpace (TotalSpace F V)]
variable [∀ x, TopologicalSpace (V x)]
variable [FiberBundle F V]
variable [∀ x, NormedAddCommGroup (V x)]
variable [∀ x, NormedSpace 𝕜 (V x)]
variable [VectorBundle 𝕜 F V]

/--
The sup-norm of a smooth section over a compact base:
`supNorm σ = ⨆ x : M, ‖σ x‖`.
-/
noncomputable def supNorm (σ : ContMDiffSection I F ⊤ V) : ℝ :=
  ⨆ x : M, ‖σ.toFun x‖

/--
The compatibility hypothesis threaded through the sup-norm / metric API. It asserts
exactly the fact every `supNorm` axiom needs: the fiberwise norm of each smooth
section is **bounded above** on the (compact) base.

Historically this was stated as `∀ σ, Continuous (fiberNorm σ)` and `BddAbove` was
derived via `isCompact_univ.image`. But continuity of the fiberwise *operator* norm
is frame-dependent (it changes by the chart-transition factor) and, for the
cotangent bundle of a Riemann surface, only holds under the project's `StableChartAt`
adapter. Boundedness, by contrast, holds genuinely via a finite chart subcover (the
transition factors are bounded on compact overlaps) — so weakening the hypothesis to
`BddAbove` removes the `StableChartAt` dependence from the entire sup-norm / Banach
layer. Every downstream consumer used the continuity hypothesis ONLY to obtain this
`BddAbove`. -/
def SectionNormBddAbove (σ : ContMDiffSection I F ⊤ V) : Prop :=
  BddAbove (Set.range (fun x => ‖σ.toFun x‖))

omit [(x : M) → NormedSpace 𝕜 (V x)] [VectorBundle 𝕜 F V] in
/-- `BddAbove` of the fiberwise norm, directly from the (weaker) boundedness
hypothesis. (Previously derived from global continuity; see `SectionNormBddAbove`.) -/
theorem bddAbove_range_norm
    (hbdd : ∀ (σ : ContMDiffSection I F ⊤ V), SectionNormBddAbove (I := I) σ)
    (σ : ContMDiffSection I F ⊤ V) :
    BddAbove (Set.range (fun x => ‖σ.toFun x‖)) :=
  hbdd σ

omit [(x : M) → NormedSpace 𝕜 (V x)] [VectorBundle 𝕜 F V] in
/-- Bridge: global continuity of the fiberwise norm on a compact base gives the
boundedness witness. Provided so existing continuity-based providers still satisfy
the (weaker) `SectionNormBddAbove` API. The genuine goal is to supply
`SectionNormBddAbove` WITHOUT continuity (continuity of the operator fiber norm is
frame-dependent — see the project's `StableChartAt` discussion); this bridge keeps
the build green while that boundedness witness is built. -/
theorem sectionNormBddAbove_of_continuous
    (σ : ContMDiffSection I F ⊤ V)
    (hcont : Continuous (ContMDiffSection.fiberNorm (I := I) σ)) :
    SectionNormBddAbove (I := I) σ := by
  rw [SectionNormBddAbove, ← Set.image_univ]
  exact (isCompact_univ.image hcont).bddAbove

omit [CompactSpace M] in
theorem supNorm_zero :
    supNorm (I := I) (V := V) (0 : ContMDiffSection I F ⊤ V) = 0 := by
  unfold supNorm
  by_cases hM : Nonempty M
  · convert ciSup_const
    · exact norm_zero
    · exact hM
  · push Not at hM
    exact Real.iSup_of_isEmpty _

theorem supNorm_eq_zero_iff [Nonempty M]
    (hbdd : ∀ (σ : ContMDiffSection I F ⊤ V), SectionNormBddAbove (I := I) σ)
    (σ : ContMDiffSection I F ⊤ V) :
    supNorm σ = 0 ↔ σ = 0 := by
  constructor
  · intro h
    have h_le_zero : ∀ x : M, ‖σ.toFun x‖ ≤ 0 :=
      fun x => h ▸ le_ciSup (bddAbove_range_norm hbdd σ) x
    exact ContMDiffSection.ext fun x => norm_le_zero_iff.mp (h_le_zero x)
  · intro h
    exact h.symm ▸ supNorm_zero

theorem supNorm_add_le
    (hbdd : ∀ (σ : ContMDiffSection I F ⊤ V), SectionNormBddAbove (I := I) σ)
    (σ τ : ContMDiffSection I F ⊤ V) :
    supNorm (σ + τ) ≤ supNorm σ + supNorm τ := by
  by_cases hM : Nonempty M
  · exact ciSup_le fun x =>
      le_trans (norm_add_le _ _)
        (add_le_add (le_ciSup (bddAbove_range_norm hbdd σ) x)
          (le_ciSup (bddAbove_range_norm hbdd τ) x))
  · push Not at hM
    simp [supNorm, Real.iSup_of_isEmpty]

theorem supNorm_smul_le
    (hbdd : ∀ (σ : ContMDiffSection I F ⊤ V), SectionNormBddAbove (I := I) σ)
    (c : 𝕜) (σ : ContMDiffSection I F ⊤ V) :
    supNorm (c • σ) ≤ ‖c‖ * supNorm σ := by
  by_cases hM : Nonempty M
  · exact ciSup_le fun x =>
      le_trans (by convert norm_smul_le c (σ.toFun x) using 1)
        (mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_norm hbdd σ) x) (norm_nonneg c))
  · push Not at hM
    simp [supNorm, Real.iSup_of_isEmpty]

omit [CompactSpace M] in
theorem supNorm_neg (σ : ContMDiffSection I F ⊤ V) :
    supNorm (-σ) = supNorm σ := by
  exact iSup_congr fun x => norm_neg _

end JacobianChallenge.HolomorphicForms.SectionSupNorm
