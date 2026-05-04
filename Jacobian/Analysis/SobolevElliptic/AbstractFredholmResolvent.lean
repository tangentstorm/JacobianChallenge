import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
-- (Operator norm comes transitively via the imports above; no
-- direct import needed.)

/-!
# Phase 2.2 — Abstract Fredholm-resolvent framework

The dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 3) routes the headline `Module.Finite ℝ (ker Δ)` through the
*spectral* shortcut: `(Δ + 1)⁻¹` compact ⇒ each non-zero spectral
value has finite-dimensional eigenspace ⇒ `ker Δ` finite-dim.

This file isolates the **abstract** spectral consequence — the
Riesz / Hilbert-Schmidt argument — completely independent of any
manifold construction.  The argument: if `T : H →L[ℝ] H` is a
*compact* operator on a real normed space and `λ ≠ 0` is in its
spectrum, then `ker (T - λ • 1)` is finite-dimensional.

Concretely: the eigenspace `V := ker (T - λ • 1)` carries the action
`T |_V = λ • id_V`, so the closed unit ball in `V` (viewed as a
subset of `H`) sits inside the compact set `λ⁻¹ • T(B_H)`.  By
Riesz' theorem (`FiniteDimensional.of_isCompact_closedBall₀`),
`V` is finite-dimensional.

This is the irreducible analytic content of the Galerkin route.
**No `sorry`, no `True`-valued bodies.**

The downstream R10 plug-in (Phase 4) instantiates `H := L²(M, μ)`,
`T := (Δ + 1)⁻¹`, `λ := 1` (since `Δ f = 0 ↔ T f = f`).  The Lean
definitions for `T` and the analytic input "T is compact" are still
to be supplied (Phase 3); this file proves the spectral output is
*automatic* once those are in place.

## Mathlib hooks used

* `Mathlib/Analysis/Normed/Operator/Compact.lean` — `IsCompactOperator`,
  `IsCompactOperator.image_closedBall_subset_compact`.
* `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` —
  `FiniteDimensional.of_isCompact_closedBall₀` (Riesz' theorem).
-/

namespace JacobianChallenge.Analysis.SobolevElliptic

set_option linter.unusedSectionVars false

open Set Metric

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ### The eigenspace at a nonzero scalar -/

/-- The eigenspace of `T : H →L[ℝ] H` at a scalar `λ`: the closed
linear subspace `{v : T v = λ • v}`. -/
def Eigenspace (T : H →L[ℝ] H) (lam : ℝ) : Submodule ℝ H :=
  LinearMap.ker (T.toLinearMap - lam • LinearMap.id)

@[simp]
theorem mem_Eigenspace {T : H →L[ℝ] H} {lam : ℝ} {v : H} :
    v ∈ Eigenspace T lam ↔ T v = lam • v := by
  simp [Eigenspace, sub_eq_zero, LinearMap.sub_apply, ContinuousLinearMap.coe_coe]

/-- On the eigenspace at `λ`, `T` acts by scalar multiplication by `λ`. -/
theorem Eigenspace.apply_eq {T : H →L[ℝ] H} {lam : ℝ} {v : H}
    (hv : v ∈ Eigenspace T lam) : T v = lam • v := mem_Eigenspace.mp hv

/-- The eigenspace, viewed as a set of `H`, is closed. -/
theorem Eigenspace.isClosed (T : H →L[ℝ] H) (lam : ℝ) :
    IsClosed (Eigenspace T lam : Set H) := by
  -- `{v : H | T v = λ • v} = (T - λ • id)⁻¹' {0}`.
  have hcont : Continuous fun v : H => T v - lam • v :=
    T.continuous.sub (continuous_const.smul continuous_id)
  have h_eq : (Eigenspace T lam : Set H) =
      {v : H | T v - lam • v = 0} := by
    ext v
    simp [SetLike.mem_coe, mem_Eigenspace, sub_eq_zero]
  rw [h_eq]
  exact isClosed_eq hcont continuous_const

/-! ### The closed unit ball of the eigenspace, viewed in `H`, is compact -/

/-- **Key lemma.**  For a compact operator `T` and a nonzero scalar
`λ`, the set `{v ∈ H : T v = λ • v ∧ ‖v‖ ≤ 1}` is compact in `H`.

Proof: every such `v` satisfies `v = λ⁻¹ • T v` and `‖λ⁻¹ • v‖ ≤
1 / |λ|`, so `v ∈ T(closedBall 0 (1/|λ|))`, which is contained in a
compact set `K` by `IsCompactOperator.image_closedBall_subset_compact`.
The set is also closed (intersection of the closed eigenspace with
the closed ball).  Closed subset of compact is compact. -/
theorem isCompact_eigenspace_inter_ball
    {T : H →L[ℝ] H} (hT : IsCompactOperator T)
    {lam : ℝ} (hlam : lam ≠ 0) :
    IsCompact ((Eigenspace T lam : Set H) ∩ Metric.closedBall (0 : H) 1) := by
  obtain ⟨K, hK, hKsub⟩ := hT.image_closedBall_subset_compact (1 / |lam|)
  -- Inclusion into `K`:
  have h_sub :
      ((Eigenspace T lam : Set H) ∩ Metric.closedBall (0 : H) 1) ⊆ K := by
    rintro v ⟨hvE, hvB⟩
    have hTv : T v = lam • v := mem_Eigenspace.mp hvE
    have hv_norm : ‖v‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hvB
    -- We exhibit `v` as `T (lam⁻¹ • v)`, with `lam⁻¹ • v ∈ closedBall (0 : H) (1/|λ|)`.
    have habs : 0 < |lam| := abs_pos.mpr hlam
    have hsub : (lam⁻¹ • v) ∈ Metric.closedBall (0 : H) (1 / |lam|) := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
                 abs_inv, one_div]
      calc |lam|⁻¹ * ‖v‖
          ≤ |lam|⁻¹ * 1 := by
            apply mul_le_mul_of_nonneg_left hv_norm
            exact inv_nonneg.mpr habs.le
        _ = |lam|⁻¹ := mul_one _
    have hT_in : T (lam⁻¹ • v) ∈ K := hKsub ⟨lam⁻¹ • v, hsub, rfl⟩
    have hTeq : T (lam⁻¹ • v) = v := by
      rw [map_smul, hTv, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [← hTeq]; exact hT_in
  -- Closedness: intersection of closed eigenspace with closed ball.
  have h_closed :
      IsClosed ((Eigenspace T lam : Set H) ∩ Metric.closedBall (0 : H) 1) :=
    (Eigenspace.isClosed T lam).inter Metric.isClosed_closedBall
  -- Closed subset of compact is compact.
  exact hK.of_isClosed_subset h_closed h_sub

/-! ### Closed-ball compactness inside the eigenspace -/

/-- The closed unit ball of the eigenspace `Eigenspace T lam`,
viewed inside the subspace topology, is compact (under the same
hypotheses as `isCompact_eigenspace_inter_ball`). -/
theorem isCompact_closedBall_eigenspace
    {T : H →L[ℝ] H} (hT : IsCompactOperator T)
    {lam : ℝ} (hlam : lam ≠ 0) :
    IsCompact (Metric.closedBall (0 : Eigenspace T lam) 1) := by
  -- The subtype inclusion `(↑)` is a topological embedding (subspace topology).
  have h_emb : Topology.IsEmbedding (Subtype.val : Eigenspace T lam → H) :=
    Topology.IsEmbedding.subtypeVal
  -- Image of the closed unit ball under `(↑)`.
  have h_image :
      Subtype.val '' Metric.closedBall (0 : Eigenspace T lam) 1 =
        (Eigenspace T lam : Set H) ∩ Metric.closedBall (0 : H) 1 := by
    ext x
    constructor
    · rintro ⟨⟨v, hv⟩, hball, rfl⟩
      refine ⟨hv, ?_⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    · rintro ⟨hxE, hxB⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hxB
  rw [h_emb.isCompact_iff, h_image]
  exact isCompact_eigenspace_inter_ball hT hlam

/-! ### Finite-dimensionality of the eigenspace -/

/-- **Headline (Phase 2.2).**  The eigenspace of a compact operator
at a *nonzero* scalar is finite-dimensional.

This is the irreducible analytic step of the Galerkin / spike-
solution route to R10's headline finite-dim-kernel claim.  The
proof: the closed unit ball of the eigenspace (in the subspace
topology) is compact (`isCompact_closedBall_eigenspace`); Riesz'
theorem (`FiniteDimensional.of_isCompact_closedBall₀`) concludes
finite-dimensionality.

When this is plugged into Phase 4 with `T := (Δ + 1)⁻¹` and
`λ := 1`, we get `ker Δ = Eigenspace T 1` finite-dim, the headline
of R10. -/
theorem finiteDimensional_eigenspace_of_compact
    {T : H →L[ℝ] H} (hT : IsCompactOperator T)
    {lam : ℝ} (hlam : lam ≠ 0) :
    FiniteDimensional ℝ (Eigenspace T lam) :=
  FiniteDimensional.of_isCompact_closedBall₀ ℝ (one_pos)
    (isCompact_closedBall_eigenspace hT hlam)

/-- **Module.Finite version.**  Equivalent reformulation of the
headline in terms of `Module.Finite`, which is the form consumed by
the R10 statement bank
(`JacobianChallenge.Analysis.SobolevElliptic.sobolev_elliptic_overview`). -/
theorem moduleFinite_eigenspace_of_compact
    {T : H →L[ℝ] H} (hT : IsCompactOperator T)
    {lam : ℝ} (hlam : lam ≠ 0) :
    Module.Finite ℝ (Eigenspace T lam) :=
  have : FiniteDimensional ℝ (Eigenspace T lam) :=
    finiteDimensional_eigenspace_of_compact hT hlam
  inferInstance

end JacobianChallenge.Analysis.SobolevElliptic
