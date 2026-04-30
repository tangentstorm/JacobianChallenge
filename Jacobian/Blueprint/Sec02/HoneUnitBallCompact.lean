import Jacobian.Blueprint.Sec02.MontelCompactness
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Sequences

/-! # Blueprint stub: `thm:hone-unit-ball-compact`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The closed unit ball of `(H⁰(X, Ω¹), ‖·‖)` is compact (topological
form). This is the consumer that feeds Riesz's theorem
(`thm:fd-from-riesz`).

Because `HolomorphicOneForm ℂ X` carries no canonical normed-space
instance in Mathlib, the statement is parameterised by an *abstract*
normed `ℂ`-vector space `H` together with a `ℂ`-linear bijection
`HolomorphicOneForm ℂ X ≃ₗ[ℂ] H` whose norm matches
`holomorphicSupNorm`. The conclusion is `IsCompact (Metric.closedBall
(0 : H) 1)`, which is the precise precondition of
`FiniteDimensional.of_isCompact_closedBall`.

The downstream worker should prove this as: take a sequence in the
closed ball, push it through `e.symm` to a sequence of holomorphic
1-forms with sup norm `≤ 1`, apply `montel_compactness` to extract a
sup-norm convergent subsequence, push the limit back through `e` to
exhibit the metric-convergent subsequence.

NOTE FOR WORKERS (the seq→topo bridge): `montel_compactness` returns
the **sequential** form `Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim)) atTop (𝓝 0)`.
The conclusion below — `IsCompact (Metric.closedBall (0 : H) 1)` — is
the **topological** form. The two are not the same theorem; in a
metric (hence first-countable) space they coincide via Mathlib's
`UniformSpace.isCompact_iff_isSeqCompact` or `IsSeqCompact.isCompact`.
You will need: (a) translate Montel's `Tendsto`-conclusion into
`IsSeqCompact (e '' { ω | holomorphicSupNorm X ω ≤ 1 })`, transporting
the sup-norm distance to `H`'s metric via `_h_norm`; (b) note that
`Metric.closedBall (0 : H) 1 = e '' { ω | holomorphicSupNorm X ω ≤ 1 }`
(same `_h_norm`); (c) apply `IsSeqCompact.isCompact`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Topological compactness of the closed unit ball of `H⁰(X, Ω¹)`,
parameterised by a normed-space realisation `H` of the section space
whose norm equals `holomorphicSupNorm`. -/
theorem hone_unit_ball_compact
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : HolomorphicOneForm ℂ X ≃ₗ[ℂ] H)
    (_h_norm : ∀ ω : HolomorphicOneForm ℂ X, ‖e ω‖ = holomorphicSupNorm X ω) :
    IsCompact (Metric.closedBall (0 : H) 1) := by
  suffices h : IsSeqCompact (Metric.closedBall (0 : H) 1) from h.isCompact
  intro v hv
  set ω : ℕ → HolomorphicOneForm ℂ X := fun n => e.symm (v n) with ω_def
  have hev : ∀ n, e (ω n) = v n := fun n => by
    simp [ω_def, e.apply_symm_apply]
  have hω_bd : ∀ n, holomorphicSupNorm X (ω n) ≤ 1 := by
    intro n
    rw [← _h_norm, hev n]
    simpa [Metric.mem_closedBall, dist_zero_right] using hv n
  obtain ⟨φ, hφ, ωlim, hlim_norm, htends⟩ := montel_compactness X ω hω_bd
  refine ⟨e ωlim, ?_, φ, hφ, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, _h_norm]
    exact hlim_norm
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq : (fun n => ‖(v ∘ φ) n - e ωlim‖)
        = (fun n => holomorphicSupNorm X (ω (φ n) - ωlim)) := by
      funext n
      have h1 : (v ∘ φ) n - e ωlim = e (ω (φ n) - ωlim) := by
        rw [Function.comp_apply, ← hev (φ n), ← map_sub]
      rw [h1, _h_norm]
    rw [heq]
    exact htends

end JacobianChallenge.Blueprint
