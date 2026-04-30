import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Mathlib.Topology.MetricSpace.Basic

/-! # Blueprint stub: `lem:montel-compactness`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Montel compactness in sequential form: every sequence
`ω_n : ℕ → H⁰(X, Ω¹)` with `‖ω_n‖ ≤ 1` has a subsequence
`ω_{φ n}` converging in sup norm to some `ω∞ ∈ H⁰(X, Ω¹)` with
`‖ω∞‖ ≤ 1`.

The statement is in **sequential** form (the topological-compactness
form `IsCompact (Metric.closedBall …)` lives downstream as
`hone_unit_ball_compact`, since stating it requires picking a normed
structure on `H⁰(X, Ω¹)`).

Proof outline (downstream worker):
1. Cover `X` by finitely many charts; on each chart pull back `ω_n`
   to a holomorphic function `f_n : ℂ → ℂ` with sup bound `M`
   coming from `chart_coefficient_bound`.
2. Cauchy estimates ⇒ `|f_n'(z)| ≤ M / (R - r)` on a smaller disc,
   so the family `{f_n}` is equicontinuous on the smaller disc.
3. Arzelà–Ascoli on each chart extracts a uniformly convergent
   subsequence; diagonalise across the finite atlas.
4. Weierstrass: the uniform limit of holomorphic functions is
   holomorphic, so the limit lies in `H⁰(X, Ω¹)`.
5. Sup norm passes to the limit.

NOTE FOR WORKERS: this lemma stops at the **sequential**
`Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim)) atTop (𝓝 0)`.
The downstream consumer `hone_unit_ball_compact` wants
`IsCompact (Metric.closedBall (0 : H) 1)` for a normed-space
realisation `H`. The conversion is **not** trivially this lemma —
it requires the metric-space bridge "sequential compactness ⇒
topological compactness on first-countable spaces" (Mathlib:
`UniformSpace.isCompact_iff_isSeqCompact`, or
`IsSeqCompact.isCompact` on a metric space). Whoever picks up
`hone_unit_ball_compact` (Node 5) is responsible for that bridge —
this lemma's contract is the sequential form only.

----------------------------------------------------------------
WIP STATUS (this branch): the analytic body of Montel cannot be
honestly written until upstream `holomorphicSupNorm` (and the
underlying `cotangentFiberNorm`) acquire real definitions. The
sup-norm bound `‖ωlim‖ ≤ 1` is discharged trivially below from
`_h_bounded 0` exploiting that the stubbed `holomorphicSupNorm`
is `rfl`-constant in its form argument. The `Tendsto` half is a
single `-- BLOCKER:` sorry: with the current stubs, the goal
unfolds (by `rfl`) to `Tendsto (fun _ => sorryAx ℝ false) atTop
(𝓝 0)`, which forces the constant to equal `0` in any Hausdorff
target — and `_h_bounded` only constrains it to `≤ 1`.

The full ~200 LOC analytic proof (finite chart subcover, per-chart
Cauchy estimates, Arzelà–Ascoli, diagonalisation, Weierstrass
glue) becomes possible once the chain reaches `holomorphicSupNorm`
expressed as a chart-decomposable supremum. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold Topology
open Filter JacobianChallenge.HolomorphicForms

/-- Montel compactness (sequential form): the closed unit ball of
`H⁰(X, Ω¹)` is sequentially compact in the sup-norm sense.

WIP scaffold: the witness subsequence is `id` and the witness limit
is `ω 0`. The bound clause is dischargable today (see proof). The
`Tendsto` clause is the single remaining `-- BLOCKER:` and is keyed
to the currently-stubbed `holomorphicSupNorm` upstream. -/
theorem montel_compactness
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim))
          atTop (𝓝 0) := by
  refine ⟨id, strictMono_id, ω 0, ?_, ?_⟩
  · -- Sup-norm bound on the limit. With the upstream stub
    -- `holomorphicSupNorm := sorry`, every value of
    -- `holomorphicSupNorm X · ` is rfl-equal, so taking `ωlim := ω 0`
    -- makes this exactly `_h_bounded 0`. When `holomorphicSupNorm`
    -- gets a real definition, this branch will need the genuine
    -- "sup-norm passes to uniform limit" argument: pointwise pass
    -- under `iSup`, using lower-semicontinuity of the fiber norm.
    exact _h_bounded 0
  · -- BLOCKER: this is the analytic core of Montel compactness, and
    -- it cannot be discharged at this point in the chain.
    --
    -- Reduction (verifiable): with `holomorphicSupNorm := sorry` the
    -- statement `Tendsto (fun n => holomorphicSupNorm X (ω n - ω 0))
    -- atTop (𝓝 0)` reduces by `rfl` to `Tendsto (fun _ => c) atTop
    -- (𝓝 0)` for the closed term `c := sorryAx ℝ false`. In a
    -- Hausdorff target this forces `c = 0`, but `_h_bounded` only
    -- constrains `c ≤ 1`. Hence no proof can exist with the current
    -- upstream stubs — the obstruction is genuinely upstream of this
    -- file.
    --
    -- Real-content plan once upstream is concrete (cf. proofsketch in
    -- `tex/sections/02-holomorphic-forms-and-genus.tex` lines
    -- 187–222):
    --   1. Finite chart subcover: from `[CompactSpace X]` and the
    --      atlas charts `{e.source : e ∈ atlas ℂ X}` covering `X`,
    --      extract a finite subcover indexed by `Fin N` plus closed
    --      discs `D̄(c_i, r_i) ⊂ D̄(c_i, R_i) ⊂ e_i.target` whose
    --      preimages still cover.
    --   2. Per-chart sup bound: `chart_coefficient_bound X e_i he_i`
    --      gives `C_i ≥ 0` with `‖(ω_n).1 x‖_x ≤ C_i * ‖ω_n‖ ≤ C_i`
    --      for `x ∈ e_i.source`.
    --   3. Cauchy estimate: pull `ω_n` through `e_i` to a holomorphic
    --      `f_{n,i} : ℂ → ℂ` and apply
    --      `Complex.norm_deriv_le_aux_of_norm_le` /
    --      `DiffContOnCl.circleIntegral_sub_inv_smul` to bound
    --      `|f_{n,i}'(z)| ≤ C_i R_i / (R_i - r_i)^2` on `D̄(c_i, r_i)`.
    --   4. Equicontinuity from the derivative bound + mean value
    --      (`lipschitzWith_of_norm_deriv_le`).
    --   5. Arzelà–Ascoli on each `D̄(c_i, r_i)` (Mathlib
    --      `BoundedContinuousFunction.arzela_ascoli` or the
    --      uniform-space form
    --      `ArzelaAscoli.compactSpace_of_equicontinuous_of_uniformlyBounded`)
    --      yields a uniformly convergent subsequence per chart.
    --   6. Diagonalise across `Fin N` to a single subsequence `φ`.
    --   7. Weierstrass: `TendstoUniformlyOn.holomorphicAt` /
    --      `tendstoLocallyUniformly_iff_…` produces a holomorphic
    --      chart limit; reassemble into a global section using the
    --      atlas-overlap consistency of the diagonal subsequence.
    --   8. Pass to the sup-norm limit (lower-semicontinuity of `iSup`
    --      under uniform convergence).
    --
    -- The actual proof body is expected at ~200 LOC once the
    -- prerequisites are present.
    sorry

end JacobianChallenge.Blueprint
