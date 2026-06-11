import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Real-part maximum principle for stage potentials (Perron engine B3a)

Blueprint node: `lem:stage-harmonic-max-principle`.

The Perron stage construction needs harmonic potentials to be bounded on
compact subdomains by their boundary data (phase-1 plan §B3).  In the
project's conjugate-pair language a harmonic potential `u` on a planar
domain comes with `f = u + I·v` holomorphic, and the classical route is
the exponential trick: `‖exp (f z)‖ = Real.exp (re (f z))`, so Mathlib's
maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) bounds `re f` inside a
bounded domain by its frontier bound.

Outputs: the core real-part bound, the two-sided version, the disc form
with sphere boundary (the Cauchy-circle shape D2 consumes), and the
conjugate-pair form (the exact shape in which B2/B4 stage solutions carry
their data).  Pure Mathlib-leaf composition — no stage dependencies.
-/

namespace JacobianChallenge.HolomorphicForms

open Set Metric Bornology

/--
**Real-part maximum principle.** If `f` is holomorphic on a bounded
planar domain and continuous up to the closure, then `re f` is bounded on
the closure by any bound valid on the frontier: apply the maximum modulus
principle to `exp ∘ f`, whose norm is `Real.exp (re (f ·))`.
-/
theorem re_le_of_forall_mem_frontier_re_le
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ f U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, (f z).re ≤ M) :
    ∀ z ∈ closure U, (f z).re ≤ M := by
  intro z hz
  have hexp : DiffContOnCl ℂ (fun w => Complex.exp (f w)) U :=
    Complex.differentiable_exp.comp_diffContOnCl hf
  have hbound : ∀ w ∈ frontier U, ‖Complex.exp (f w)‖ ≤ Real.exp M := by
    intro w hw
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hM w hw)
  have hin : ‖Complex.exp (f z)‖ ≤ Real.exp M :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hU hexp hbound hz
  rw [Complex.norm_exp] at hin
  exact Real.exp_le_exp.mp hin

/--
Two-sided version: a frontier bound on `|re f|` controls `|re f|` on the
closure (apply the one-sided bound to `f` and `-f`).
-/
theorem abs_re_le_of_forall_mem_frontier_abs_re_le
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ f U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, |(f z).re| ≤ M) :
    ∀ z ∈ closure U, |(f z).re| ≤ M := by
  intro z hz
  rw [abs_le]
  constructor
  · have hneg : ∀ w ∈ frontier U, ((-f) w).re ≤ M := by
      intro w hw
      have := (abs_le.mp (hM w hw)).1
      simpa using neg_le.mp this
    have := re_le_of_forall_mem_frontier_re_le hU hf.neg hneg z hz
    simpa using neg_le.mp (by simpa using this)
  · exact re_le_of_forall_mem_frontier_re_le hU hf
      (fun w hw => (abs_le.mp (hM w hw)).2) z hz

/--
Disc form: on a closed disc of positive radius, `re f` is bounded by its
bound on the boundary circle — the Cauchy-circle shape consumed by the
uniform chart-ball estimates (phase-1 plan §D2).
-/
theorem re_le_on_closedBall_of_sphere_re_le
    {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (Metric.ball z₀ r)) {M : ℝ}
    (hM : ∀ z ∈ Metric.sphere z₀ r, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall z₀ r, (f z).re ≤ M := by
  intro z hz
  have hfront : frontier (Metric.ball z₀ r) = Metric.sphere z₀ r :=
    frontier_ball z₀ hr.ne'
  have hM' : ∀ w ∈ frontier (Metric.ball z₀ r), (f w).re ≤ M := by
    rw [hfront]; exact hM
  have hcl : z ∈ closure (Metric.ball z₀ r) := by
    rw [closure_ball z₀ hr.ne']; exact hz
  exact re_le_of_forall_mem_frontier_re_le isBounded_ball hf hM' z hcl

/--
Conjugate-pair form — the exact shape in which the stage Dirichlet
solutions carry their data: a real potential `u` with conjugate `v` such
that `u + I·v` is holomorphic on the bounded domain and continuous up to
the closure is bounded on the closure by its frontier bound.
-/
theorem re_bound_of_conjugate_pair
    {u v : ℂ → ℝ} {U : Set ℂ} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ
      (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, u z ≤ M) :
    ∀ z ∈ closure U, u z ≤ M := by
  have hre : ∀ z : ℂ, ((u z : ℂ) + Complex.I * (v z : ℂ)).re = u z := by
    intro z
    simp [Complex.add_re, Complex.mul_re]
  intro z hz
  have := re_le_of_forall_mem_frontier_re_le hU hf
    (fun w hw => by rw [hre]; exact hM w hw) z hz
  rwa [hre] at this

end JacobianChallenge.HolomorphicForms
