import Jacobian.HolomorphicForms.PerronPoissonBoundary
import Jacobian.HolomorphicForms.PerronRemovableSingularity
import Jacobian.HolomorphicForms.PerronHarmonicMaxPrinciple

/-!
# W6 adapters: the obligations discharged, and the unconditional theorems (Perron engine B2 toolbox)

Blueprint node: `lem:perron-removable-singularity` (W6 of
`docs/perron-b2-dirichlet-phase0.md` §4); tracking #232.

`DiscDirichletInput`, the W3 named obligation of the W6
removable-singularity file, is exactly the solvability of the disc
Dirichlet problem for continuous circle data — which is what jc6's W3d
M4 closed-ball packaging (`PerronPoissonBoundary.lean`) provides.  This
file is the thin consumer adapter: zero analytical content, pure
obtain-and-apply.  The witness is `poissonSolution g c r`; harmonicity
on the open ball is `poissonSolution_harmonicOnNhd`, continuity on the
closed ball is `continuousOn_poissonSolution`, and the sphere `EqOn` is
the extension's off-ball branch (`poissonSolution_apply_of_mem_sphere`).

With both named obligations discharged — `DiscDirichletInput` here,
`WeakMaxPrincipleInput` by jc3's `weakMaxPrincipleInput_holds`
(`PerronHarmonicMaxPrinciple.lean`) — the second half of this file
states the three W6 theorems hypothesis-free (primed names, following
the W1-sweep convention of `PerronSubOn.lean`); the parametric
originals in `PerronRemovableSingularity.lean` are retained for
consumers that thread obligation terms.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter InnerProductSpace Metric
open scoped Topology

/--
The disc Dirichlet problem is solvable for continuous circle data:
the W3 obligation of the W6 removable-singularity file, discharged by
jc6's W3d M4 closed-ball Dirichlet packaging.
-/
theorem discDirichletInput_of_poissonOperator : DiscDirichletInput :=
  fun c r hr g hg =>
    ⟨poissonSolution g c r, poissonSolution_harmonicOnNhd hr hg,
      continuousOn_poissonSolution hr hg,
      fun _ hz => poissonSolution_apply_of_mem_sphere hz⟩

/-! ### The unconditional W6 theorems

The three main theorems of `PerronRemovableSingularity.lean` with both
named obligations supplied: `weakMaxPrincipleInput_holds` (W1, jc3) and
`discDirichletInput_of_poissonOperator` (W3, above). -/

/--
**Annuli comparison, hypothesis-free (W6).**  A harmonic function on
the punctured ball, bounded there, agrees on the punctured inner ball
with every disc-Dirichlet solution of its inner-circle restriction.
-/
theorem eq_dirichletSolution_of_bounded_punctured'
    {u h : ℂ → ℝ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOnNhd u (ball c R \ {c}))
    (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M)
    (hh : HarmonicOnNhd h (ball c r))
    (hhc : ContinuousOn h (closedBall c r))
    (hagree : Set.EqOn h u (sphere c r)) :
    Set.EqOn u h (ball c r \ {c}) :=
  eq_dirichletSolution_of_bounded_punctured weakMaxPrincipleInput_holds
    hr hrR hu hbd hh hhc hagree

/--
**Bounded-harmonic removable singularity, hypothesis-free (W6 main
theorem).**  A harmonic function on the punctured ball, bounded there,
extends harmonically across the puncture.
-/
theorem harmonicOnNhd_extend_of_bounded_punctured'
    {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (ball c R \ {c}))
    {M : ℝ} (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M) :
    ∃ v : ℂ → ℝ, HarmonicOnNhd v (ball c R) ∧
      Set.EqOn v u (ball c R \ {c}) :=
  harmonicOnNhd_extend_of_bounded_punctured weakMaxPrincipleInput_holds
    discDirichletInput_of_poissonOperator hR hu hbd

/--
**Limit corollary, hypothesis-free (W6).**  A bounded harmonic function
on the punctured ball has a limit at the puncture.
-/
theorem exists_tendsto_of_bounded_punctured'
    {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (ball c R \ {c}))
    {M : ℝ} (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M) :
    ∃ L : ℝ, Tendsto u (𝓝[ball c R \ {c}] c) (𝓝 L) :=
  exists_tendsto_of_bounded_punctured weakMaxPrincipleInput_holds
    discDirichletInput_of_poissonOperator hR hu hbd

end JacobianChallenge.HolomorphicForms
