import Jacobian.HolomorphicForms.StageDipoleBoundary
import Jacobian.HolomorphicForms.StageEventualContainment
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Stage Dirichlet harmonic-solution interface

This module records the B2 statement-level Perron/Dirichlet solution payload
for the genus-zero engine.  It consumes the existing stage exhaustion,
eventual-containment, and dipole boundary-control interfaces, but deliberately
does not construct harmonic conjugates, holomorphic stage maps, or Montel
limits.

The payload shapes implement the S1–S7 statement repairs of
`docs/perron-b2-dirichlet-phase0.md` §2 under the manager's boundary lever
(§5 item 2): the harmonicity export is chartwise Mathlib
`InnerProductSpace.HarmonicOnNhd` (S2 = the B4 lane's R2 request), and the
pointwise frontier agreement is replaced by a maximum-principle inf/sup
bracket against the A4 boundary datum (S3-as-lever), which removes the
Poisson boundary-limit and barrier subtrees (W3d/W8) from the price of the
open obligation.
-/

namespace JacobianChallenge.HolomorphicForms

open Metric Set
open scoped Topology

/--
Derived-bridge harmonicity shape for one real stage potential.

This local-conjugate form is NOT a payload primitive: it is recoverable from
the chartwise `StageHarmonicOnNhd` field through the
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` funnel
(`docs/perron-b2-dirichlet-phase0.md` §3.8) — a chartwise harmonic reading
yields one analytic completion per chart ball, whose imaginary part is a
single conjugate witness on the whole ball preimage.  It is kept as the
consumer-facing bridge shape for the B4 conjugate lane.
-/
def StageHarmonicOn
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ} (marked : GenusZeroStageMarkedData X e)
    (stage : Set X) (potential : X → ℝ) : Prop :=
  ∀ x, x ∈ stage → x ≠ marked.P0 → x ≠ marked.Pinf →
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ stage ∧
      ∃ conjugate : X → ℝ,
        ∀ y, y ∈ U → IsHarmonicConjugateAtReal X potential conjugate y

/--
Chartwise neighborhood-uniform harmonicity for one real stage potential
(S2 repair = the B4 lane's R2 shape, `docs/perron-b2-dirichlet-phase0.md`
§2.3): at every stage point away from the two marked singular points, some
preferred-chart ball inside the stage carries Mathlib-side harmonicity of the
chart reading.

This is the shape every Perron construction step natively proves; the
per-point conjugate forms are one routine bridge downstream (§3.8).  Unlike
the per-point predicate it replaces, it cannot be satisfied by pointwise
real-differentiable junk with a different affine conjugate at each point.
-/
def StageHarmonicOnNhd
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ} (marked : GenusZeroStageMarkedData X e)
    (stage : Set X) (potential : X → ℝ) : Prop :=
  ∀ x, x ∈ stage → x ≠ marked.P0 → x ≠ marked.Pinf →
    ∃ r > 0, ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm '' ball ((chartAt ℂ x) x) r ⊆ stage ∧
      InnerProductSpace.HarmonicOnNhd
        (potential ∘ (chartAt ℂ x).symm) (ball ((chartAt ℂ x) x) r)

/--
Maximum-principle boundary bracket (the B2 boundary lever,
`docs/perron-b2-dirichlet-phase0.md` §5 item 2): away from the two marked
neighborhoods, the stage solution is trapped between the frontier `sInf` and
`sSup` of the A4 boundary datum up to a per-stage slack constant.

The bracket is restricted to `stage \ avoid` because the dipole poles make
any global two-sided bound false for the honest solution; off the marked
neighborhoods every Perron summand is bounded (Green caps off the pole
discs, envelope bracketing for the regular part), so the bracket is
deliverable WITHOUT the suspended boundary-limit/barrier subtree (W3d/W8).
Zero-slack frontier attainment is exactly the suspended barrier content;
pinning the slack uniformly in the stage index is the B3/D2 lane's job
(§3.6), not B2's.
-/
def StageBoundaryMaxBracket
    (X : Type*) [TopologicalSpace X]
    (stage avoid : Set X) (potential boundaryPotential : X → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ stage \ avoid,
    sInf (boundaryPotential '' frontier stage) - C ≤ potential x ∧
      potential x ≤ sSup (boundaryPotential '' frontier stage) + C

/--
The B2 Dirichlet/Perron solution payload for all bordered stages.

It packages one real solution per stage, chartwise neighborhood-uniform
harmonicity on the stage away from the marked singular points (S2/R2 shape),
the maximum-principle inf/sup bracket against the A4 boundary datum
(S3-as-lever, replacing pointwise frontier agreement), base normalization,
logarithmic singular behavior, and compact-subdomain bounds for later Cauchy
estimates.

`base_normalized` is retained under the lever (S4 resolution): the §2.4
over-determination needed pointwise boundary agreement (uniqueness pins
`u base` to a generically nonzero harmonic-measure average); with the
agreement clause replaced by a slack bracket, constant-shift freedom is
restored — `u - u base` satisfies every other field — so normalizing at the
base is consistent and keeps the downstream B5 coordinate formula
satisfiable.
-/
structure StageDirichletHarmonicSolution
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles) where
  harmonicPotential : ℕ → X → ℝ
  harmonicOnNhd_stage :
    ∀ n, StageHarmonicOnNhd X marked (exhaustion.stage n) (harmonicPotential n)
  boundary_maxBracket :
    ∀ n, StageBoundaryMaxBracket X (exhaustion.stage n)
      (marked.U0 ∪ marked.Uinf)
      (harmonicPotential n) (boundaryControl.boundaryPotential n)
  base_normalized :
    ∀ n, harmonicPotential n marked.base = 0
  has_pos_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.P0
      (harmonicPotential n) 1
  has_neg_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.Pinf
      (harmonicPotential n) (-1)
  compactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n) (harmonicPotential n)
  boundaryCompactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n)
      (boundaryControl.boundaryPotential n)
  boundaryCompactBound_eq :
    ∀ n, boundaryCompactBound n = boundaryControl.compactBound n

namespace StageDirichletHarmonicSolution

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}
variable {marked : GenusZeroStageMarkedData X e}
variable {selected : StageSelectedCompactFamily X}
variable {exhaustion : StageBorderedExhaustion X selected}
variable {profiles : GenusZeroStageDipoleProfiles X e marked}
variable {boundaryControl :
  StageDipoleBoundaryControl X e marked selected exhaustion profiles}

/-- The A4 boundary compact bounds are available from any B2 solution package. -/
theorem boundaryCompactBound_eq_boundaryControl
    (solution :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl)
    (n : ℕ) :
    solution.boundaryCompactBound n = boundaryControl.compactBound n := by
  exact solution.boundaryCompactBound_eq n

end StageDirichletHarmonicSolution

/--
B2 frontier obligation: solve the normalized stage Dirichlet/Perron problem
for the A4 boundary-control data.

This is intentionally narrower than the later harmonic-conjugate and
holomorphic-coordinate stages: it produces only real harmonic potentials with
maximum-principle boundary brackets, singular profile, normalization, and
compact-bound data.

The `IsManifold` hypothesis is the S5 repair: with arbitrary non-holomorphic
chart transitions, chartwise harmonicity does not transfer between preferred
charts, and no honest route to the payload exists.
-/
theorem exists_stageDirichletHarmonicSolution
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles) :
    Nonempty
      (StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl) := by
  sorry

end JacobianChallenge.HolomorphicForms
