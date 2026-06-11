import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.Topology.Order.Lattice
import Jacobian.HolomorphicForms.PerronRemovableSingularity
import Jacobian.HolomorphicForms.PerronPoissonBoundary

/-!
# The Perron comparison subclass `PerronSubOn` (B2 toolbox W5a)

Blueprint node: `def:perron-sub-on`.

B2 Dirichlet toolbox leaf W5 (`docs/perron-b2-dirichlet-phase0.md` §3.2 +
§4 row W5).  Perron's method does **not** require an
upper-semicontinuous subharmonic theory (Riesz representation, polar
sets, fine topology): nothing downstream in the genus-zero engine
consumes it.  All it needs is a *continuous comparison subclass* — the
class of continuous functions that lie below every harmonic majorant on
every disc.  This file defines that class and proves the two facts that
have **no** dependency on the rest of the toolbox: the definition itself,
its continuity accessor, and closure under `max`.

## Design: the disc-comparison form lives on `ℂ`

The §3.2 phrase "preferred-chart closed disc `D̄ ⊆ V`" describes the
*application context* (in the stage construction `V` is a chart image),
but the comparison itself is a purely planar statement about discs in
`ℂ`.  The toolbox lemmas W1–W4 are all pure-`ℂ`
(`PerronHarnack.lean`, `PerronStageMaxPrinciple.lean`), and the W7
envelope reads chart **pullbacks** `v ∘ (chartAt ℂ x).symm` on balls in
`ℂ`.  So `PerronSubOn` is defined for `v : ℂ → ℝ` on an open `V ⊆ ℂ`,
with honest `Metric.closedBall c R ⊆ V` discs; the chart / `IsManifold`
machinery is isolated in the gated chart-transfer lemma (W5c, consuming
`HarmonicAt.comp_analyticAt` from `PerronStageHarmonicCompose.lean`).

The comparison majorant `h` is packaged with Mathlib's
`HarmonicContOnCl h (Metric.ball c R)`
(`Mathlib/Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean`),
which bundles exactly "`h` harmonic on the open disc, continuous on its
closure `= D̄`".

## Scope of this file (un-gated, sorry-free)

- the definition + its `ContinuousOn` accessor;
- closure under `max` (pure logic + `ContinuousOn.sup`).

Harmonic-membership (a harmonic function is a member) and the
Poisson-modification / chart-transfer lemmas are **gated**: membership
reduces to the harmonic maximum principle (toolbox W1, in flight in
jc10's lane), so it is deferred to the W5b follow-up and integrated by
import when W1 lands — it is deliberately *not* stubbed here.
-/

namespace JacobianChallenge.HolomorphicForms

open Metric Set InnerProductSpace

/--
**B2 toolbox W5.** The continuous Perron comparison subclass.

A function `v` continuous on the open set `V ⊆ ℂ` is `PerronSubOn V` iff
on every closed disc `closedBall c R ⊆ V` (with `0 < R`) it lies below
every comparison function `h` that is harmonic on the open disc,
continuous up to its closure (`HarmonicContOnCl h (ball c R)`), and
dominates `v` on the bounding circle `sphere c R`.

This is the disc-comparison ("sub-the-harmonics") characterisation that
replaces upper-semicontinuous subharmonicity in the Perron construction:
harmonic functions are members, the class is closed under `max` and
Poisson modification, and the envelope `sup` of a bounded family of
members is harmonic — none of which needs the full subharmonic theory.
-/
def PerronSubOn (v : ℂ → ℝ) (V : Set ℂ) : Prop :=
  ContinuousOn v V ∧
    ∀ ⦃c : ℂ⦄ ⦃R : ℝ⦄, 0 < R → Metric.closedBall c R ⊆ V →
      ∀ ⦃h : ℂ → ℝ⦄, HarmonicContOnCl h (Metric.ball c R) →
        (∀ z ∈ Metric.sphere c R, v z ≤ h z) →
        ∀ z ∈ Metric.ball c R, v z ≤ h z

/-- Members of `PerronSubOn V` are continuous on `V`. -/
theorem PerronSubOn.continuousOn {v : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) : ContinuousOn v V :=
  hv.1

/-- The pointwise comparison clause of `PerronSubOn` membership. -/
theorem PerronSubOn.le_on_ball {v : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ V) {h : ℂ → ℝ}
    (hh : HarmonicContOnCl h (Metric.ball c R))
    (hbd : ∀ z ∈ Metric.sphere c R, v z ≤ h z) :
    ∀ z ∈ Metric.ball c R, v z ≤ h z :=
  hv.2 hR hsub hh hbd

/--
**Closure under `max` (B2 toolbox W5a).** The pointwise maximum of two
`PerronSubOn V` members is again a member.

No maximum principle is needed: from `max (v₁ z) (v₂ z) ≤ h z` on the
circle we get `vᵢ z ≤ h z` there (each summand is `≤` the max), each
member's comparison clause then gives `vᵢ ≤ h` on the disc, and `max_le`
recombines.  Continuity is `ContinuousOn.sup`.
-/
theorem PerronSubOn.max {v₁ v₂ : ℂ → ℝ} {V : Set ℂ}
    (h₁ : PerronSubOn v₁ V) (h₂ : PerronSubOn v₂ V) :
    PerronSubOn (fun z => max (v₁ z) (v₂ z)) V := by
  refine ⟨h₁.1.sup h₂.1, ?_⟩
  intro c R hR hsub h hh hbd z hz
  have hbd₁ : ∀ w ∈ Metric.sphere c R, v₁ w ≤ h w := fun w hw =>
    (le_max_left (v₁ w) (v₂ w)).trans (hbd w hw)
  have hbd₂ : ∀ w ∈ Metric.sphere c R, v₂ w ≤ h w := fun w hw =>
    (le_max_right (v₁ w) (v₂ w)).trans (hbd w hw)
  exact max_le (h₁.2 hR hsub hh hbd₁ z hz) (h₂.2 hR hsub hh hbd₂ z hz)

/--
**Restriction to a smaller open (B2 toolbox W5a).** `PerronSubOn`
membership descends to any subset `W ⊆ V`: every closed disc inside `W`
is a closed disc inside `V`, so the comparison clause is inherited, and
continuity restricts by `ContinuousOn.mono`.

Consumed by the Green's-function families (members built on a component
and restricted to the puncture) and by the envelope locality step
(restrict a member to a chart disc before Poisson modification).
-/
theorem PerronSubOn.mono {v : ℂ → ℝ} {V W : Set ℂ}
    (hv : PerronSubOn v V) (hWV : W ⊆ V) : PerronSubOn v W := by
  refine ⟨hv.1.mono hWV, ?_⟩
  intro c R hR hsub h hh hbd z hz
  exact hv.2 hR (hsub.trans hWV) hh hbd z hz

/--
**Transfer along pointwise equality (B2 toolbox W5a).** `PerronSubOn`
membership is invariant under changing the function on a set off `V`:
if `g = v` on `V` then `PerronSubOn v V → PerronSubOn g V`.  Every point
the comparison clause quantifies over lies in `V` (`ball c R` and
`sphere c R` are inside `closedBall c R ⊆ V`), so the boundary hypothesis
and the conclusion rewrite through the equality.

Lets the family members of §3.3/§3.4 — defined by gluing and extension —
be reasoned about up to their on-domain values.
-/
theorem PerronSubOn.congr {v g : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) (hgv : Set.EqOn g v V) : PerronSubOn g V := by
  refine ⟨hv.1.congr hgv, ?_⟩
  intro c R hR hsub h hh hbd z hz
  have hsphereV : Metric.sphere c R ⊆ V :=
    Metric.sphere_subset_closedBall.trans hsub
  have hballV : Metric.ball c R ⊆ V :=
    Metric.ball_subset_closedBall.trans hsub
  have hbd' : ∀ w ∈ Metric.sphere c R, v w ≤ h w := fun w hw => by
    rw [← hgv (hsphereV hw)]; exact hbd w hw
  have hle := hv.2 hR hsub hh hbd' z hz
  rwa [hgv (hballV hz)]

/--
**Harmonic-membership (B2 toolbox W5b).** A function harmonic on the open
set `V ⊆ ℂ` is a `PerronSubOn V` member — modulo the harmonic weak
maximum principle, supplied as the `WeakMaxPrincipleInput` obligation
(`PerronRemovableSingularity.lean`; owner lane jc10's W1).  This is the
first membership fact every Perron envelope (Green's functions §3.3,
`H[g]` §3.4) consumes: the envelopes are sups of members, and harmonic
functions are the basic members.

On a disc `closedBall c R ⊆ V` with majorant `h'`
(`HarmonicContOnCl h' (ball c R)`, `h ≤ h'` on `sphere c R`), the
difference `w := h - h'` is harmonic on `ball c R`, continuous on its
closure `closedBall c R`, and `≤ 0` on
`frontier (ball c R) = sphere c R`; the maximum principle forces `w ≤ 0`
inside, i.e. `h ≤ h'` on `ball c R`.

When jc10 lands `WeakMaxPrincipleInput` as a proved fact, every call site
discharges `hmax` trivially. -/
theorem PerronSubOn.of_harmonicOnNhd
    (hmax : WeakMaxPrincipleInput) {h : ℂ → ℝ} {V : Set ℂ}
    (hh : HarmonicOnNhd h V) : PerronSubOn h V := by
  refine ⟨continuousOn_of_harmonicOnNhd hh, ?_⟩
  intro c R hR hsub h' hh' hbd z hz
  have hRne : R ≠ 0 := ne_of_gt hR
  have hballV : Metric.ball c R ⊆ V :=
    Metric.ball_subset_closedBall.trans hsub
  -- `w := h - h'` is harmonic on the open ball.
  have hwHarm : HarmonicOnNhd (fun x => h x - h' x) (Metric.ball c R) :=
    (hh.mono hballV).sub hh'.harmonicOnNhd
  -- `w` is continuous up to the closed ball = closure of the open ball.
  have hhCont : ContinuousOn h (Metric.closedBall c R) :=
    (hh.mono hsub).continuousOn
  have hwCont : ContinuousOn (fun x => h x - h' x)
      (closure (Metric.ball c R)) := by
    rw [closure_ball c hRne]
    exact hhCont.sub hh'.continuousOn_ball
  -- `w ≤ 0` on the frontier circle.
  have hfront : ∀ ζ ∈ frontier (Metric.ball c R), (fun x => h x - h' x) ζ ≤ 0 := by
    intro ζ hζ
    rw [frontier_ball c hRne] at hζ
    exact sub_nonpos.mpr (hbd ζ hζ)
  -- The maximum principle forces `w ≤ 0` inside.
  have hw := hmax (Metric.ball c R) (fun x => h x - h' x)
    Metric.isOpen_ball Metric.isBounded_ball hwHarm hwCont hfront z hz
  exact sub_nonpos.mp hw

/--
**Two-harmonic disc comparison (B2 toolbox W5b).** If `h₁`, `h₂` are
harmonic on the open disc `ball c R`, continuous up to its closure, and
`h₁ ≤ h₂` on the bounding circle `sphere c R`, then `h₁ ≤ h₂` throughout
`ball c R` — modulo the harmonic weak maximum principle
(`WeakMaxPrincipleInput`, jc10's W1 obligation).

This is the applied disc form of the maximum principle the Perron
envelope and Green's-function upper bounds (§3.3) consume: the difference
`w := h₁ - h₂` is harmonic on `ball c R`, continuous on its closure
`closedBall c R`, and `≤ 0` on `frontier (ball c R) = sphere c R`, so the
weak maximum principle forces `w ≤ 0` inside.

The symmetric two-`HarmonicContOnCl` companion to
`PerronSubOn.of_harmonicOnNhd` (there the lower function is only a
`PerronSubOn` member; here both are continuous up to the closure). -/
theorem harmonicContOnCl_le_of_le_on_sphere
    (hmax : WeakMaxPrincipleInput) {h₁ h₂ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hh₁ : HarmonicContOnCl h₁ (Metric.ball c R))
    (hh₂ : HarmonicContOnCl h₂ (Metric.ball c R))
    (hbd : ∀ z ∈ Metric.sphere c R, h₁ z ≤ h₂ z) :
    ∀ z ∈ Metric.ball c R, h₁ z ≤ h₂ z := by
  intro z hz
  have hRne : R ≠ 0 := ne_of_gt hR
  have hwHarm : HarmonicOnNhd (fun x => h₁ x - h₂ x) (Metric.ball c R) :=
    hh₁.harmonicOnNhd.sub hh₂.harmonicOnNhd
  have hwCont : ContinuousOn (fun x => h₁ x - h₂ x)
      (closure (Metric.ball c R)) := by
    rw [closure_ball c hRne]
    exact hh₁.continuousOn_ball.sub hh₂.continuousOn_ball
  have hfront : ∀ ζ ∈ frontier (Metric.ball c R), (fun x => h₁ x - h₂ x) ζ ≤ 0 := by
    intro ζ hζ
    rw [frontier_ball c hRne] at hζ
    exact sub_nonpos.mpr (hbd ζ hζ)
  have hw := hmax (Metric.ball c R) (fun x => h₁ x - h₂ x)
    Metric.isOpen_ball Metric.isBounded_ball hwHarm hwCont hfront z hz
  exact sub_nonpos.mp hw

/--
**Closed under adding a harmonic function (B2 toolbox W5b).** If `v` is a
`PerronSubOn V` member and `h` is harmonic on the open set `V`, then
`v + h` is a `PerronSubOn V` member.

On a disc `closedBall c R ⊆ V` with majorant `h'`
(`HarmonicContOnCl h' (ball c R)`, `v + h ≤ h'` on `sphere c R`), one has
`v ≤ h' - h` on the sphere, and `h' - h` is itself `HarmonicContOnCl` on
`ball c R` (`h` restricts to the disc via `HarmonicContOnCl.mk_ball`), so
`v`'s comparison clause gives `v ≤ h' - h` on the ball, i.e.
`v + h ≤ h'`.  Continuity is `ContinuousOn.add`.

Subsumes the constant-shift case (a constant is harmonic).  Consumed by
the §3.3 Green's families (members shifted by the harmonic log profile)
and the §3.5 envelope assembly. -/
theorem PerronSubOn.add_harmonicOnNhd {v h : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) (hh : HarmonicOnNhd h V) :
    PerronSubOn (fun z => v z + h z) V := by
  refine ⟨hv.1.add (continuousOn_of_harmonicOnNhd hh), ?_⟩
  intro c R hR hsub h' hh' hbd z hz
  have hhDisc : HarmonicContOnCl h (Metric.ball c R) :=
    HarmonicContOnCl.mk_ball
      (hh.mono (Metric.ball_subset_closedBall.trans hsub))
      ((hh.mono hsub).continuousOn)
  have hmaj : HarmonicContOnCl (fun x => h' x - h x) (Metric.ball c R) :=
    hh'.sub hhDisc
  have hbd' : ∀ w ∈ Metric.sphere c R, v w ≤ (fun x => h' x - h x) w := by
    intro w hw; have := hbd w hw; linarith
  have hle := hv.2 hR hsub hmaj hbd' z hz
  linarith

/-!
## W5b-iii: Poisson modification

For a member `v` of `PerronSubOn V` and a comparison disc
`closedBall c R ⊆ V`, the M4 Dirichlet packaging
`poissonSolution v c R` (`PerronPoissonBoundary.lean`, jc6's W3d) is the
*Poisson modification* of `v` on that disc: the Poisson extension of `v`'s
own circle values inside the disc, glued to `v` outside.  Two facts close
the W5b-iii leaf:

* `PerronSubOn.le_poissonSolution_of_mem_ball` — `v ≤ poissonSolution v c R`
  on the disc, consuming **only** M4 packaging + `v`'s own comparison
  clause (no maximum principle);
* `PerronSubOn.poissonModify` — the modification is again a `PerronSubOn V`
  member, parametric over the W1 obligation `WeakMaxPrincipleInput` (the
  only clause that forces it — see the proof's `U`-region step).
-/

/--
The M4 Dirichlet solution `poissonSolution v c R`, packaged as a
`HarmonicContOnCl` majorant on the open disc `ball c R`: harmonic inside
(`poissonSolution_harmonicOnNhd`), continuous up to the closure
(`continuousOn_poissonSolution`).  Consumes jc6's W3d M4 packaging by
name; re-deriving either half is the jc9-gate duplication land-mine. -/
theorem harmonicContOnCl_poissonSolution {v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hv : ContinuousOn v (Metric.sphere c R)) :
    HarmonicContOnCl (poissonSolution v c R) (Metric.ball c R) :=
  HarmonicContOnCl.mk_ball
    (poissonSolution_harmonicOnNhd hR hv)
    (continuousOn_poissonSolution hR hv)

/--
**W5b-iii, the comparison half.**  For a `PerronSubOn V` member `v` and a
disc `closedBall c R ⊆ V`, the Poisson modification dominates `v` on the
disc: `v ≤ poissonSolution v c R` on `ball c R`.

The M4 extension is a legal `HarmonicContOnCl` majorant on `ball c R`
whose sphere values are `v`'s own (`poissonSolution_apply_of_mem_sphere`),
so the comparison clause `v ≤ majorant` on the sphere holds by equality
and `v`'s own `PerronSubOn` clause closes the disc.  **No** maximum
principle obligation. -/
theorem PerronSubOn.le_poissonSolution_of_mem_ball {v : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ V) :
    ∀ z ∈ Metric.ball c R, v z ≤ poissonSolution v c R z := by
  have hvSphere : ContinuousOn v (Metric.sphere c R) :=
    hv.1.mono (Metric.sphere_subset_closedBall.trans hsub)
  refine hv.le_on_ball hR hsub (harmonicContOnCl_poissonSolution hR hvSphere) ?_
  intro w hw
  rw [poissonSolution_apply_of_mem_sphere hw]

open scoped Classical in
/--
The Poisson modification `poissonSolution v c R` is continuous on `V`:
it agrees with `v` outside the open disc and with the M4 closed-disc
solution on `closedBall c R`, glued along the circle where M4's value is
`v`'s own.  The two-closed-set gluing `ContinuousOn.if` consumes only
`continuousOn_poissonSolution` (M4) and `v`'s continuity — no maximum
principle. -/
theorem PerronSubOn.poissonSolution_continuousOn {v : ℂ → ℝ} {V : Set ℂ}
    (hv : PerronSubOn v V) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ V) :
    ContinuousOn (poissonSolution v c R) V := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hvSphere : ContinuousOn v (Metric.sphere c R) :=
    hv.1.mono (Metric.sphere_subset_closedBall.trans hsub)
  have hpcl : ContinuousOn (poissonSolution v c R) (Metric.closedBall c R) :=
    _root_.JacobianChallenge.HolomorphicForms.continuousOn_poissonSolution hR hvSphere
  -- `poissonSolution = (if · ∈ ball c R then poissonSolution · else v ·)`
  have hfun : poissonSolution v c R =
      fun z => if z ∈ Metric.ball c R then poissonSolution v c R z else v z := by
    funext z
    by_cases hz : z ∈ Metric.ball c R
    · rw [if_pos hz]
    · rw [if_neg hz, poissonSolution]
      simp only [if_neg hz]
  rw [hfun]
  refine ContinuousOn.if ?_ ?_ ?_
  · -- on the frontier circle the two branches agree (M4 boundary value)
    intro a ha
    have haS : a ∈ Metric.sphere c R := by
      have : a ∈ frontier (Metric.ball c R) := ha.2
      rwa [frontier_ball c hRne] at this
    exact poissonSolution_apply_of_mem_sphere haS
  · -- interior branch: M4 closed-disc continuity
    refine hpcl.mono ?_
    simp only [Set.setOf_mem_eq, closure_ball c hRne]
    exact Set.inter_subset_right
  · -- exterior branch: `v`'s continuity on `V`
    exact hv.1.mono Set.inter_subset_left

/--
**W5b-iii: the Poisson modification is a member (B2 toolbox W5b).**  For a
`PerronSubOn V` member `v` and a comparison disc `closedBall c R ⊆ V`, the
M4 Dirichlet solution `poissonSolution v c R` — the Poisson extension of
`v`'s circle values inside the disc, glued to `v` outside — is again a
`PerronSubOn V` member.

Continuity is `PerronSubOn.continuousOn_poissonSolution` (M4 gluing, no
obligation).  The comparison clause on an arbitrary test disc
`closedBall c' R' ⊆ V` with majorant `h'`
(`HarmonicContOnCl h' (ball c' R')`, `P ≤ h'` on `sphere c' R'`) splits a
point `z ∈ ball c' R'` by whether it meets the modification disc:

* `z ∉ ball c R` ⟹ `P z = v z`, and `v ≤ h'` on `ball c' R'` because
  `v ≤ P` (`le_poissonSolution_of_mem_ball` inside the modification disc,
  equality outside) makes `v ≤ h'` on `sphere c' R'`, so `v`'s own clause
  closes it;
* `z ∈ ball c R` ⟹ on the overlap `U := ball c' R' ∩ ball c R`, `P` is the
  Poisson operator (harmonic) and `w := P - h'` is harmonic on `U`,
  continuous on `closure U`, and `≤ 0` on `frontier U` — every frontier
  point is on `sphere c' R'` (where `P ≤ h'` by hypothesis) or on
  `sphere c R` (where `P = v ≤ h'`).  **This** is the only clause that
  forces the weak maximum principle obligation `WeakMaxPrincipleInput`.

The parametricity is therefore minimal: continuity and the exterior case
are obligation-free; only the overlap comparison consumes `hmax`. -/
theorem PerronSubOn.poissonModify (hmax : WeakMaxPrincipleInput)
    {v : ℂ → ℝ} {V : Set ℂ} (hv : PerronSubOn v V) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hsub : Metric.closedBall c R ⊆ V) :
    PerronSubOn (poissonSolution v c R) V := by
  refine ⟨hv.poissonSolution_continuousOn hR hsub, ?_⟩
  intro c' R' hR' hsub' h' hh' hbd z hz
  set P := poissonSolution v c R with hP
  -- `v ≤ P` everywhere: equality off the modification disc, the comparison
  -- half inside it.
  have hvP : ∀ w, v w ≤ P w := by
    intro w
    by_cases hw : w ∈ Metric.ball c R
    · exact hv.le_poissonSolution_of_mem_ball hR hsub w hw
    · rw [hP, poissonSolution]; simp only [if_neg hw]; exact le_refl _
  -- `v ≤ h'` on the closed test disc: on the sphere from `v ≤ P ≤ h'`,
  -- then `v`'s own clause gives it on the ball.
  have hvbd_sphere : ∀ w ∈ Metric.sphere c' R', v w ≤ h' w := fun w hw =>
    (hvP w).trans (hbd w hw)
  have hv_ball : ∀ w ∈ Metric.ball c' R', v w ≤ h' w :=
    hv.le_on_ball hR' hsub' hh' hvbd_sphere
  have hv_closed : ∀ w ∈ Metric.closedBall c' R', v w ≤ h' w := by
    intro w hw
    rcases (Metric.mem_closedBall.mp hw).lt_or_eq with hlt | heq
    · exact hv_ball w (Metric.mem_ball.mpr hlt)
    · exact hvbd_sphere w (Metric.mem_sphere.mpr heq)
  -- split `z` by whether it is inside the modification disc.
  by_cases hzc : z ∈ Metric.ball c R
  · -- overlap case: maximum principle on `U := ball c' R' ∩ ball c R`.
    set U := Metric.ball c' R' ∩ Metric.ball c R with hU
    have hRne : R ≠ 0 := ne_of_gt hR
    have hR'ne : R' ≠ 0 := ne_of_gt hR'
    have hzU : z ∈ U := ⟨hz, hzc⟩
    -- `P` is the Poisson operator (hence harmonic) on the modification disc.
    have hPharm : HarmonicOnNhd P (Metric.ball c R) :=
      (harmonicContOnCl_poissonSolution hR
        (hv.1.mono (Metric.sphere_subset_closedBall.trans hsub))).harmonicOnNhd
    -- `w := P - h'` harmonic on `U`.
    have hwHarm : HarmonicOnNhd (fun x => P x - h' x) U :=
      (hPharm.mono Set.inter_subset_right).sub
        (hh'.harmonicOnNhd.mono Set.inter_subset_left)
    -- continuity on `closure U`.
    have hPcont : ContinuousOn P (Metric.closedBall c R) :=
      _root_.JacobianChallenge.HolomorphicForms.continuousOn_poissonSolution hR
        (hv.1.mono (Metric.sphere_subset_closedBall.trans hsub))
    have hclU : closure U ⊆ Metric.closedBall c' R' ∩ Metric.closedBall c R := by
      refine (closure_inter_subset_inter_closure _ _).trans ?_
      rw [closure_ball c' hR'ne, closure_ball c hRne]
    have hwCont : ContinuousOn (fun x => P x - h' x) (closure U) := by
      refine (ContinuousOn.sub ?_ ?_).mono hclU
      · exact hPcont.mono Set.inter_subset_right
      · exact hh'.continuousOn_ball.mono Set.inter_subset_left
    -- `w ≤ 0` on `frontier U`.
    have hfront : ∀ ζ ∈ frontier U, (fun x => P x - h' x) ζ ≤ 0 := by
      intro ζ hζ
      have hsplit := frontier_inter_subset (Metric.ball c' R') (Metric.ball c R) hζ
      rw [frontier_ball c' hR'ne, frontier_ball c hRne,
        closure_ball c' hR'ne, closure_ball c hRne] at hsplit
      refine sub_nonpos.mpr ?_
      rcases hsplit with ⟨hS', _⟩ | ⟨hC', hS⟩
      · -- on `sphere c' R'`: `P ≤ h'` by the test-disc hypothesis
        exact hbd ζ hS'
      · -- on `sphere c R`: `P = v ≤ h'` (sphere value is `v`, `ζ ∈ closedBall c' R'`)
        rw [hP, poissonSolution_apply_of_mem_sphere hS]
        exact hv_closed ζ hC'
    have hUopen : IsOpen U := Metric.isOpen_ball.inter Metric.isOpen_ball
    have hUbdd : Bornology.IsBounded U :=
      Metric.isBounded_ball.subset Set.inter_subset_left
    have := hmax U (fun x => P x - h' x) hUopen hUbdd hwHarm hwCont hfront z hzU
    exact sub_nonpos.mp this
  · -- exterior case: `P z = v z ≤ h' z`.
    have : P z = v z := by rw [hP, poissonSolution]; simp only [if_neg hzc]
    rw [this]
    exact hv_ball z hz

end JacobianChallenge.HolomorphicForms
