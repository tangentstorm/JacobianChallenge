import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.Topology.Order.Lattice

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

end JacobianChallenge.HolomorphicForms
