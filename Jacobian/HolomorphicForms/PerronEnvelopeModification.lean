import Jacobian.HolomorphicForms.PerronEnvelope

/-!
# Discharging the Perron envelope's Poisson-modification oracle (B2 toolbox W7)

Blueprint node: `lem:perron-envelope-poisson-modification-input`.

jc11's W7-i `PerronEnvelope.lean` freezes the **Poisson modification
obligation** `PoissonModificationInput F V c R` as a named `Prop`: every
member of the family `F` can be replaced by a member dominating it on `V`
and harmonic on the disc `ball c R`.  The center-touch core of Perron's
lemma (`perronEnvelope_exists_harmonic_eq_at`) consumes it as a hypothesis.

This file discharges that obligation for the family shape the §3.5 envelope
assembly actually builds: a family **all of whose members are
`PerronSubOn V`** that is **closed under the disc Poisson modification**
(`v ∈ F → poissonSolution v c R ∈ F`).  The witness for each member `v` is
its own W5b-iii modification `poissonSolution v c R` (jc6's W3d M4
extension): membership is the closure hypothesis, domination on `V` is B1's
comparison half inside the disc and equality outside, and disc-harmonicity
is M4's `poissonSolution_harmonicOnNhd`.

Thin consumption of the W5b-iii lemmas (`116cc6bf`) + M4 (`8c67fcef`) — no
re-derivation, and `PerronEnvelope.lean` is consumed by import only, never
edited.  The `WeakMaxPrincipleInput` obligation does **not** appear here: it
was internal to B1's `poissonModify`, which this discharge does not need
(the oracle asks only for domination + harmonicity, not for the witness to
be a `PerronSubOn` member).
-/

namespace JacobianChallenge.HolomorphicForms

open InnerProductSpace Metric

/--
**W7 Poisson-modification oracle, discharged for modification-closed
`PerronSubOn` families (B2 toolbox W7).**  If every member of `F` is
`PerronSubOn V`, the disc `closedBall c R ⊆ V`, and `F` is closed under the
disc Poisson modification (`v ∈ F → poissonSolution v c R ∈ F`), then the
frozen `PoissonModificationInput F V c R` holds.

The witness for `v ∈ F` is `poissonSolution v c R`:

* membership `∈ F` is the modification-closure hypothesis `hclosed`;
* domination `v ≤ poissonSolution v c R` on `V` is B1's
  `le_poissonSolution_of_mem_ball` inside `ball c R` and pointwise equality
  (`poissonSolution = v` off the ball) outside;
* `HarmonicOnNhd (poissonSolution v c R) (ball c R)` is M4's
  `poissonSolution_harmonicOnNhd`, with `v` continuous on `sphere c R`
  inherited from its `PerronSubOn V` continuity.

The modification-closure clause is the load-bearing hypothesis; max-closure
enters separately at the envelope consumer
(`perronEnvelope_exists_harmonic_eq_at`), not here. -/
theorem poissonModificationInput_of_perronSubOn {F : Set (ℂ → ℝ)} {V : Set ℂ}
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ V)
    (hmem : ∀ v ∈ F, PerronSubOn v V)
    (hclosed : ∀ v ∈ F, poissonSolution v c R ∈ F) :
    PoissonModificationInput F V c R := by
  intro v hv
  refine ⟨poissonSolution v c R, hclosed v hv, ?_, ?_⟩
  · -- domination on `V`
    intro z hz
    by_cases hzc : z ∈ Metric.ball c R
    · exact (hmem v hv).le_poissonSolution_of_mem_ball hR hball z hzc
    · rw [poissonSolution]; simp only [if_neg hzc]; exact le_refl _
  · -- harmonic on the disc (M4)
    have hvSphere : ContinuousOn v (Metric.sphere c R) :=
      (hmem v hv).continuousOn.mono (Metric.sphere_subset_closedBall.trans hball)
    exact poissonSolution_harmonicOnNhd hR hvSphere

end JacobianChallenge.HolomorphicForms
