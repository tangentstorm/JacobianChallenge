import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.LocalSection
import Jacobian.ComplexTorus.MkInjOnSmallBall
import Jacobian.ComplexTorus.MkImage

/-!
# Continuity of the local section on the chart image

Queue B sibling. This is the substantive continuity statement that
unblocks the chart's `OpenPartialHomeomorph` assembly: on the image
`mk '' Metric.ball v r`, the local section
`localSection Λ v r : V ⧸ Λ.subgroup → V` is continuous.

Conceptually, this follows from `mk` being an open embedding when
restricted to `Metric.ball v r` — its three ingredients
(continuity, openness, injectivity) are all already available:

- `QuotientAddGroup.continuous_mk` (continuity of `mk`);
- `QuotientAddGroup.isOpenMap_coe` (openness of `mk`);
- `MkInjOnSmallBall.mk_injOn_ball_of_isolation`
  (injectivity of `mk` on `Metric.ball v r` for `r < δ / 2`).

The Mathlib path most likely goes through one of:
- a subtype-based open-embedding constructor and
  `IsOpenEmbedding.continuous_inv`/`.toHomeomorph`;
- `Set.InjOn.bijOn_image` followed by the standard
  inverse-from-bijection on the image; or
- `IsOpenMap` + `Continuous` + `InjOn` ⇒ inverse is continuous.

If the path is not direct, this packet can be downgraded to a
reconnaissance packet (Aristotle reports the exact missing/closest
Mathlib lemma names instead of completing the proof).

Status: statement scaffold; `sorry` to be replaced by Aristotle.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The local section is continuous on the image of the small ball,
provided the ball radius makes `mk` injective on the ball. -/
lemma continuousOn_localSection
    (Λ : FullComplexLattice V) (v : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖) :
    ContinuousOn (localSection Λ v r) (mk V Λ '' Metric.ball v r) := by
  sorry

end JacobianChallenge.ComplexTorus
