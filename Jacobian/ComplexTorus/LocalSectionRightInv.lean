import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.LocalSection
import Jacobian.ComplexTorus.MkInjOnSmallBall

/-!
# Right-inverse property of `localSection` on the small ball

Queue B sibling. This is the second equation of the chart's
local-section/projection pair: when the chart radius is small enough
to make `mk` injective on the ball, `localSection (mk x) = x` for any
`x` in that ball.

The proof uses `localSection`'s `Function.invFunOn` API together with
`MkInjOnSmallBall.mk_injOn_ball_of_isolation` to upgrade the standard
`mk (localSection q) = q` property into a fully two-sided inverse on
the ball.

Status: statement scaffold; `sorry` to be replaced by Aristotle.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- When `r < δ / 2` and δ is an isolation radius for `Λ.subgroup`,
the local section on `Metric.ball v r` is a left inverse of `mk` on
that ball. -/
lemma localSection_mk
    (Λ : FullComplexLattice V) (v : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖)
    {x : V} (hx : x ∈ Metric.ball v r) :
    localSection Λ v r (mk V Λ x) = x := by
  sorry

end JacobianChallenge.ComplexTorus
