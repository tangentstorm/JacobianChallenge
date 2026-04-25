import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.IsolationAtZero
import Jacobian.ComplexTorus.MkInjOnSmallBall
import Jacobian.ComplexTorus.MkImage

/-!
# Existence of a chart-prep ball around any point of `V`

Queue B sibling. This is the first chart-layer primitive, bundling the
three earlier preparatory lemmas:

- `IsolationAtZero.exists_pos_le_norm_of_discreteTopology` extracts an
  isolation radius `δ` from the `FullComplexLattice.isDiscrete` field.
- `MkInjOnSmallBall.mk_injOn_ball_of_isolation` turns `δ` into
  injectivity of the quotient projection on `Metric.ball v r` for any
  `r < δ / 2`.
- `MkImage.mk_image_isOpen` shows that the image of an open set
  through `mk` is open in the quotient (since `mk` is an open map).

Their combination gives the chart-construction prerequisites at every
base point: a small enough ball on which `mk` is injective and whose
image is open. This is the minimal data for an
`OpenPartialHomeomorph` whose source is the image and whose target is
the ball.

Status: statement scaffold; `sorry` to be replaced by Aristotle.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- For any full complex lattice and any base point, a small enough
open ball admits the chart-construction prerequisites: the quotient
projection is injective on the ball, and the image is open in the
quotient. -/
lemma exists_chart_ball (Λ : FullComplexLattice V) (v : V) :
    ∃ r > 0,
      Set.InjOn (mk V Λ) (Metric.ball v r) ∧
      IsOpen (mk V Λ '' Metric.ball v r) := by
  obtain ⟨δ, δpos, hiso⟩ := exists_pos_le_norm_of_discreteTopology Λ.subgroup
  refine ⟨δ / 4, by linarith, ?_, ?_⟩
  · exact mk_injOn_ball_of_isolation Λ.subgroup (by linarith) hiso v
  · exact mk_image_isOpen Λ Metric.isOpen_ball

end JacobianChallenge.ComplexTorus
