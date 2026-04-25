import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Isolation at zero for a discrete additive subgroup

Queue B sibling. This is a small generic lemma needed for the
manifold-layer chart construction (see `ManifoldRecon.lean` step (b)
of the construction outline): in a normed additive group, a discrete
additive subgroup has its nonzero elements bounded away from zero.

Status: statement scaffold; `sorry` to be replaced by Aristotle.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [SeminormedAddCommGroup V]

/-- In a seminormed additive group, the nonzero elements of a discrete
additive subgroup are bounded away from zero in the ambient norm. -/
lemma exists_pos_le_norm_of_discreteTopology
    (S : AddSubgroup V) [DiscreteTopology S] :
    ∃ δ > 0, ∀ g ∈ S, g ≠ 0 → δ ≤ ‖g‖ := by
  sorry

end JacobianChallenge.ComplexTorus
