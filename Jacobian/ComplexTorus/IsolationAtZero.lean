import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Isolation at zero for a discrete additive subgroup

Queue B sibling. This is a small generic lemma needed for the
manifold-layer chart construction (see `ManifoldRecon.lean` step (b)
of the construction outline): in a normed additive group, a discrete
additive subgroup has its nonzero elements bounded away from zero.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [SeminormedAddCommGroup V]

/-- In a seminormed additive group, the nonzero elements of a discrete
additive subgroup are bounded away from zero in the ambient norm. -/
lemma exists_pos_le_norm_of_discreteTopology
    (S : AddSubgroup V) [DiscreteTopology S] :
    ∃ δ > 0, ∀ g ∈ S, g ≠ 0 → δ ≤ ‖g‖ := by
  obtain ⟨U, hU_open, hU_inter⟩ : ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧ U ∩ S = {0} := by
    have := @isOpen_inter_eq_singleton_of_mem_discrete V
    convert this (show IsDiscrete (S : Set V) from ?_) (S.zero_mem)
    · simp +contextual [Set.eq_singleton_iff_unique_mem]
    · exact SetLike.isDiscrete_iff_discreteTopology.mpr ‹_›
  rcases Metric.isOpen_iff.1 hU_open 0 hU_inter.1 with ⟨δ, δpos, hδ⟩
  exact ⟨δ, δpos, fun g hg hg' => le_of_not_gt fun hg'' =>
    hg' <| hU_inter.2.subset ⟨hδ <| mem_ball_zero_iff.2 hg'', hg⟩⟩

end JacobianChallenge.ComplexTorus
