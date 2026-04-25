import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Injectivity of the quotient projection on small balls

Queue B sibling. Step (d) of the manifold-layer chart construction
outline (`ManifoldRecon.lean`): given a "no nonzero element near zero"
hypothesis on the subgroup, the quotient projection is injective on
any open ball of radius strictly less than half the isolation
constant.

This packet takes the isolation property as an explicit hypothesis,
so it is independent of how the isolation is sourced (discrete
topology, ZLattice, full-rank lattice). It plugs into both flavors.

Status: statement scaffold; `sorry` to be replaced by Aristotle.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [SeminormedAddCommGroup V]

/-- If every nonzero element of an additive subgroup `S ≤ V` has norm
at least `δ`, then `QuotientAddGroup.mk : V → V ⧸ S` is injective on
any open ball of radius strictly less than `δ / 2`. (The case `r ≤ 0`
is vacuous: `Metric.ball v r = ∅`.) -/
lemma mk_injOn_ball_of_isolation
    (S : AddSubgroup V) {δ r : ℝ} (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ S, g ≠ 0 → δ ≤ ‖g‖)
    (v : V) :
    Set.InjOn (QuotientAddGroup.mk : V → V ⧸ S) (Metric.ball v r) := by
  intro x hx y hy hxy
  have hxy_in_S : x - y ∈ S := QuotientAddGroup.eq_iff_sub_mem.mp hxy
  contrapose! hiso
  refine ⟨x - y, hxy_in_S, sub_ne_zero.mpr hiso, ?_⟩
  rw [← dist_eq_norm]
  exact lt_of_le_of_lt (dist_triangle_right _ _ _)
    (by linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy])

end JacobianChallenge.ComplexTorus
