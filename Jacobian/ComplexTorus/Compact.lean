import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Compactness of the complex-torus quotient from a compact fundamental domain

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet: when there is a compact set `K ⊆ V` that hits every
`Λ.subgroup`-coset (i.e. every point of `V` is `Λ`-translatable into `K`),
the quotient `V ⧸ Λ.subgroup` is compact. This is the standard
"cocompact lattice → compact quotient" fact and is the analytic input the
project ultimately needs to drop the `quotient_compact` field of
`FullComplexLattice` in favor of a derived instance.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- If `K ⊆ V` is compact and every point of `V` lies in some
`Λ.subgroup`-translate of `K`, the complex-torus quotient is compact. -/
lemma compactSpace_quotient_of_cover
    {K : Set V} (hK : IsCompact K)
    (hcov : ∀ v : V, ∃ g ∈ Λ.subgroup, v - g ∈ K) :
    CompactSpace (quotient V Λ) := by
  sorry

end JacobianChallenge.ComplexTorus
