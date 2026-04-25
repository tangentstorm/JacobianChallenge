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
  rw [← isCompact_univ_iff]
  have hsurj : mk V Λ '' K = Set.univ := by
    ext q
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    obtain ⟨v, hv⟩ := mk_surjective V Λ q
    obtain ⟨g, hg, hvg⟩ := hcov v
    exact ⟨v - g, hvg, by rw [show mk V Λ (v - g) = mk V Λ v from
      QuotientAddGroup.eq.mpr (by simp [hg]), hv]⟩
  rw [← hsurj]
  exact hK.image QuotientAddGroup.continuous_mk

end JacobianChallenge.ComplexTorus
