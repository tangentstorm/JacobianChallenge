import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.Basic

/-!
# Quotient map induced by a continuous linear map

A continuous linear map `V →L[ℂ] W` that maps `Λ.subgroup` into `Γ.subgroup`
gives a continuous additive homomorphism between the two complex tori.
This bundles the algebraic descent (already in the statement bank) with
continuity.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/--
A continuous linear map descends to a continuous additive homomorphism
between complex tori, given that it preserves the lattices.
-/
def mapClm (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    quotient V Λ →+ quotient W Γ :=
  map Λ Γ f.toAddMonoidHom hf

/-- The quotient map induced by a continuous linear map is continuous. -/
lemma mapClm_continuous (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    Continuous (mapClm f hf) :=
  map_continuous f.continuous hf

/-!
### Functoriality of `mapClm`

`mapClm` is a functor from continuous linear lattice-preserving maps to
continuous additive homomorphisms of complex tori, so it commutes with
identity and composition. The proofs are spelled-out wrappers around the
algebraic `map_id` / `map_comp` from the statement bank.
-/

/-- `mapClm` of the identity is the identity. -/
lemma mapClm_id :
    mapClm (ContinuousLinearMap.id ℂ V)
        (Λ := Λ) (Γ := Λ) (fun _ hv => hv) =
      AddMonoidHom.id (quotient V Λ) :=
  map_id Λ

/-- `mapClm` distributes over composition of continuous linear maps. -/
lemma mapClm_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {Η : FullComplexLattice U}
    (f : V →L[ℂ] W) (g : W →L[ℂ] U)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup)
    (hg : ∀ w ∈ Γ.subgroup, g w ∈ Η.subgroup) :
    mapClm (g.comp f)
        (Λ := Λ) (Γ := Η) (fun v hv => hg (f v) (hf v hv)) =
      (mapClm g hg).comp (mapClm f hf) :=
  map_comp Λ Γ Η f.toAddMonoidHom g.toAddMonoidHom hf hg

end JacobianChallenge.ComplexTorus
