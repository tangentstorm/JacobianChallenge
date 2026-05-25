import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.OfClm
import Jacobian.ComplexTorus.Surjective

/-!
# Surjectivity of the continuous-linear quotient map

Wraps the additive `map_surjective` for the continuous-linear-map
version `mapClm`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/--
A surjective continuous linear lattice-preserving map descends to a
surjective quotient map.
-/
lemma mapClm_surjective {f : V →L[ℂ] W} (hf_surj : Function.Surjective f)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    Function.Surjective (mapClm f hf) := by
  show Function.Surjective (map Λ Γ f.toAddMonoidHom hf)
  exact map_surjective hf_surj hf

end JacobianChallenge.ComplexTorus
