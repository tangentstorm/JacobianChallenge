import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Continuity-of-lift criterion on the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

This is the universal property of the quotient topology, stated for the
specific complex-torus quotient. It gives a clean way to prove a function
out of the quotient is continuous by checking it on representatives.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V]
  [TopologicalSpace W]
  (Λ : FullComplexLattice V)

/-- A function from the complex torus is continuous iff its precomposition
with `mk` is continuous. -/
lemma continuous_iff_continuous_comp_mk (f : quotient V Λ → W) :
    Continuous f ↔ Continuous (f ∘ mk V Λ) :=
  (QuotientAddGroup.isQuotientMap_mk Λ.subgroup).continuous_iff

end JacobianChallenge.ComplexTorus
