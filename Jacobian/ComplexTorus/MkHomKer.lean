import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank
import Jacobian.ComplexTorus.MkBundled

/-!
# Kernel of the bundled quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The kernel of `mkHom` is exactly `Λ.subgroup`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The kernel of the bundled quotient projection equals the lattice. -/
@[simp] lemma mkHom_ker : (mkHom Λ).ker = Λ.subgroup := by
  sorry

end JacobianChallenge.ComplexTorus
