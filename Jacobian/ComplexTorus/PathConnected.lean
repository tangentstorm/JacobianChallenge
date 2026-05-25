import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.PathConnected
import Jacobian.ComplexTorus.Defs

/-!
# Path-connectedness of the complex-torus quotient

A normed `ℂ`-space is path-connected (the segment from `0` is a path),
and `mk` is a continuous surjection, so the quotient is also
path-connected.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The complex-torus quotient is path connected. -/
instance pathConnectedSpace_quotient :
    PathConnectedSpace (quotient V Λ) := Quotient.instPathConnectedSpace

end JacobianChallenge.ComplexTorus
