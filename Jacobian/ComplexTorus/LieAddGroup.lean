import Jacobian.ComplexTorus.AddSmooth
import Jacobian.ComplexTorus.NegSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# `LieAddGroup` instance on the complex torus

`LieAddGroup` extends `ContMDiffAdd`, so we register the
`ContMDiffAdd` instance first.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- `ContMDiffAdd` instance for the complex torus. -/
noncomputable instance contMDiffAdd_quotient (Λ : FullComplexLattice V) :
    ContMDiffAdd (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (quotient V Λ) where
  contMDiff_add := contMDiff_quotient_add Λ

/--
The complex torus is an additive Lie group: the manifold structure
combined with smooth `+` and `-`.
-/
noncomputable instance lieAddGroup_quotient (Λ : FullComplexLattice V) :
    LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (quotient V Λ) where
  contMDiff_neg := contMDiff_quotient_neg Λ

end JacobianChallenge.ComplexTorus
