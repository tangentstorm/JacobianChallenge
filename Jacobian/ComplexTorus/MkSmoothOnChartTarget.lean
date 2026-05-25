import Jacobian.ComplexTorus.IsManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# `mk` is `ContMDiffOn` on each chart target

This is a stepping stone toward the full `ContMDiff (mk V Λ)`. The
remaining work is the translation argument: every point `x : V` lies
in `Λ.subgroup`-translate of some chart target, and `mk` is invariant
under those translations, so smoothness on the chart target propagates
to all of `V`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/--
The `symm` of the chart at `q` is `ContMDiffOn ℂ ω` on the chart's
target. This is the manifold-level statement for the projection
`mk V Λ` restricted to the target ball, since the chart's `invFun`
is `mk V Λ`.
-/
lemma contMDiffOn_chartAt_symm (Λ : FullComplexLattice V)
    (q : quotient V Λ) :
    ContMDiffOn (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (chartAt V q).symm
      (chartAt V q).target :=
  contMDiffOn_chart_symm

end JacobianChallenge.ComplexTorus
