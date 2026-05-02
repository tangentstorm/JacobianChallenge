import Jacobian.HolomorphicForms.Serre.CotangentSheaf

/-!
# Dualizing sheaf `K_X` on a Riemann surface

The dualizing sheaf of a 1-dimensional complex manifold is the
cotangent sheaf (sheaf of holomorphic 1-forms). Lifted out of
`SerreDualityRS.lean` (round 1) so Serre/ files that need to refer to
`K_X` without depending on the upstream Serre-duality bookkeeping can
import this lightweight file instead.

The original public name
`JacobianChallenge.HolomorphicForms.RSDualizingSheaf` is preserved.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- The dualizing sheaf `K_X` on a topological space `X`, viewed as an
abelian sheaf via `RSAbSheaf`. For 1-dim complex manifolds this is the
cotangent sheaf `Ω¹_X`. Declared as an `abbrev` so the universe-
parameter count of `RSAbSheaf` is preserved at the call site
(downstream files use `RSDualizingSheaf.{_, 0}` syntax). -/
noncomputable abbrev RSDualizingSheaf (X : Type*) [TopologicalSpace X] :
    RSAbSheaf X :=
  RSCotangentSheaf X

end JacobianChallenge.HolomorphicForms
