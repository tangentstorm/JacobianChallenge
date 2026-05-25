import Mathlib.Topology.Subpath

/-!
# `γ.symm.subpath = γ.subpath ∘ σ`

A subpath of the reversed path equals the subpath of `γ` at the
reflected parameters: `γ.symm.subpath s t = γ.subpath (σ s) (σ t)`.

Pointwise: at `r ∈ I`,
```
(γ.symm.subpath s t) r = γ (σ ((1-r) s + r t))
                       = γ ((1-r) (σ s) + r (σ t))
                       = (γ.subpath (σ s) (σ t)) r
```
The first equality is the definition of `Path.symm`; the second is
`σ`-affinity (`σ` is `1 - ·`, which distributes over the convex
combination); the third is the definition of `subpath`.

This is a path-level helper toward `pathIntegralViaCoverWith_symm`,
where the i-th segment of `γ.symm` corresponds to the (n-i-1)-th
segment of `γ` (re-indexed by `Fin.rev`).
-/

namespace JacobianChallenge.Periods

open unitInterval

/--
Subpath of a reversed path at parameters `s, t` equals subpath
of the original at the reflected parameters `σ s, σ t`.
-/
theorem path_symm_subpath_eq
    {X : Type*} [TopologicalSpace X] {a b : X}
    (γ : Path a b) (s t : unitInterval) :
    γ.symm.subpath s t = γ.subpath (σ s) (σ t) := by
  apply Path.ext
  funext r
  show γ (σ (Path.subpathAux s t r)) = γ (Path.subpathAux (σ s) (σ t) r)
  congr 1
  apply Subtype.ext
  show 1 - ((1 - (r : ℝ)) * (s : ℝ) + (r : ℝ) * (t : ℝ)) =
       (1 - (r : ℝ)) * (1 - (s : ℝ)) + (r : ℝ) * (1 - (t : ℝ))
  ring

end JacobianChallenge.Periods
