import Jacobian.Periods.PathSymmSubpath
import Jacobian.Periods.DivFinIcc

/-!
# Segment-level reflection of a subpath partition

For a uniform `n`-partition of `[0, 1]` with boundaries `i/n`, the
i-th segment of `γ.symm` equals the symm of `γ`'s segment with
parameters `[σ((i+1)/n), σ(i/n)]`. By `divFinIcc_symm`, those
boundaries are `[(n-i-1)/n, (n-i)/n]`.

The lemma is stated keeping `σ` in the segment endpoints so that
the path types unify definitionally (`γ.symm s = γ (σ s)` is rfl,
but `σ (i/n) = (n-i)/n` is propositional). Callers that want the
arithmetic-form boundaries can rewrite via `divFinIcc_symm` after
breaking out of the `Path` type.

This is the key path-level identity for the eventual
`pathIntegralViaCoverWith_symm` proof, which then re-indexes the
`Fin n` Finset sum via `Fin.rev` and uses the per-segment sign-flip
from `pathIntegralInChartCorrect_symm`.
-/

namespace JacobianChallenge.Periods

open unitInterval

variable {X : Type*} [TopologicalSpace X]

/--
The i-th segment of `γ.symm` (for the uniform `n`-partition)
equals the symm of `γ`'s segment with endpoints reflected via `σ`.
-/
theorem path_symm_subpath_divFinIcc
    {a b : X} (γ : Path a b) (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i + 1 ≤ n) :
    γ.symm.subpath (divFinIcc n hn i (Nat.le_of_succ_le hi))
                   (divFinIcc n hn (i + 1) hi) =
    (γ.subpath
        (σ (divFinIcc n hn (i + 1) hi))
        (σ (divFinIcc n hn i (Nat.le_of_succ_le hi)))).symm := by
  rw [path_symm_subpath_eq, ← Path.symm_subpath]

end JacobianChallenge.Periods
