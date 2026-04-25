import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.Mk
import Jacobian.ComplexTorus.LocalSection

/-!
# The chart transition's "subtract input" lands in the lattice

Queue B sibling. First small step toward `IsManifold`: when two
charts overlap, their composition `e2 ∘ e1.symm` differs from the
identity by an element of `Λ.subgroup`.

For our charts, `e1.symm = mk` and `e2 = localSection_v2`, so the
transition value at `x` is `localSection_v2 (mk x)`. By the
right-inverse of `localSection`, `mk (localSection_v2 (mk x)) = mk x`,
so `localSection_v2 (mk x) - x ∈ Λ.subgroup`.

This file states only the "subtract lands in the subgroup" fact;
continuity and local constancy come in later siblings.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- If `q ∈ mk V Λ '' Metric.ball v r` and `mk x = q`, then
`localSection Λ v r q - x ∈ Λ.subgroup`. The membership comes from
`mk (localSection q) = q = mk x`, via `mk_eq_iff`. -/
lemma localSection_sub_mem_subgroup
    (Λ : FullComplexLattice V) (v : V) (r : ℝ)
    {q : quotient V Λ} (hq : q ∈ mk V Λ '' Metric.ball v r)
    {x : V} (hx : mk V Λ x = q) :
    localSection Λ v r q - x ∈ Λ.subgroup := by
  have heq : mk V Λ (localSection Λ v r q) = mk V Λ x :=
    (mk_localSection Λ v r hq).trans hx.symm
  -- mk_eq_iff: mk V Λ a = mk V Λ b ↔ -a + b ∈ Λ.subgroup
  have hmem : -(localSection Λ v r q) + x ∈ Λ.subgroup :=
    (mk_eq_iff (Λ := Λ)).mp heq
  have hrewrite : localSection Λ v r q - x = -(-(localSection Λ v r q) + x) := by
    abel
  rw [hrewrite]
  exact Λ.subgroup.neg_mem hmem

end JacobianChallenge.ComplexTorus
