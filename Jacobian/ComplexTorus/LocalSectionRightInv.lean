import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.LocalSection
import Jacobian.ComplexTorus.MkInjOnSmallBall

set_option linter.unusedSectionVars false

/-!
# Right-inverse property of `localSection` on the small ball

The proof uses `localSection`'s `Function.invFunOn` API together with
`MkInjOnSmallBall.mk_injOn_ball_of_isolation` to upgrade the standard
`mk (localSection q) = q` property into a fully two-sided inverse on
the ball.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/--
When `r < δ / 2` and δ is an isolation radius for `Λ.subgroup`,
the local section on `Metric.ball v r` is a left inverse of `mk` on
that ball.
-/
lemma localSection_mk
    (Λ : FullComplexLattice V) (v : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖)
    {x : V} (hx : x ∈ Metric.ball v r) :
    localSection Λ v r (mk V Λ x) = x := by
  have hmem : mk V Λ x ∈ mk V Λ '' Metric.ball v r :=
    Set.mem_image_of_mem (mk V Λ) hx
  have hsec : localSection Λ v r (mk V Λ x) ∈ Metric.ball v r :=
    localSection_mem Λ v r hmem
  have heq : mk V Λ (localSection Λ v r (mk V Λ x)) = mk V Λ x :=
    mk_localSection Λ v r hmem
  exact mk_injOn_ball_of_isolation Λ.subgroup hr_lt hiso v hsec hx heq

end JacobianChallenge.ComplexTorus
