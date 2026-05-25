import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.MkImage
import Jacobian.ComplexTorus.TransitionContDiffOn

/-!
# Pointwise `ContDiffAt` of `localSection ∘ mk`

`contDiffOn_localSection_mk` proves `ContDiffOn` on
`Metric.ball v₁ r ∩ mk ⁻¹' (mk '' Metric.ball v₂ r)`. Specializing
`v₁ := x` makes that intersection an open neighborhood of `x` (both
sides are open and contain `x` when `r > 0` and `x` is in the
preimage), so `ContDiffOn.contDiffAt` upgrades to `ContDiffAt`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/--
Pointwise version of `contDiffOn_localSection_mk`: for any `x`
in the saturated chart preimage, `y ↦ localSection Λ w r (mk y)` is
`ContDiffAt ℂ ω` at `x`.
-/
lemma contDiffAt_localSection_mk
    (Λ : FullComplexLattice V) (w : V) {δ r : ℝ}
    (hδpos : 0 < δ)
    (hr_lt : r < δ / 2)
    (hr_pos : 0 < r)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖)
    {x : V} (hx : x ∈ mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) :
    ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : V => localSection Λ w r (mk V Λ y)) x := by
  have h := contDiffOn_localSection_mk Λ x w hδpos hr_lt hiso
  have hxball : x ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_self]; exact hr_pos
  have hopen1 : IsOpen (Metric.ball x r) := Metric.isOpen_ball
  have hopen2 : IsOpen (mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) :=
    (mk_image_isOpen Λ Metric.isOpen_ball).preimage QuotientAddGroup.continuous_mk
  have h_set_open :
      IsOpen (Metric.ball x r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) :=
    hopen1.inter hopen2
  have h_set_mem :
      Metric.ball x r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r) ∈ nhds x :=
    h_set_open.mem_nhds ⟨hxball, hx⟩
  exact h.contDiffAt h_set_mem

end JacobianChallenge.ComplexTorus
