import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.TransitionSubMem
import Jacobian.ComplexTorus.LocalSectionContinuous

/-!
# `localSection ∘ mk` is locally a translation on the full chart preimage

This is the building block needed both for smoothness of the
quotient projection `mk : V → V ⧸ Λ.subgroup` and for the
`LieAddGroup` smoothness of `+` and `-` on the quotient.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]

/--
`y ↦ localSection Λ w r (mk y) - y` is continuous on the full
chart preimage `mk ⁻¹' (mk '' Metric.ball w r)`.
-/
lemma continuousOn_localSection_mk_sub'
    [NormedSpace ℂ V]
    (Λ : FullComplexLattice V) (w : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖) :
    ContinuousOn (fun x : V => localSection Λ w r (mk V Λ x) - x)
      (mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) := by
  have hmk : ContinuousOn (mk V Λ)
      (mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) :=
    QuotientAddGroup.continuous_mk.continuousOn
  have hsec : ContinuousOn (localSection Λ w r) (mk V Λ '' Metric.ball w r) :=
    continuousOn_localSection Λ w hr_lt hiso
  have hcomp : ContinuousOn (fun x : V => localSection Λ w r (mk V Λ x))
      (mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) := by
    refine hsec.comp hmk ?_
    intro x hx
    exact hx
  exact hcomp.sub continuousOn_id

/--
For each `x` in the full preimage `mk ⁻¹' (mk '' Metric.ball w r)`,
the map `y ↦ localSection Λ w r (mk y)` agrees with the translation
`y ↦ y + g` (for `g := localSection Λ w r (mk x) - x ∈ Λ.subgroup`)
on a neighborhood of `x` (within the preimage).
-/
lemma mk_locally_translate
    [NormedSpace ℂ V]
    (Λ : FullComplexLattice V) (w : V) {δ r : ℝ}
    (hδpos : 0 < δ)
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖)
    {x : V}
    (hx : x ∈ mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)) :
    ∃ U ∈ nhdsWithin x (mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r)),
      ∀ y ∈ U,
        localSection Λ w r (mk V Λ y) =
          y + (localSection Λ w r (mk V Λ x) - x) := by
  set s := mk V Λ ⁻¹' (mk V Λ '' Metric.ball w r) with s_def
  set f : V → V := fun y => localSection Λ w r (mk V Λ y) - y with f_def
  have hf : ContinuousOn f s :=
    continuousOn_localSection_mk_sub' Λ w hr_lt hiso
  have hat : ContinuousWithinAt f s x := hf.continuousWithinAt hx
  have htends : Filter.Tendsto f (nhdsWithin x s) (nhds (f x)) := hat
  have hball : Metric.ball (f x) δ ∈ nhds (f x) :=
    Metric.ball_mem_nhds _ hδpos
  have hpre : f ⁻¹' Metric.ball (f x) δ ∈ nhdsWithin x s :=
    htends hball
  have hs_mem : s ∈ nhdsWithin x s := self_mem_nhdsWithin
  have hwitness : f ⁻¹' Metric.ball (f x) δ ∩ s ∈ nhdsWithin x s :=
    Filter.inter_mem hpre hs_mem
  refine ⟨f ⁻¹' Metric.ball (f x) δ ∩ s, hwitness, ?_⟩
  intro y hy
  obtain ⟨hyball, hys⟩ := hy
  have hclose : ‖f y - f x‖ < δ := by
    have := Metric.mem_ball.mp hyball
    simpa [dist_eq_norm] using this
  have hy_image : mk V Λ y ∈ mk V Λ '' Metric.ball w r := hys
  have hx_image : mk V Λ x ∈ mk V Λ '' Metric.ball w r := hx
  have hfy_mem : f y ∈ Λ.subgroup :=
    localSection_sub_mem_subgroup Λ w r hy_image rfl
  have hfx_mem : f x ∈ Λ.subgroup :=
    localSection_sub_mem_subgroup Λ w r hx_image rfl
  have hdiff_mem : f y - f x ∈ Λ.subgroup :=
    Λ.subgroup.sub_mem hfy_mem hfx_mem
  have hdiff_zero : f y - f x = 0 := by
    by_contra hne
    have := hiso (f y - f x) hdiff_mem hne
    linarith
  have heq : f y = f x := sub_eq_zero.mp hdiff_zero
  have hsub : localSection Λ w r (mk V Λ y) - y =
              localSection Λ w r (mk V Λ x) - x := heq
  exact sub_eq_iff_eq_add'.mp hsub

end JacobianChallenge.ComplexTorus
