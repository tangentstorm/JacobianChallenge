import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.TransitionSubMem
import Jacobian.ComplexTorus.TransitionSubContinuous

/-!
# Chart transitions are locally translations by lattice elements

Queue B sibling. Combines the previous two sub-lemmas plus the
isolation hypothesis: at each point of the chart overlap, there is
a neighborhood on which the chart transition equals translation by a
fixed lattice element.

Logical content: the map `f x := localSection_v₂ (mk x) - x` is
continuous (`TransitionSubContinuous`), takes values in `Λ.subgroup`
(`TransitionSubMem`), and `Λ.subgroup` is `δ`-isolated at zero
(hypothesis). Continuity at `x` produces a neighborhood `U` where
`‖f y - f x‖ < δ`. Since `f y - f x ∈ Λ.subgroup` and its norm is
strictly below the isolation threshold, the contrapositive of `hiso`
forces `f y - f x = 0`, i.e., `f y = f x` on `U`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- For each point of the chart overlap, the chart transition agrees
with a translation by a fixed lattice element on a neighborhood. -/
lemma localSection_mk_locally_translate
    (Λ : FullComplexLattice V) (v₁ v₂ : V) {δ r : ℝ}
    (hδpos : 0 < δ)
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖)
    {x : V}
    (hx : x ∈ Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) :
    ∃ U ∈ nhdsWithin x
        (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)),
      ∀ y ∈ U,
        localSection Λ v₂ r (mk V Λ y) =
          y + (localSection Λ v₂ r (mk V Λ x) - x) := by
  set s := Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r) with s_def
  set f : V → V := fun y => localSection Λ v₂ r (mk V Λ y) - y with f_def
  have hf : ContinuousOn f s :=
    continuousOn_localSection_mk_sub Λ v₁ v₂ hr_lt hiso
  have hat : ContinuousWithinAt f s x := hf.continuousWithinAt hx
  have htends : Filter.Tendsto f (nhdsWithin x s) (nhds (f x)) := hat
  have hball : Metric.ball (f x) δ ∈ nhds (f x) :=
    Metric.ball_mem_nhds _ hδpos
  have hpre : f ⁻¹' Metric.ball (f x) δ ∈ nhdsWithin x s :=
    htends hball
  -- Intersect with s so that every y in the witness is in the overlap.
  have hs_mem : s ∈ nhdsWithin x s := self_mem_nhdsWithin
  have hwitness : f ⁻¹' Metric.ball (f x) δ ∩ s ∈ nhdsWithin x s :=
    Filter.inter_mem hpre hs_mem
  refine ⟨f ⁻¹' Metric.ball (f x) δ ∩ s, hwitness, ?_⟩
  intro y hy
  obtain ⟨hyball, hys⟩ := hy
  -- f y ∈ Metric.ball (f x) δ means ‖f y - f x‖ < δ
  have hclose : ‖f y - f x‖ < δ := by
    have := Metric.mem_ball.mp hyball
    simpa [dist_eq_norm] using this
  -- Extract image-membership facts from y ∈ s (= ball v₁ r ∩ mk⁻¹' (mk '' ball v₂ r))
  have hy_image : mk V Λ y ∈ mk V Λ '' Metric.ball v₂ r := hys.2
  have hx_image : mk V Λ x ∈ mk V Λ '' Metric.ball v₂ r := hx.2
  -- f y, f x ∈ Λ.subgroup (each is `localSection (mk _) - _`)
  have hfy_mem : f y ∈ Λ.subgroup :=
    localSection_sub_mem_subgroup Λ v₂ r hy_image rfl
  have hfx_mem : f x ∈ Λ.subgroup :=
    localSection_sub_mem_subgroup Λ v₂ r hx_image rfl
  -- f y - f x ∈ Λ.subgroup
  have hdiff_mem : f y - f x ∈ Λ.subgroup :=
    Λ.subgroup.sub_mem hfy_mem hfx_mem
  -- By hiso (contrapositive) and hclose, f y - f x = 0
  have hdiff_zero : f y - f x = 0 := by
    by_contra hne
    have := hiso (f y - f x) hdiff_mem hne
    linarith
  -- Conclude
  have heq : f y = f x := sub_eq_zero.mp hdiff_zero
  -- f y = f x means localSection (mk y) - y = localSection (mk x) - x
  -- so localSection (mk y) = y + (localSection (mk x) - x)
  have hsub : localSection Λ v₂ r (mk V Λ y) - y =
              localSection Λ v₂ r (mk V Λ x) - x := heq
  -- a - y = b ⟹ a = y + b in an additive group.
  have := sub_eq_iff_eq_add'.mp hsub
  exact this


end JacobianChallenge.ComplexTorus
