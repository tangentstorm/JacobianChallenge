import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.LocalSection
import Jacobian.ComplexTorus.LocalSectionRightInv
import Jacobian.ComplexTorus.LocalSectionContinuous
import Jacobian.ComplexTorus.MkImage
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Chart on the complex torus from a small ball

- `MkImage.mk_image_isOpen`             — open-source obligation
- `Metric.isOpen_ball`                   — open-target obligation
- `LocalSection.mk_localSection`         — quotient-side left inverse
  and the `map_source'`/`map_target'` shape (combined with
  `localSection_mem`)
- `LocalSectionRightInv.localSection_mk` — model-side right inverse
- `LocalSectionContinuous.continuousOn_localSection` — toFun continuity
- `QuotientAddGroup.continuous_mk`       — invFun continuity
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/--
A chart on the complex torus near a base point `v ∈ V`, with
chart radius `r` strictly less than half the isolation radius `δ`.
-/
noncomputable def chartAtBall
    (Λ : FullComplexLattice V) (v : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖) :
    OpenPartialHomeomorph (quotient V Λ) V where
  toFun := localSection Λ v r
  invFun := mk V Λ
  source := mk V Λ '' Metric.ball v r
  target := Metric.ball v r
  map_source' _ hq := localSection_mem Λ v r hq
  map_target' _ hx := Set.mem_image_of_mem (mk V Λ) hx
  left_inv' _ hq := mk_localSection Λ v r hq
  right_inv' _ hx := localSection_mk Λ v hr_lt hiso hx
  open_source := mk_image_isOpen Λ Metric.isOpen_ball
  open_target := Metric.isOpen_ball
  continuousOn_toFun := continuousOn_localSection Λ v hr_lt hiso
  continuousOn_invFun := QuotientAddGroup.continuous_mk.continuousOn

end JacobianChallenge.ComplexTorus
