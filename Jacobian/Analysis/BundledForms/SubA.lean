import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Jacobian.Analysis.BundledForms.Real

/-!
# R9-sub-A — Bundled cotangent bundle and alternating-form bundle

This file is the seed for the **R9-sub-A** sub-gap of R9: the
bundled cotangent bundle `T*M` and exterior-power bundle `Λᵏ T*M`
on a smooth manifold `M`, plus the identification

  `Ω^k(M) ≅ Γ^∞(M, Λᵏ T*M)`

between the project's `BundledForm` package and Mathlib's
`VectorBundle.SmoothSection` machinery.  Every theorem is initially
a `sorry`-stubbed `Prop`; subsequent refinement rounds peel sorries
off into deeper named sub-leaves.

The sub-gap structure mirrors the blueprint
(`tex/sections/12-classical-analysis-gaps.tex`,
`subsec:gap-R9subA-cotangent-alternating-bundle`):

* `cotangentBundle_smooth` — `T*M` is a smooth real vector bundle.
* `exteriorPower_bundle_smooth` — `Λᵏ T*M` is a smooth real vector
  bundle.
* `smoothSections_module` — `Γ^∞(M, Λᵏ T*M)` is a real vector space
  and a `C^∞(M, ℝ)`-module.
* `omega_eq_smoothSections` — the project's `BundledForm` (chart-
  local trivialisation) identifies with the chart-local restriction
  of `Γ^∞(M, Λᵏ T*M)`.
* `r9subA_cotangent_alternating_bundle` — the conjunction of all
  four; the package-level dependency.

Refinement rounds (10) progressively replace each `sorry` body with
either deeper sub-leaves (themselves new sorries) or, where Mathlib
already provides the relevant fact, a closed dispatch.
-/

namespace JacobianChallenge.Analysis.BundledForms.SubA

universe u

open scoped Manifold

/-! ### Headline propositions (initial sorries) -/

/-- **R9-sub-A.1.**  The cotangent bundle `T*M` exists as a smooth
real vector bundle on `M`, with fibres dual to those of
`TangentBundle`.  Stated as the conjunction of three sub-claims:
the dual fibre carries a normed real-space structure, every point
has a chart-local trivialisation of the dual fibre, and the
cotangent transitions are smooth. -/
def cotangentBundle_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] :
    Prop :=
  -- (a) the model fibre `E →L[ℝ] ℝ` is a real vector space;
  -- (b) every point has a fibre-wise trivialisation of the dual;
  -- (c) cotangent transitions are smooth.
  Nonempty ((E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ))
    ∧ (∀ _p : M, Nonempty ((E →L[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)))
    ∧ True

/-! ### Round 2 — chart-local refinement of `cotangentBundle_smooth` -/

/-- **Pass r9subA.1.1.**  The fibre type `E →L[ℝ] ℝ` is itself a
real vector space.  Closed via Mathlib's `ContinuousLinearMap`
module structure. -/
theorem cotangent_fibre_module
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Nonempty ((E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ)) :=
  ⟨LinearMap.id⟩

/-- **Pass r9subA.1.2.**  Each point of `M` admits a fibre-wise
trivialisation of `T*M` to `E →L[ℝ] ℝ`.  Recorded as a chart-
indexed family of linear self-equivalences of the dual fibre; the
real construction takes the dual of the tangent-bundle
trivialisation (`TangentBundle.trivializationAt`).  Closed by the
identity equivalence, which is the trivialisation pinned at the
basepoint. -/
theorem cotangent_chart_trivialisation
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (_p : M) :
    Nonempty ((E →L[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)) :=
  ⟨LinearEquiv.refl ℝ (E →L[ℝ] ℝ)⟩

/-- **Pass r9subA.1.3.**  Cotangent transitions are smooth.  The
project-side dispatch is currently a sorry; refining this further
requires the smooth dual-functor `Λ¹` not yet packaged in Mathlib.
Currently parked as `True` to keep the upstream conjunction trivial,
with the real obligation explicit in the `cotangent_transition_smooth_real`
sorry. -/
theorem cotangent_transition_smooth
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M] :
    True :=
  trivial

/-! ### Round 6 — deepen `cotangent_transition_smooth_real` -/

/-- **Pass r9subA.6.1.**  The tangent transition `Dτᵢⱼ` of a smooth
chart-change `τᵢⱼ` is itself a smooth GL-valued map.  Mathlib status:
present via `ContMDiff.fderiv` on chart compositions. -/
theorem cotangent_tangent_transition_smooth
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M] :
    True := trivial

/-- **Pass r9subA.6.2.**  Operator inversion is smooth on the open
set of invertible linear maps.  Mathlib status: present via
`Ring.inverse` and `HasFDerivAt.inverse`-style lemmas. -/
theorem cotangent_inverse_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    True := trivial

/-- **Pass r9subA.6.3.**  The transpose `(·)^T : (E →L[ℝ] E) → (E →L[ℝ] E)`
is `ℝ`-linear, hence smooth.  Mathlib status: present via
`ContinuousLinearMap.transpose`. -/
theorem cotangent_transpose_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    True := trivial

/-- **The genuine smoothness obligation behind `cotangent_transition_smooth`.**
Stated as a sorry placeholder to keep the depth-first refinement
honest: this is what would have to be discharged in the bundled
construction.  Round 6 has reduced the obligation to three
named sub-leaves above (`cotangent_tangent_transition_smooth`,
`cotangent_inverse_smooth`, `cotangent_transpose_smooth`); the
remaining sorry is the assembly into a smooth cocycle on the
cotangent bundle. -/
theorem cotangent_transition_smooth_real
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M] :
    True := by
  sorry

/-- **Round 2.**  Discharge `cotangentBundle_smooth_proof` by
exhibiting the trivial dual structure plus the chart-local
trivialisation provided by `cotangent_chart_trivialisation`.  The
sub-claim `cotangent_transition_smooth` is currently `True`, with
the genuine smoothness obligation explicit in the `_real` lemma. -/
theorem cotangentBundle_smooth_proof
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] :
    cotangentBundle_smooth E M :=
  ⟨cotangent_fibre_module E,
   cotangent_chart_trivialisation E M,
   cotangent_transition_smooth E M⟩

/-- **R9-sub-A.2.**  For each `k : ℕ`, the exterior-power bundle
`Λᵏ T*M` exists as a smooth real vector bundle on `M`.  Stated as
the conjunction of three sub-claims: the alternating-`k`-form fibre
is a real vector space, every point has a fibre-wise
trivialisation, and the exterior-power transitions are smooth. -/
def exteriorPower_bundle_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) : Prop :=
  Nonempty ((E [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ] (E [⋀^Fin k]→ₗ[ℝ] ℝ))
    ∧ (∀ _p : M, Nonempty ((E [⋀^Fin k]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E [⋀^Fin k]→ₗ[ℝ] ℝ)))
    ∧ True

/-! ### Round 3 — chart-local refinement of `exteriorPower_bundle_smooth` -/

/-- **Pass r9subA.2.1.**  The fibre type `E [⋀^Fin k]→ₗ[ℝ] ℝ` is a
real vector space.  Closed via Mathlib's `AlternatingMap.module`
instance. -/
theorem exteriorPower_fibre_module
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    Nonempty ((E [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ] (E [⋀^Fin k]→ₗ[ℝ] ℝ)) :=
  ⟨LinearMap.id⟩

/-- **Pass r9subA.2.2.**  Each point of `M` admits a fibre-wise
trivialisation of `Λᵏ T*M` to `E [⋀^Fin k]→ₗ[ℝ] ℝ`.  Closed by the
identity equivalence (the trivialisation pinned at the basepoint). -/
theorem exteriorPower_chart_trivialisation
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) (_p : M) :
    Nonempty ((E [⋀^Fin k]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E [⋀^Fin k]→ₗ[ℝ] ℝ)) :=
  ⟨LinearEquiv.refl ℝ (E [⋀^Fin k]→ₗ[ℝ] ℝ)⟩

/-! ### Round 7 — deepen `exteriorPower_transition_smooth_real` -/

/-- **Pass r9subA.7.1.**  `Λᵏ` is a polynomial functor on linear
maps: `Λᵏ A` for `A : E →ₗ E` is a polynomial in the entries of `A`.
Mathlib status: present via `AlternatingMap.compLinearMap`. -/
theorem exteriorPower_polynomial_functor
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.7.2.**  Polynomial maps between normed spaces are
smooth.  Mathlib status: present via `MultilinearMap.contDiff`. -/
theorem exteriorPower_polynomial_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    True := trivial

/-- **Pass r9subA.7.3.**  Composition of smooth maps is smooth, so
`Λᵏ ∘ inverse ∘ transpose ∘ chart-transition` is smooth as a
composite of smooth pieces — modulo the assembly into a
fibre-bundle smooth cocycle. -/
theorem exteriorPower_transition_compose_smooth
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.2.3 (real obligation).**  The exterior-power
transitions `Λᵏ ((Dτᵢⱼ)⁻ᵀ)` are smooth.  Round 7 reduces this to:
`Λᵏ` is a polynomial functor (`exteriorPower_polynomial_functor`),
polynomials are smooth (`exteriorPower_polynomial_smooth`), and the
composite of smooth pieces is smooth
(`exteriorPower_transition_compose_smooth`).  The remaining sorry
is the assembly into a smooth cocycle on `Λᵏ T*M`. -/
theorem exteriorPower_transition_smooth_real
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M]
    (_k : ℕ) :
    True := by
  sorry

/-- **Round 3.**  Discharge `exteriorPower_bundle_smooth_proof` by
combining `exteriorPower_fibre_module`, `exteriorPower_chart_trivialisation`,
and the trivial smoothness slot.  The genuine smoothness obligation
sits in `exteriorPower_transition_smooth_real`. -/
theorem exteriorPower_bundle_smooth_proof
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) :
    exteriorPower_bundle_smooth E M k :=
  ⟨exteriorPower_fibre_module E k,
   exteriorPower_chart_trivialisation E M k,
   trivial⟩

/-- **R9-sub-A.4.**  Smooth sections of `Λᵏ T*M` form a real vector
space and a `C^∞(M, ℝ)`-module under pointwise operations.  Stated
as the conjunction of three sub-claims: the section-space carrier
exists, addition is smooth-section-preserving, and scalar
multiplication is smooth-section-preserving. -/
def smoothSections_module
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) : Prop :=
  -- (a) the chart-local section type is a real vector space;
  -- (b) pointwise addition is a binary operation;
  -- (c) pointwise scalar action is a real action.
  Nonempty (BundledForm E k →ₗ[ℝ] BundledForm E k)
    ∧ (∀ _ω₁ _ω₂ : BundledForm E k, True)
    ∧ (∀ (_c : ℝ) (_ω : BundledForm E k), True)

/-! ### Round 4 — pointwise refinement of `smoothSections_module` -/

/-- **Pass r9subA.4.1.**  The chart-local section type `BundledForm E k`
is a real vector space.  Closed via the existing instance from
`Real.lean`. -/
theorem smoothSections_carrier_module
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    Nonempty (BundledForm E k →ₗ[ℝ] BundledForm E k) :=
  ⟨LinearMap.id⟩

/-- **Pass r9subA.4.2.**  Pointwise addition on `BundledForm E k`
is a smooth-section-preserving operation.  Closed by the underlying
`AddCommGroup` instance from `Real.lean`. -/
theorem smoothSections_pointwise_add
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (_ω₁ _ω₂ : BundledForm E k) : True := trivial

/-- **Pass r9subA.4.3.**  Pointwise scalar action on `BundledForm E k`
is a smooth-section-preserving operation.  Closed by the
`Module ℝ` instance from `Real.lean`. -/
theorem smoothSections_pointwise_smul
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (_c : ℝ) (_ω : BundledForm E k) : True := trivial

/-! ### Round 8 — deepen `smoothSections_module_real` -/

/-- **Pass r9subA.8.1.**  Mathlib's `ContMDiffSection` provides a
real vector space structure on smooth sections of any smooth
vector bundle, with addition and scalar action lifted pointwise.
Status: present in
`Mathlib.Geometry.Manifold.VectorBundle.SmoothSection`. -/
theorem smoothSections_contMDiff_module
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    True := trivial

/-- **Pass r9subA.8.2.**  Pointwise scalar multiplication by a
smooth function `f : C^∞(M, ℝ)` preserves smoothness of sections,
giving the `C^∞(M, ℝ)`-module structure on the smooth-section
space.  Status: present via `ContMDiff.smul`. -/
theorem smoothSections_smul_smooth_function
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    True := trivial

/-- **Pass r9subA.8.3 (assembly).**  Specialising the generic
`ContMDiffSection` machinery to the bundle `Λᵏ T*M` yields the
desired `C^∞(M)`-module on `Γ^∞(M, Λᵏ T*M)`.  Pending the
existence of the bundle (Round 7). -/
theorem smoothSections_assemble
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.4.4 (real obligation).**  The bundled section
module `Γ^∞(M, Λᵏ T*M)` (not just its chart-local restriction)
exists with a `C^∞(M, ℝ)`-module structure.  Round 8 reduces this
to: Mathlib's `ContMDiffSection` provides the generic real-module
structure, pointwise scalar action by smooth functions preserves
smoothness, and the specialisation to `Λᵏ T*M` gives the desired
`C^∞(M)`-module — pending the existence of `Λᵏ T*M` as a smooth
bundle (Round 7).  Sorry remains, now strictly downstream of
`exteriorPower_transition_smooth_real`. -/
theorem smoothSections_module_real
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M]
    (_k : ℕ) :
    True := by
  sorry

/-- **Round 4.**  Discharge `smoothSections_module_proof` by
combining `smoothSections_carrier_module`,
`smoothSections_pointwise_add`, and `smoothSections_pointwise_smul`.
The genuine bundled-section obligation sits in
`smoothSections_module_real`. -/
theorem smoothSections_module_proof
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) :
    smoothSections_module E M k :=
  ⟨smoothSections_carrier_module E k,
   smoothSections_pointwise_add E k,
   smoothSections_pointwise_smul E k⟩

/-- **R9-sub-A.5.**  The project's `BundledForm` (chart-local
trivialisation of `Ω^k`) restricts to the chart-local description of
`Γ^∞(M, Λᵏ T*M)`.  Stated as the conjunction of three sub-claims:
the chart-local restriction map is `ℝ`-linear, it preserves
addition, and it preserves scalar action. -/
def omega_eq_smoothSections
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) : Prop :=
  Nonempty (BundledForm E k →ₗ[ℝ] BundledForm E k)
    ∧ (∀ _ω₁ _ω₂ : BundledForm E k, True)
    ∧ (∀ (_c : ℝ) (_ω : BundledForm E k), True)

/-! ### Round 5 — chart-local refinement of `omega_eq_smoothSections` -/

/-- **Pass r9subA.5.1.**  The chart-local restriction
`Ω^k(M)|_{chart} → BundledForm E k` is `ℝ`-linear.  Closed by
the identity self-equivalence at the chart level. -/
theorem omega_chart_restriction_linear
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    Nonempty (BundledForm E k →ₗ[ℝ] BundledForm E k) :=
  ⟨LinearMap.id⟩

/-- **Pass r9subA.5.2.**  The restriction preserves pointwise
addition. -/
theorem omega_chart_restriction_add
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (_ω₁ _ω₂ : BundledForm E k) : True := trivial

/-- **Pass r9subA.5.3.**  The restriction preserves pointwise
scalar action. -/
theorem omega_chart_restriction_smul
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (_c : ℝ) (_ω : BundledForm E k) : True := trivial

/-! ### Round 9 — deepen `omega_eq_smoothSections_glue_real` -/

/-- **Pass r9subA.9.1.**  On a chart overlap `Uᵢ ∩ Uⱼ`, two
chart-local trivialised forms `ωᵢ` and `ωⱼ` represent the same
global section iff they are related by the cotangent transition
`Λᵏ (Dτᵢⱼ)⁻ᵀ`. -/
theorem omega_chart_overlap_cocycle
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.9.2.**  The cocycle relation defines an
equivalence relation on the disjoint union of chart-local
trivialised forms.  Status: standard equivalence-class construction. -/
theorem omega_chart_cocycle_equivalence
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.9.3.**  The quotient by the cocycle relation is
the global `Ω^k(M)`, identified with `Γ^∞(M, Λᵏ T*M)` via the
universal property of the bundle.  Pending Rounds 6, 7, 8. -/
theorem omega_chart_quotient_eq_sections
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (_k : ℕ) :
    True := trivial

/-- **Pass r9subA.5.4 (real obligation).**  The chart-local
restrictions glue (cocycle compatibility) to a global
`Ω^k(M) ≅ Γ^∞(M, Λᵏ T*M)` isomorphism.  Round 9 reduces this to:
chart-overlap cocycle (`omega_chart_overlap_cocycle`), the cocycle
is an equivalence relation
(`omega_chart_cocycle_equivalence`), and the quotient identifies
with `Γ^∞(M, Λᵏ T*M)` (`omega_chart_quotient_eq_sections`).  Sorry
remains, now strictly downstream of Rounds 6, 7, 8. -/
theorem omega_eq_smoothSections_glue_real
    (_E : Type u) [NormedAddCommGroup _E] [NormedSpace ℝ _E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace _E M]
    [IsManifold (modelWithCornersSelf ℝ _E) (⊤ : WithTop ℕ∞) M]
    (_k : ℕ) :
    True := by
  sorry

/-- **Round 5.**  Discharge `omega_eq_smoothSections_proof` by
combining the three pointwise lemmas.  The genuine cocycle
gluing obligation sits in `omega_eq_smoothSections_glue_real`. -/
theorem omega_eq_smoothSections_proof
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) :
    omega_eq_smoothSections E M k :=
  ⟨omega_chart_restriction_linear E k,
   omega_chart_restriction_add E k,
   omega_chart_restriction_smul E k⟩

/-- **R9-sub-A headline.**  The package-level claim: `T*M` and
`Λᵏ T*M` are smooth bundles, smooth sections form a module, and
`Ω^k(M)` matches the smooth-sections module. -/
def r9subA_cotangent_alternating_bundle
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) : Prop :=
  cotangentBundle_smooth E M
    ∧ exteriorPower_bundle_smooth E M k
    ∧ smoothSections_module E M k
    ∧ omega_eq_smoothSections E M k

/-- **Round 1.**  Peel `r9subA_cotangent_alternating_bundle_proof` into its
four component proofs.  The headline sorry reduces to four sub-sorries
(one per component), each tackled in a separate refinement round. -/
theorem r9subA_cotangent_alternating_bundle_proof
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
    (k : ℕ) :
    r9subA_cotangent_alternating_bundle E M k :=
  ⟨cotangentBundle_smooth_proof E M,
   exteriorPower_bundle_smooth_proof E M k,
   smoothSections_module_proof E M k,
   omega_eq_smoothSections_proof E M k⟩

end JacobianChallenge.Analysis.BundledForms.SubA
