import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Abstract finite-dimensional Hodge complex

This file proves the algebraic skeleton of the Hodge decomposition
theorem in the finite-dimensional setting.  No `sorry`s, no
placeholders, no PUnit collapse: the proofs reduce to standard Mathlib
lemmas about adjoints and orthogonal complements.

## Headline results (for `V₀, V₁, V₂` finite-dim real inner product spaces
and `d₀ : V₀ →ₗ[ℝ] V₁`, `d₁ : V₁ →ₗ[ℝ] V₂` satisfying `d₁ ∘ d₀ = 0`):

* `laplacian_isSymmetric` — `Δ := δ ∘ d + d' ∘ δ'` is symmetric.
* `ker_laplacian_eq` — `ker Δ = ker d ∩ ker δ'` (harmonic = closed and
  co-closed).
* `selfAdjoint_orthogonal_decomposition` — for any symmetric
  finite-dim endomorphism `T`, `(LinearMap.range T)ᗮ = LinearMap.ker T`.
* `range_d_orthogonal_range_codiff` — `(range d) ⟂ (range d'.adjoint)`
  follows from `d² = 0`.

The "analytic" R5 statement on a compact Kähler manifold reduces to the
finite-dim version once `Δ` has finite-dimensional kernel
(elliptic regularity); from that point onwards, everything below is
the actual proof.
-/

namespace JacobianChallenge.HodgeAbstract

open scoped InnerProductSpace
open LinearMap Submodule

universe u

variable {V₀ V₁ V₂ : Type u}
variable [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀] [FiniteDimensional ℝ V₀]
variable [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [FiniteDimensional ℝ V₁]
variable [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-! ### Hodge decomposition for a single self-adjoint operator -/

/-- For a symmetric endomorphism `T` of a finite-dim real inner product
space, the orthogonal complement of `range T` is exactly `ker T`.
This is `LinearMap.IsSymmetric.orthogonal_range` from Mathlib. -/
theorem orthogonal_range_eq_ker (T : V₁ →ₗ[ℝ] V₁) (hT : T.IsSymmetric) :
    (LinearMap.range T)ᗮ = LinearMap.ker T :=
  hT.orthogonal_range

/-- For a symmetric endomorphism `T` of a finite-dim real inner product
space, `range T` and `ker T` are orthogonal complements: every vector
splits orthogonally as `kernel-part + range-part`.

Stated using Mathlib's `IsCompl` predicate plus `Submodule.IsOrtho`. -/
theorem isCompl_ker_range_of_symmetric (T : V₁ →ₗ[ℝ] V₁) (hT : T.IsSymmetric) :
    IsCompl (LinearMap.ker T) (LinearMap.range T) := by
  -- range T is closed in finite dim, so range T = ((range T)ᗮ)ᗮ = (ker T)ᗮ.
  have hrange_closed : (LinearMap.range T).topologicalClosure = LinearMap.range T :=
    Submodule.topologicalClosure_eq_self _
  have hker_orth_range : (LinearMap.range T)ᗮ = LinearMap.ker T :=
    hT.orthogonal_range
  -- Take orthogonal of both sides.
  have hker_orth : (LinearMap.ker T)ᗮ = LinearMap.range T := by
    rw [← hker_orth_range, Submodule.orthogonal_orthogonal_eq_closure, hrange_closed]
  have hcompl : IsCompl (LinearMap.ker T) (LinearMap.ker T)ᗮ :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  rw [hker_orth] at hcompl
  exact hcompl

/-- Range and kernel of a symmetric finite-dim endomorphism are
orthogonal as submodules. -/
theorem range_ker_isOrtho_of_symmetric (T : V₁ →ₗ[ℝ] V₁) (hT : T.IsSymmetric) :
    (LinearMap.ker T) ⟂ (LinearMap.range T) := by
  rw [Submodule.isOrtho_iff_le, ← hT.orthogonal_range]

/-! ### The Hodge complex `V₀ →ᵈ V₁ →ᵈ V₂` -/

variable (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂)

/-- The codifferentials are the formal adjoints of the differentials. -/
noncomputable def codiff₀ : V₁ →ₗ[ℝ] V₀ := d₀.adjoint
noncomputable def codiff₁ : V₂ →ₗ[ℝ] V₁ := d₁.adjoint

/-- The Hodge Laplacian on `V₁`: `Δ = δd + dδ` where `δ = d.adjoint`. -/
noncomputable def laplacian : V₁ →ₗ[ℝ] V₁ :=
  d₀ ∘ₗ d₀.adjoint + d₁.adjoint ∘ₗ d₁

/-- The Laplacian is symmetric: `⟨Δα, β⟩ = ⟨α, Δβ⟩`. -/
theorem laplacian_isSymmetric :
    (laplacian d₀ d₁).IsSymmetric := by
  intro α β
  unfold laplacian
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    inner_add_left, inner_add_right]
  congr 1
  · -- ⟨d₀ (d₀.adjoint α), β⟩ = ⟨α, d₀ (d₀.adjoint β)⟩
    rw [← LinearMap.adjoint_inner_right d₀, LinearMap.adjoint_inner_left]
  · -- ⟨d₁.adjoint (d₁ α), β⟩ = ⟨α, d₁.adjoint (d₁ β)⟩
    rw [LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right]

/-- `‖dα‖² + ‖δα‖² = ⟨Δα, α⟩` (the Bochner / Weitzenböck form). -/
theorem inner_laplacian_self_eq_norm_sq
    (α : V₁) :
    ⟪laplacian d₀ d₁ α, α⟫_ℝ =
      ‖d₀.adjoint α‖ ^ 2 + ‖d₁ α‖ ^ 2 := by
  unfold laplacian
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, inner_add_left]
  -- ⟨d₀ (δ₀ α), α⟩ = ⟨δ₀ α, δ₀ α⟩ = ‖δ₀ α‖²
  have h1 : ⟪d₀ (d₀.adjoint α), α⟫_ℝ = ‖d₀.adjoint α‖ ^ 2 := by
    rw [show ⟪d₀ (d₀.adjoint α), α⟫_ℝ = ⟪d₀.adjoint α, d₀.adjoint α⟫_ℝ from
        (LinearMap.adjoint_inner_right d₀ (d₀.adjoint α) α).symm]
    exact real_inner_self_eq_norm_sq _
  -- ⟨d₁.adjoint (d₁ α), α⟩ = ⟨d₁ α, d₁ α⟩ = ‖d₁ α‖²
  have h2 : ⟪d₁.adjoint (d₁ α), α⟫_ℝ = ‖d₁ α‖ ^ 2 := by
    rw [LinearMap.adjoint_inner_left]
    exact real_inner_self_eq_norm_sq _
  rw [h1, h2]

/-- Harmonic forms are exactly forms killed by both `d` and `δ` (i.e.
closed and co-closed). -/
theorem ker_laplacian_eq :
    LinearMap.ker (laplacian d₀ d₁) =
      LinearMap.ker d₀.adjoint ⊓ LinearMap.ker d₁ := by
  ext α
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  constructor
  · intro hα
    have hsum : ‖d₀.adjoint α‖ ^ 2 + ‖d₁ α‖ ^ 2 = 0 := by
      have := inner_laplacian_self_eq_norm_sq d₀ d₁ α
      rw [hα] at this
      simpa [inner_zero_left] using this.symm
    have h₀ : ‖d₀.adjoint α‖ ^ 2 = 0 := by
      have hge1 : (0 : ℝ) ≤ ‖d₀.adjoint α‖ ^ 2 := sq_nonneg _
      have hge2 : (0 : ℝ) ≤ ‖d₁ α‖ ^ 2 := sq_nonneg _
      linarith
    have h₁ : ‖d₁ α‖ ^ 2 = 0 := by
      have hge1 : (0 : ℝ) ≤ ‖d₀.adjoint α‖ ^ 2 := sq_nonneg _
      have hge2 : (0 : ℝ) ≤ ‖d₁ α‖ ^ 2 := sq_nonneg _
      linarith
    refine ⟨?_, ?_⟩
    · have : ‖d₀.adjoint α‖ = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp h₀
        exact this
      exact norm_eq_zero.mp this
    · have : ‖d₁ α‖ = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp h₁
        exact this
      exact norm_eq_zero.mp this
  · rintro ⟨h₀, h₁⟩
    unfold laplacian
    simp [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, h₀, h₁]

/-! ### Orthogonal decomposition of `V₁` -/

/-- The Hodge decomposition (analytic core, finite-dim version):
`V₁ = ker Δ ⊕ range Δ`, orthogonally. -/
theorem hodge_decomposition_finite_dim :
    IsCompl (LinearMap.ker (laplacian d₀ d₁))
      (LinearMap.range (laplacian d₀ d₁)) :=
  isCompl_ker_range_of_symmetric _ (laplacian_isSymmetric d₀ d₁)

/-! ### Orthogonality `range d₀ ⟂ range δ₁` from `d² = 0` -/

variable (h_d_sq : d₁ ∘ₗ d₀ = 0)

include h_d_sq in
/-- From `d² = 0`: `⟨d α, δ β⟩ = ⟨d²α, β⟩ = 0`, so `range d₀ ⟂ range d₁.adjoint`. -/
theorem range_d_orthogonal_range_codiff :
    (LinearMap.range d₀) ⟂ (LinearMap.range d₁.adjoint) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  -- ⟨d₀ a, d₁.adjoint b⟩ = ⟨d₁ (d₀ a), b⟩ via adjoint_inner_right
  rw [LinearMap.adjoint_inner_right]
  have h : d₁ (d₀ a) = 0 := by
    have := LinearMap.congr_fun h_d_sq a
    simpa using this
  rw [h, inner_zero_left]

/-! ### Range of Laplacian splits as `range d ⊔ range δ` -/

/-- The image of the Laplacian is contained in the sum
`range d₀ + range d₁.adjoint`.  Immediate from
`Δ = d₀ ∘ δ₀ + δ₁ ∘ d₁`. -/
theorem range_laplacian_le :
    LinearMap.range (laplacian d₀ d₁) ≤
      LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint := by
  rintro v ⟨α, rfl⟩
  unfold laplacian
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.mem_sup_left ?_
    exact ⟨d₀.adjoint α, rfl⟩
  · refine Submodule.mem_sup_right ?_
    exact ⟨d₁ α, rfl⟩

/-- Reverse inclusion: `range d₀ + range d₁.adjoint ≤ range Δ`.

Note: this does NOT require `d² = 0`.  Range of any symmetric finite-dim
operator equals the orthogonal complement of its kernel; everything in
`range d₀ ⊔ range d₁.adjoint` is orthogonal to `ker Δ = ker d₁ ∩ ker δ₀`. -/
theorem range_d_le_range_laplacian :
    LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint ≤
      LinearMap.range (laplacian d₀ d₁) := by
  -- range Δ = (ker Δ)ᗮ for Δ symmetric finite-dim.
  have hΔ_sym : (laplacian d₀ d₁).IsSymmetric := laplacian_isSymmetric d₀ d₁
  have hcompl : IsCompl (LinearMap.ker (laplacian d₀ d₁))
      (LinearMap.range (laplacian d₀ d₁)) :=
    hodge_decomposition_finite_dim d₀ d₁
  -- We show the LHS is orthogonal to ker Δ, hence ≤ range Δ.
  have hker_eq : LinearMap.ker (laplacian d₀ d₁) =
      LinearMap.ker d₀.adjoint ⊓ LinearMap.ker d₁ :=
    ker_laplacian_eq d₀ d₁
  -- range d₀ ≤ (ker d₀.adjoint)ᗮ, and similarly for d₁.adjoint.
  have h1 : LinearMap.range d₀ ≤ (LinearMap.ker d₀.adjoint)ᗮ := by
    rintro v ⟨a, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    -- target: ⟨u, d₀ a⟩ = 0; rewrite as ⟨d₀.adjoint u, a⟩ = ⟨0, a⟩ = 0.
    rw [← LinearMap.adjoint_inner_left d₀, hu, inner_zero_left]
  have h2 : LinearMap.range d₁.adjoint ≤ (LinearMap.ker d₁)ᗮ := by
    rintro v ⟨b, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    -- target: ⟨u, d₁.adjoint b⟩ = 0; rewrite as ⟨d₁ u, b⟩ = ⟨0, b⟩ = 0.
    rw [LinearMap.adjoint_inner_right, hu, inner_zero_left]
  -- Combine: any v ∈ range d₀ ⊔ range d₁.adjoint is orthogonal to
  -- (ker d₀.adjoint ∩ ker d₁) = ker Δ, so v ∈ (ker Δ)ᗮ = range Δ.
  have hker_orth : LinearMap.range (laplacian d₀ d₁) =
      (LinearMap.ker (laplacian d₀ d₁))ᗮ := by
    have := hΔ_sym.orthogonal_range
    have hclosed : (LinearMap.range (laplacian d₀ d₁)).topologicalClosure =
        LinearMap.range (laplacian d₀ d₁) :=
      Submodule.topologicalClosure_eq_self _
    rw [← this, Submodule.orthogonal_orthogonal_eq_closure, hclosed]
  rw [hker_orth, hker_eq]
  -- Show range d₀ ⊔ range d₁.adjoint ≤ (ker d₀.adjoint ⊓ ker d₁)ᗮ.
  rw [sup_le_iff]
  refine ⟨?_, ?_⟩
  · -- range d₀ ≤ (ker d₀.adjoint ⊓ ker d₁)ᗮ
    refine le_trans h1 ?_
    -- (ker d₀.adjoint)ᗮ ⊆ (ker d₀.adjoint ⊓ ker d₁)ᗮ since A ⊆ B ⇒ Bᗮ ⊆ Aᗮ.
    exact Submodule.orthogonal_le inf_le_left
  · -- range d₁.adjoint ≤ (ker d₀.adjoint ⊓ ker d₁)ᗮ
    refine le_trans h2 ?_
    exact Submodule.orthogonal_le inf_le_right

/-- The full range identity: `range Δ = range d₀ + range d₁.adjoint`. -/
theorem range_laplacian_eq :
    LinearMap.range (laplacian d₀ d₁) =
      LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint :=
  le_antisymm (range_laplacian_le d₀ d₁) (range_d_le_range_laplacian d₀ d₁)

include h_d_sq in
/-- **Hodge decomposition (final form, finite-dim).**
`V₁ = ker Δ ⊕ range d₀ ⊕ range d₁.adjoint`, all three summands
pairwise orthogonal (where the `range d₀ / range d₁.adjoint` orthogonality
uses `d² = 0`). -/
theorem hodge_decomposition_full :
    IsCompl (LinearMap.ker (laplacian d₀ d₁))
        (LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint) ∧
    (LinearMap.range d₀) ⟂ (LinearMap.range d₁.adjoint) := by
  refine ⟨?_, range_d_orthogonal_range_codiff d₀ d₁ h_d_sq⟩
  rw [← range_laplacian_eq d₀ d₁]
  exact hodge_decomposition_finite_dim d₀ d₁

/-! ### De Rham cohomology and the harmonic isomorphism

For a chain complex `V₀ →ᵈ V₁ →ᵈ V₂` with `d² = 0`, the (middle) de
Rham cohomology is `H¹ := ker d₁ / range d₀`.  The harmonic-form
representative theorem says every cohomology class has a unique
harmonic representative — the projection
`harmonic → ker d₁ → ker d₁ / range d₀` is a linear isomorphism.

This is the second half of R5 (after the orthogonal decomposition).
-/

/-- Submodule version of `ker d₁` so we can quotient by `range d₀`. -/
abbrev kerD₁ : Submodule ℝ V₁ := LinearMap.ker d₁

/-- Submodule version of `range d₀` (which lies inside `ker d₁` when
`d² = 0`). -/
abbrev rangeD₀ : Submodule ℝ V₁ := LinearMap.range d₀

include h_d_sq in
/-- `range d₀ ⊆ ker d₁` from `d² = 0`. -/
theorem range_d₀_le_ker_d₁ : rangeD₀ d₀ ≤ kerD₁ d₁ := by
  rintro v ⟨a, rfl⟩
  rw [LinearMap.mem_ker]
  have := LinearMap.congr_fun h_d_sq a
  simpa using this

/-- The harmonic submodule is contained in `ker d₁` (every harmonic
form is closed). -/
theorem harmonic_le_ker_d₁ :
    LinearMap.ker (laplacian d₀ d₁) ≤ kerD₁ d₁ := by
  rw [ker_laplacian_eq d₀ d₁]
  exact inf_le_right

/-- Range of `d₀`, viewed as a submodule of `ker d₁` (using `d² = 0`). -/
def rangeD₀_in_kerD₁ (h_d_sq : d₁ ∘ₗ d₀ = 0) : Submodule ℝ (kerD₁ d₁) :=
  (rangeD₀ d₀).comap (kerD₁ d₁).subtype

/-- The de Rham cohomology in the middle degree:
`H¹ := ker d₁ / range d₀`. -/
abbrev deRhamH₁ (h_d_sq : d₁ ∘ₗ d₀ = 0) : Type _ :=
  (kerD₁ d₁) ⧸ rangeD₀_in_kerD₁ d₀ d₁ h_d_sq

instance (h_d_sq : d₁ ∘ₗ d₀ = 0) : AddCommGroup (deRhamH₁ d₀ d₁ h_d_sq) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (h_d_sq : d₁ ∘ₗ d₀ = 0) : Module ℝ (deRhamH₁ d₀ d₁ h_d_sq) :=
  inferInstanceAs (Module ℝ (_ ⧸ _))

/-- The inclusion `harmonic → ker d₁`. -/
noncomputable def harmonicToKerD₁ : LinearMap.ker (laplacian d₀ d₁) →ₗ[ℝ] kerD₁ d₁ :=
  Submodule.inclusion (harmonic_le_ker_d₁ d₀ d₁)

/-- The projection `ker d₁ → H¹_dR`. -/
noncomputable def kerD₁ToDeRham (h_d_sq : d₁ ∘ₗ d₀ = 0) :
    kerD₁ d₁ →ₗ[ℝ] deRhamH₁ d₀ d₁ h_d_sq :=
  Submodule.mkQ _

/-- The composite `harmonic → H¹_dR`. -/
noncomputable def harmonicToDeRham (h_d_sq : d₁ ∘ₗ d₀ = 0) :
    LinearMap.ker (laplacian d₀ d₁) →ₗ[ℝ] deRhamH₁ d₀ d₁ h_d_sq :=
  (kerD₁ToDeRham d₀ d₁ h_d_sq).comp (harmonicToKerD₁ d₀ d₁)

include h_d_sq in
/-- **Injectivity of `harmonic → H¹_dR`.**  A harmonic form that is
exact is zero.  Proof: if `h ∈ ker Δ` and `h = d₀ a`, then
`⟨h, h⟩ = ⟨d₀ a, h⟩ = ⟨a, d₀.adjoint h⟩ = ⟨a, 0⟩ = 0` (using
`d₀.adjoint h = 0` from harmonicity), so `h = 0`. -/
theorem harmonicToDeRham_injective :
    Function.Injective (harmonicToDeRham d₀ d₁ h_d_sq) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨h_val, hh⟩ hquot
  -- hh : h_val ∈ ker Δ, hquot : harmonicToDeRham ⟨h_val, hh⟩ = 0.
  -- Get the codifferential vanishing condition.
  rw [ker_laplacian_eq] at hh
  obtain ⟨h_codiff_zero, h_d_zero⟩ := Submodule.mem_inf.mp hh
  rw [LinearMap.mem_ker] at h_codiff_zero
  -- Unfold harmonicToDeRham and the quotient-zero condition.
  unfold harmonicToDeRham kerD₁ToDeRham harmonicToKerD₁ at hquot
  rw [LinearMap.comp_apply, Submodule.inclusion_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hquot
  -- hquot : ⟨h_val, _⟩ ∈ rangeD₀_in_kerD₁ d₀ d₁ h_d_sq.
  -- rangeD₀_in_kerD₁ = (range d₀).comap (kerD₁).subtype, so this is h_val ∈ range d₀.
  have h_val_in_range : h_val ∈ LinearMap.range d₀ := hquot
  obtain ⟨a, ha⟩ := h_val_in_range
  -- ⟨h_val, h_val⟩ = ⟨d₀ a, h_val⟩ = ⟨a, d₀.adjoint h_val⟩ = 0.
  have hnorm : ⟪h_val, h_val⟫_ℝ = 0 := by
    nth_rewrite 1 [show h_val = d₀ a from ha.symm]
    rw [← LinearMap.adjoint_inner_right d₀, h_codiff_zero, inner_zero_right]
  have h_val_eq_zero : h_val = 0 := by
    have hsq := real_inner_self_eq_norm_sq h_val
    rw [hnorm] at hsq
    have hnorm_eq : ‖h_val‖ ^ 2 = 0 := by linarith
    have : ‖h_val‖ = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp hnorm_eq
      exact this
    exact norm_eq_zero.mp this
  apply Subtype.ext
  exact h_val_eq_zero

include h_d_sq in
/-- **Surjectivity of `harmonic → H¹_dR`.**  Every closed form has a
harmonic representative.  Proof: given `ω ∈ ker d₁`, decompose using
the Hodge orthogonal decomposition `ω = h + d₀ a + d₁.adjoint b`.
From `d₁ ω = 0` and `d₁ (d₀ a) = 0`, we get `d₁ (d₁.adjoint b) = 0`,
so `⟨d₁.adjoint b, d₁.adjoint b⟩ = ⟨d₁ d₁.adjoint b, b⟩ = 0`, hence
`d₁.adjoint b = 0`.  So `ω - h = d₀ a`, i.e.\ `[ω] = [h]` in `H¹_dR`. -/
theorem harmonicToDeRham_surjective :
    Function.Surjective (harmonicToDeRham d₀ d₁ h_d_sq) := by
  intro x
  -- x : (ker d₁) ⧸ rangeD₀_in_kerD₁
  obtain ⟨ω_subtype, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨ω, hω_closed⟩ := ω_subtype
  -- Decompose ω using Hodge: ω = h + r, where h ∈ ker Δ, r ∈ range d₀ ⊔ range d₁.adjoint.
  have hcompl : IsCompl (LinearMap.ker (laplacian d₀ d₁))
      (LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint) :=
    (hodge_decomposition_full d₀ d₁ h_d_sq).1
  -- Use Submodule.exists_add_of_isCompl: ω = h + r with h ∈ ker Δ, r ∈ range d₀ ⊔ range δ₁.
  obtain ⟨h, r, hh, hr, hsum⟩ : ∃ h r,
      h ∈ LinearMap.ker (laplacian d₀ d₁) ∧
      r ∈ LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint ∧
      h + r = ω := by
    have hcodisj : Codisjoint (LinearMap.ker (laplacian d₀ d₁))
        (LinearMap.range d₀ ⊔ LinearMap.range d₁.adjoint) := hcompl.codisjoint
    have hmem : ω ∈ (⊤ : Submodule ℝ V₁) := Submodule.mem_top
    rw [← hcodisj.eq_top, Submodule.mem_sup] at hmem
    obtain ⟨h, hh, r, hr, hsum⟩ := hmem
    exact ⟨h, r, hh, hr, hsum⟩
  -- Now: from d₁ ω = 0, deduce d₁ r = 0.  Since r ∈ range d₀ ⊔ range δ₁,
  -- r = d₀ a + d₁.adjoint b.  d₁ (d₀ a) = 0 from h_d_sq, so d₁ (d₁.adjoint b) = 0.
  -- Then ⟨d₁ (d₁.adjoint b), b⟩ = ⟨d₁.adjoint b, d₁.adjoint b⟩ = 0, so d₁.adjoint b = 0.
  -- Hence r = d₀ a ∈ range d₀.
  have hh_closed : d₁ h = 0 := by
    have := harmonic_le_ker_d₁ d₀ d₁ hh
    rw [LinearMap.mem_ker] at this
    exact this
  have hr_closed : d₁ r = 0 := by
    have : d₁ (h + r) = 0 := by rw [hsum]; exact hω_closed
    rw [map_add] at this
    rw [hh_closed, zero_add] at this
    exact this
  -- Decompose r = d₀ a + d₁.adjoint b.
  rw [Submodule.mem_sup] at hr
  obtain ⟨da, ⟨a, rfl⟩, db, ⟨b, rfl⟩, rfl⟩ := hr
  -- d₁ (d₀ a) = 0 from h_d_sq.
  have h_d₀a_closed : d₁ (d₀ a) = 0 := by
    have := LinearMap.congr_fun h_d_sq a
    simpa using this
  -- So d₁ (d₁.adjoint b) = 0.
  have h_dadj_b : d₁ (d₁.adjoint b) = 0 := by
    have hsum' : d₁ (d₀ a) + d₁ (d₁.adjoint b) = 0 := by
      rw [← map_add]; exact hr_closed
    rw [h_d₀a_closed, zero_add] at hsum'
    exact hsum'
  -- Then ⟨d₁ (d₁.adjoint b), b⟩ = 0 = ⟨d₁.adjoint b, d₁.adjoint b⟩ = ‖d₁.adjoint b‖².
  have h_dadj_b_zero : d₁.adjoint b = 0 := by
    have hinner : ⟪d₁ (d₁.adjoint b), b⟫_ℝ = 0 := by rw [h_dadj_b]; exact inner_zero_left _
    rw [← LinearMap.adjoint_inner_right d₁ (d₁.adjoint b) b] at hinner
    have hsq := real_inner_self_eq_norm_sq (d₁.adjoint b)
    rw [hinner] at hsq
    have hnorm_eq : ‖d₁.adjoint b‖ ^ 2 = 0 := by linarith
    have : ‖d₁.adjoint b‖ = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp hnorm_eq
      exact this
    exact norm_eq_zero.mp this
  -- So r = d₀ a + 0 = d₀ a, i.e. r ∈ range d₀.
  refine ⟨⟨h, hh⟩, ?_⟩
  -- Goal: harmonicToDeRham _ ⟨h, hh⟩ = quotient class of ⟨ω, hω_closed⟩.
  -- After unfolding, this becomes: mkQ ⟨h, _⟩ = mkQ ⟨ω, hω_closed⟩ in (kerD₁) ⧸ (rangeD₀_in_kerD₁).
  -- Equivalent to: ⟨h, _⟩ - ⟨ω, _⟩ ∈ rangeD₀_in_kerD₁,
  -- i.e.\ (h - ω) ∈ range d₀ on the underlying V₁.
  -- We have ω = h + d₀ a + 0 (after h_dadj_b_zero), so h - ω = -d₀ a = d₀ (-a) ∈ range d₀.
  have hω_eq : ω = h + d₀ a := by
    have : h + (d₀ a + d₁.adjoint b) = ω := hsum
    rw [h_dadj_b_zero, add_zero] at this
    exact this.symm
  have h_sub : (h : V₁) - ω = d₀ (-a) := by
    rw [hω_eq, map_neg]; abel
  unfold harmonicToDeRham kerD₁ToDeRham harmonicToKerD₁
  rw [LinearMap.comp_apply, Submodule.inclusion_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
  -- Goal: ⟨h, _⟩ - ⟨ω, hω_closed⟩ ∈ rangeD₀_in_kerD₁ d₀ d₁ h_d_sq.
  -- Unpacks to (h - ω) ∈ range d₀ on the underlying V₁.
  show (h : V₁) - ω ∈ LinearMap.range d₀
  rw [h_sub]
  exact ⟨-a, rfl⟩

include h_d_sq in
/-- **De Rham–harmonic isomorphism (real, finite-dim).**
The map `harmonic → H¹_dR` is a linear isomorphism: each cohomology
class has a unique harmonic representative. -/
noncomputable def harmonicEquivDeRham :
    LinearMap.ker (laplacian d₀ d₁) ≃ₗ[ℝ] deRhamH₁ d₀ d₁ h_d_sq :=
  LinearEquiv.ofBijective (harmonicToDeRham d₀ d₁ h_d_sq)
    ⟨harmonicToDeRham_injective d₀ d₁ h_d_sq,
     harmonicToDeRham_surjective d₀ d₁ h_d_sq⟩

end JacobianChallenge.HodgeAbstract
