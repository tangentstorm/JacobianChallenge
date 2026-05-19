import Jacobian.Periods.PullbackNaturality
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Mathlib endpoints for active numbered chains

These declarations are bottom-up wrappers around actual Mathlib/project
constants named as endpoints in the active blueprint chains.  They do not
prove the intervening classical reductions; they make the claimed terminal
statements explicit and buildable so the blueprint can point to real Lean
objects instead of generated placeholder hooks.
-/

namespace JacobianChallenge.Blueprint.MathlibEndpoints

open scoped Interval

/-! ## Trace-form chain endpoints (`trf`) -/

theorem mem_symmetricSubalgebra_iff_isSymmetric
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  MvPolynomial.mem_symmetricSubalgebra p

theorem elementarySymmetric_isSymmetric
    (σ R : Type*) [CommSemiring R] [Fintype σ] (n : ℕ) :
    (MvPolynomial.esymm σ R n).IsSymmetric :=
  MvPolynomial.esymm_isSymmetric σ R n

noncomputable def elementarySymmetricAlgEquiv
    (σ R : Type*) {n : ℕ} [Fintype σ] [CommRing R]
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial.symmetricSubalgebra σ R :=
  MvPolynomial.esymmAlgEquiv σ R hn

def continuousLinearMap_compFormalMultilinearSeries
    {𝕜 E F G : Type*} [Semiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
    [AddCommMonoid G] [Module 𝕜 G] [TopologicalSpace G]
    [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]
    (g : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  g.compFormalMultilinearSeries p

theorem continuousLinearMap_comp_hasFPowerSeriesOnBall
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {x : E} {r : ENNReal}
    (g : F →L[𝕜] G) (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r :=
  g.comp_hasFPowerSeriesOnBall h

theorem symmetricPolynomial_mem_symmetricSubalgebra
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  MvPolynomial.mem_symmetricSubalgebra p

/-! ## Period-naturality chain endpoints (`pn`) -/

noncomputable def integerSingularHomologyFunctorDegreeOne :
    CategoryTheory.Functor (ModuleCat ℤ) (CategoryTheory.Functor TopCat (ModuleCat ℤ)) :=
  AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1

theorem greenTheorem_rectangle_off_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ × ℝ → E) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E)
    (a b : ℝ × ℝ) (hle : a ≤ b) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Set.Icc a b)) (Hcg : ContinuousOn g (Set.Icc a b))
    (Hdf : ∀ x ∈ Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Set.Icc a b)) :
    (∫ x in Set.Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) -
        ∫ y in a.2..b.2, f (a.1, y) :=
  MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    f g f' g' a b hle s hs Hcf Hcg Hdf Hdg Hi

/-! ## Path-cover chain-rule endpoints (`pcr`) -/

theorem hasDerivAt_comp_chainRule
    {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    {h : 𝕜 → 𝕜'} {g : 𝕜' → 𝕜'} {h' g' : 𝕜'} {x : 𝕜}
    (hg : HasDerivAt g g' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g ∘ h) (g' * h') x :=
  HasDerivAt.comp x hg hh

theorem intervalIntegral_add_adjacent_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : ℝ} {f : ℝ → E} {μ : MeasureTheory.Measure ℝ}
    (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

theorem lebesgueNumberLemma_metric
    {α : Type*} [PseudoMetricSpace α] {s : Set α} {ι : Sort*} {c : ι → Set α}
    (hs : IsCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ δ > 0, ∀ x ∈ s, ∃ i, Metric.ball x δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs hc₁ hc₂

theorem contMDiff_continuous
    {𝕜 E H M E' H' M' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} {n : WithTop ℕ∞} (hf : ContMDiff I I' n f) :
    Continuous f :=
  hf.continuous

theorem path_map_trans
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y z : X} (γ : Path x y) (γ' : Path y z)
    {f : X → Y} (h : Continuous f) :
    (γ.trans γ').map h = (γ.map h).trans (γ'.map h) :=
  Path.map_trans γ γ' h

theorem path_map_symm
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  Path.map_symm γ h

theorem hasDerivAt_comp_intervalEndpoint
    {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    {h : 𝕜 → 𝕜'} {g : 𝕜' → 𝕜'} {h' g' : 𝕜'} {x : 𝕜}
    (hg : HasDerivAt g g' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g ∘ h) (g' * h') x :=
  HasDerivAt.comp x hg hh

/-! ## Pullback-descent chain endpoints (`pdp`) -/

def quotientAddGroup_lift_descends
    {G M : Type*} [AddGroup G] [AddMonoid M]
    (N : AddSubgroup G) [N.Normal] (φ : G →+ M) (HN : N ≤ φ.ker) :
    G ⧸ N →+ M :=
  QuotientAddGroup.lift N φ HN

theorem matrix_transpose_mul
    {l m n α : Type*} [AddCommMonoid α] [CommMagma α] [Fintype n]
    (M : Matrix m n α) (N : Matrix n l α) :
    (M * N).transpose = N.transpose * M.transpose :=
  Matrix.transpose_mul M N

theorem basis_equivFun_apply
    {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Finite ι] (b : Module.Basis ι R M) (u : M) :
    b.equivFun u = b.repr u :=
  Module.Basis.equivFun_apply b u

theorem basis_dualBasis_apply_self
    {ι R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] [Finite ι] (b : Module.Basis ι R M) (i j : ι) :
    (b.dualBasis i) (b j) = if j = i then 1 else 0 :=
  Module.Basis.dualBasis_apply_self b i j

theorem linearMap_dualMap_apply
    {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    (f : M₁ →ₗ[R] M₂) (g : Module.Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  LinearMap.dualMap_apply f g x

end JacobianChallenge.Blueprint.MathlibEndpoints
