import Jacobian.Periods.PrismChainBridge
import Jacobian.Periods.DivFinIcc
import Jacobian.Periods.IntegralOneCycle
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Path → singular 1-cycle conversion

Increment C infrastructure: convert a `Path a b` on `X` into a singular
1-simplex `SingSimplex 1 X = C(stdSimplex ℝ (Fin 2), X)`.

This is the type-level bridge needed to refine `loopToIntegralOneCycle`
(currently `:= 0` in `DeRhamComparisonMap.lean`) into a real
subdivision-based cycle. The full subdivision construction (chart-cover
partition + chain-level boundary telescoping) is the substantive
remaining work for Increment C; this file provides the base conversion.
-/

namespace JacobianChallenge.Periods

open CategoryTheory

/-- Convert a `Path a b` on `X` into a singular 1-simplex in `X`,
via the homeomorphism `stdSimplex ℝ (Fin 2) ≃ₜ unitInterval`. -/
noncomputable def Path.toSingSimplex {Y : Type} [TopologicalSpace Y] {a b : Y}
    (γ : _root_.Path a b) : SingSimplex 1 Y :=
  γ.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The constant singular 0-simplex at a point `y : Y`. -/
noncomputable def constSimplex0 {Y : Type} [TopologicalSpace Y] (y : Y) :
    SingSimplex 0 Y := ContinuousMap.const _ y

/-- `stdSimplex ℝ (Fin 1)` has a unique point — the vertex `Pi.single 0 1`. -/
lemma stdSimplex_fin_one_subsingleton :
    Subsingleton (stdSimplex ℝ (Fin 1)) := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  ext i
  have hi : i = 0 := by
    rcases i with ⟨v, hv⟩
    have : v = 0 := by omega
    cases this; rfl
  have ha := a.2.2
  have hb := b.2.2
  simp at ha hb
  rw [hi, ha, hb]

/-- Precomposing a singular 1-simplex `s` with the `j`-th face inclusion
`stdSimplexFaceInclusion 0 j : Δ⁰ → Δ¹` yields the constant 0-simplex at
`s (vertex (succAbove j 0))`: `Δ⁰` is a subsingleton, so any continuous
map out of it is constant. -/
theorem comp_face_eq_constSimplex0 {Y : Type} [TopologicalSpace Y]
    (s : SingSimplex 1 Y) (j : Fin 2) :
    s.comp (stdSimplexFaceInclusion 0 j) =
      constSimplex0 (s (stdSimplex.vertex (Fin.succAbove j 0))) := by
  haveI := stdSimplex_fin_one_subsingleton
  ext x
  have hx : x = stdSimplex.vertex 0 := Subsingleton.elim _ _
  rw [hx]
  have hface :
      (stdSimplexFaceInclusion 0 j) (stdSimplex.vertex 0) =
        stdSimplex.vertex (Fin.succAbove j 0) := by
    simp [stdSimplexFaceInclusion]
  show s ((stdSimplexFaceInclusion 0 j) (stdSimplex.vertex 0)) = _
  rw [hface]
  rfl

/-- Value of `toSingSimplex γ` at the 0-vertex of Δ¹ is the source `a`. -/
@[simp] theorem Path.toSingSimplex_vertex_zero {Y : Type} [TopologicalSpace Y]
    {a b : Y} (γ : _root_.Path a b) :
    Path.toSingSimplex γ (stdSimplex.vertex 0) = a := by
  show γ (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 0)) = a
  rw [show stdSimplex.vertex (S := ℝ) (0 : Fin 2) =
      ⟨_, single_mem_stdSimplex _ 0⟩ from rfl,
      stdSimplexHomeomorphUnitInterval_zero, γ.source]

/-- Value of `toSingSimplex γ` at the 1-vertex of Δ¹ is the target `b`. -/
@[simp] theorem Path.toSingSimplex_vertex_one {Y : Type} [TopologicalSpace Y]
    {a b : Y} (γ : _root_.Path a b) :
    Path.toSingSimplex γ (stdSimplex.vertex 1) = b := by
  show γ (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 1)) = b
  rw [show stdSimplex.vertex (S := ℝ) (1 : Fin 2) =
      ⟨_, single_mem_stdSimplex _ 1⟩ from rfl,
      stdSimplexHomeomorphUnitInterval_one, γ.target]

/-- Element-level form of `singChain_d_basis` for `n = 0`: the boundary
of the basis chain at a 1-simplex `s` (applied to `1 : ℤ`) equals
`basis(const at s(vertex 1)) - basis(const at s(vertex 0))` (vertex 1
contributes with sign `+`, vertex 0 with sign `-`). -/
theorem singChain_d_basis_apply_one {Y : Type} [TopologicalSpace Y]
    (s : SingSimplex 1 Y) :
    ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)).d 1 0).hom
        ((singChain_basis s).hom 1) =
      (singChain_basis (constSimplex0 (s (stdSimplex.vertex 1)))).hom 1 -
      (singChain_basis (constSimplex0 (s (stdSimplex.vertex 0)))).hom 1 := by
  have hd := singChain_d_basis (X := Y) 0 s
  have happ := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ _) => f.hom 1) hd
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.coe_sum, Finset.sum_apply] at happ
  rw [Fin.sum_univ_two] at happ
  rw [comp_face_eq_constSimplex0, comp_face_eq_constSimplex0] at happ
  rw [happ]
  -- (-1)^0 • a + (-1)^1 • b = a - b, and `succAbove 0 0 = 1`, `succAbove 1 0 = 0`.
  show _ = _
  simp [Fin.succAbove]
  abel

/-- The singular 1-chain formed by subdividing a path γ into n equal
segments and summing their basis classes (each with coefficient 1). -/
noncomputable def Path.partitionChain {Y : Type} [TopologicalSpace Y]
    {a b : Y} (γ : _root_.Path a b) (n : ℕ) (hn : 0 < n) :
    ↑(singChain 1 Y) :=
  ∑ i : Fin n,
    (singChain_basis (X := Y)
      (Path.toSingSimplex
        (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                   (divFinIcc n hn (i.val + 1) i.isLt)))).hom 1

/-- **Cycle property of a loop's partition chain.** For a loop
`γ : Path x x` partitioned into `n` equal segments, the resulting
1-chain has zero boundary: telescoping `Σᵢ (γ(i+1/n) - γ(i/n)) = γ(1) - γ(0) = 0`.

Routes through `singChain_d_basis` (alternating sum of face inclusions)
+ `Finset.sum` telescoping + the loop hypothesis `γ.source = γ.target`.

Focused sub-sorry — natural classical result (boundary of a sum of
chart-supported simplices on a loop is zero by telescoping). -/
theorem Path.partitionChain_boundary_eq_zero
    {Y : Type} [TopologicalSpace Y] {x : Y} (γ : _root_.Path x x)
    (n : ℕ) (hn : 0 < n) :
    ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)).d 1 0).hom
      (Path.partitionChain γ n hn) = 0 := by
  -- Strategy: each basis simplex `sub i = toSingSimplex(γ.subpath aᵢ aᵢ₊₁)`
  -- has boundary `basis(const γ(aᵢ₊₁)) - basis(const γ(aᵢ))` (by
  -- `singChain_d_basis_apply_one`, since composing with face inclusions
  -- gives constant simplices and `succAbove 0 0 = 1`, `succAbove 1 0 = 0`).
  -- Summing over `i : Fin n` telescopes via `Finset.sum_range_sub` to
  -- `basis(const γ(1)) - basis(const γ(0))`. For a loop, `γ 0 = γ 1 = x`,
  -- so the result is zero.
  set K := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)
  -- The i-th subpath simplex.
  let sub : Fin n → SingSimplex 1 Y := fun i =>
    Path.toSingSimplex
      (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                 (divFinIcc n hn (i.val + 1) i.isLt))
  -- Vertex values of `sub i`.
  have hsub_zero : ∀ i : Fin n, (sub i) (stdSimplex.vertex 0)
      = γ (divFinIcc n hn i.val (le_of_lt i.isLt)) := by
    intro i; simp [sub]
  have hsub_one : ∀ i : Fin n, (sub i) (stdSimplex.vertex 1)
      = γ (divFinIcc n hn (i.val + 1) i.isLt) := by
    intro i; simp [sub]
  -- Push (K.d 1 0) through the sum and expand each summand via
  -- `singChain_d_basis_apply_one`.
  show (K.d 1 0).hom (∑ i, (singChain_basis (sub i)).hom 1) = 0
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i _ => singChain_d_basis_apply_one (sub i))]
  simp_rw [hsub_zero, hsub_one]
  -- Telescope. Lift to ℕ-indexed `g` defined for k ≤ n.
  classical
  let g : ℕ → (singChain 0 Y : Type) := fun k =>
    if h : k ≤ n then
      (singChain_basis (constSimplex0 (γ (divFinIcc n hn k h)))).hom 1
    else 0
  have hterm : ∀ i : Fin n,
      (singChain_basis
            (constSimplex0 (γ (divFinIcc n hn (i.val + 1) i.isLt)))).hom 1 -
        (singChain_basis
            (constSimplex0 (γ (divFinIcc n hn i.val (le_of_lt i.isLt))))).hom 1
      = g (i.val + 1) - g i.val := by
    intro i
    have h1 : i.val + 1 ≤ n := i.isLt
    have h0 : i.val ≤ n := le_of_lt i.isLt
    simp only [g, dif_pos h1, dif_pos h0]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k)]
  rw [Finset.sum_range_sub g n]
  -- `g 0 = basis(const γ(0)) . 1 = basis(const x) . 1 = g n` (loop hypothesis).
  have h0 : g 0 = (singChain_basis (constSimplex0 x)).hom 1 := by
    simp only [g, dif_pos (Nat.zero_le _)]
    rw [divFinIcc_zero, γ.source]
  have hn' : g n = (singChain_basis (constSimplex0 x)).hom 1 := by
    simp only [g, dif_pos (le_refl _)]
    rw [divFinIcc_self, γ.target]
  rw [h0, hn']
  exact sub_self _

/-- **Refined loop-to-cycle map.** Given a loop `γ : Path x x`, produce
the integral 1-cycle via the n=1 partition chain (single simplex) +
homology descent. Routes through `K.cyclesMk` (which uses the
partition chain's boundary-vanishing) + `K.homologyπ`.

The result lives in `K.homology 1 = IntegralOneCycle Y`. -/
noncomputable def loopToIntegralOneCycle' {Y : Type} [TopologicalSpace Y]
    {x : Y} (γ : _root_.Path x x) : IntegralOneCycle Y :=
  let K := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)
  -- The partition chain has boundary 0 by `Path.partitionChain_boundary_eq_zero`.
  -- Build the cycle representative via `K.cyclesMk` (concrete-category constructor).
  -- Then apply the homology projection `K.homologyπ`.
  -- IntegralOneCycle Y is definitionally K.homology 1.
  (K.homologyπ 1).hom
    ((K.cyclesMk (Path.partitionChain γ 1 Nat.one_pos) 0
        (ChainComplex.next_nat_succ 0)
        (Path.partitionChain_boundary_eq_zero γ 1 Nat.one_pos)))

end JacobianChallenge.Periods
