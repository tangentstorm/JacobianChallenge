/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Category.TopCat.Basic
import Jacobian.Periods.PrismConstruction
import Jacobian.Periods.PrismChainBridge
import Jacobian.Periods.PrismChainCombinatorialIdentity

/-!
# Chain-level prism homotopy

This file builds the chain-level prism operator `P_n : C_n(X) ⟶ C_{n+1}(Y)`
from a homotopy `H : f ≃ g` and assembles it into a
`HomologicalComplex.Homotopy` between the singular chain complex maps
`(sChain.map f)` and `(sChain.map g)`. This is the *categorical* layer
of the prism construction (Hatcher §2.1, Lemma 2.10); the geometric
pieces — `prismSimplex`, `prismSimplex_top_face`,
`prismSimplex_bottom_face`, `prismSimplex_diagonal_face` — live in
`Jacobian/Periods/PrismConstruction.lean`. The Mathlib categorical
plumbing (universe / ULift / `Sigma.desc`) is in
`Jacobian/Periods/PrismChainBridge.lean`.

## Structure
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

/-!
### The chain-level prism operator

Given a homotopy `H : f ≃ g` between continuous maps `f, g : X → Y`,
the prism operator `P_n : C_n(X) ⟶ C_{n+1}(Y)` is defined on a basis
element corresponding to a singular `n`-simplex
`s : C(stdSimplex ℝ (Fin (n+1)), X)` by

`P_n s := Σ_{i : Fin (n+1)} (-1)^i.val • [prismSimplex n i H s]`

where `[·]` is the basis morphism in the chain group (cf.
`singChain_basis` in the bridge file).
-/

/--
The chain-level contribution at a single staircase index `i`:
the basis morphism of the prism simplex with sign `(-1)^(i.val + 1)`.

**Sign convention.** The geometric `prismSimplex` in
`PrismConstruction.lean` has top face = `g ∘ s` and bottom face = `f ∘ s`,
so the unsigned prism boundary computes `∂P + P∂ = g_* − f_*`. Mathlib's
`Homotopy.comm` is `f.f i = dNext i hom + prevD i hom + g.f i`, which
requires `dNext + prevD = f_* − g_*`. To convert, we use sign
`(-1)^(i + 1)` instead of `(-1)^i` (i.e., negate the entire operator).
-/
noncomputable def prismChain_summand
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (i : Fin (n + 1)) (s : SingSimplex n X) :
    ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) Y :=
  ((-1 : ℤ) ^ (i.val + 1)) • singChain_basis (prismSimplex n i H s)

/--
The chain-level prism operator at degree `n`, on a single
generator: the alternating sum over staircase indices
`i : Fin (n + 1)` of basis morphisms of `prismSimplex n i H s`.
-/
noncomputable def prismChain_op_atSimplex
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (s : SingSimplex n X) :
    ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) Y :=
  ∑ i : Fin (n + 1), prismChain_summand H n i s

/--
The chain-level prism operator at degree `n`:
`P_n : C_n(X) ⟶ C_{n+1}(Y)`.
-/
noncomputable def prismChain_op
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    singChain n X ⟶ singChain (n + 1) Y :=
  singChain_desc (prismChain_op_atSimplex H n)

/-- Universal property: the prism operator on a basis element. -/
@[simp]
theorem prismChain_op_basis
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (s : SingSimplex n X) :
    singChain_basis s ≫ prismChain_op H n =
      ∑ i : Fin (n + 1), prismChain_summand H n i s := by
  unfold prismChain_op
  rw [singChain_desc_basis]
  rfl

/-!
### The `Homotopy.hom` field, with case split on `j = i + 1`

`HomologicalComplex.Homotopy` requires `hom : ∀ i j, C.X i ⟶ D.X j` for
all pairs `(i, j)`, with `hom i j = 0` for `(i, j)` outside the
"chain shape" relation. For `ChainComplex C ℕ` (shape `down ℕ`), the
relation is `j + 1 = i`, so `hom i j` is non-zero only when `j = i + 1`,
where it equals our prism operator at degree `i`.
-/

/--
The `Homotopy.hom` field: the chain prism operator at degree `i`
when `j = i + 1`, and zero otherwise.
-/
noncomputable def prismChain_hom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i j : ℕ) :
    singChain i X ⟶ singChain j Y := by
  by_cases h : j = i + 1
  · exact h ▸ prismChain_op H i
  · exact 0

/--
The `Homotopy.zero` field: when `j ≠ i + 1` (i.e., the chain-shape
relation `c.Rel j i` fails), the `prismChain_hom` is zero by
construction. For `ComplexShape.down ℕ`, `Rel j i` holds iff `i + 1 = j`.
-/
theorem prismChain_hom_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (i j : ℕ) (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    prismChain_hom H i j = 0 := by
  unfold prismChain_hom
  rw [dif_neg]
  intro hji
  apply hij
  -- (ComplexShape.down ℕ).Rel j i ↔ i + 1 = j (since down is shift by 1)
  simp only [ComplexShape.down_Rel]
  omega

/--
Unfolding lemma: `prismChain_hom H i (i+1)` equals the prism operator
at degree `i` (no cast needed since the True branch reduces).
-/
@[simp]
theorem prismChain_hom_succ
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    prismChain_hom H i (i + 1) = prismChain_op H i := by
  unfold prismChain_hom
  rw [dif_pos rfl]

/-!
### The boundary identity

The chain-homotopy condition: for each `i : ℕ`,
`(sChain.map f).f i = dNext i (prismChain_hom H) + prevD i (prismChain_hom H) + (sChain.map g).f i`.

This is the categorical packaging of the prism boundary equation
`∂P + P∂ = g_* − f_*`. The combinatorial verification depends on:
* `prismSimplex_top_face`     — face 0 of `P_0` = `g ∘ s`
* `prismSimplex_bottom_face`  — face `n+1` of `P_n` = `f ∘ s`
* `prismSimplex_diagonal_face`— pairwise cancellation between adjacent
                                 staircase simplices
* `prismSimplex_side_face`    — *side-face identity*, **still missing**
                                 in `PrismConstruction.lean`.
-/

/-!
### Boundary identity at degree 0 (no side-faces needed)

At degree 0 the boundary identity simplifies because:
* `dNext 0 hom = 0` (no `c.next 0` in `down ℕ`),
* `prevD 0 hom = prismChain_op H 0 ≫ d_Y 1 0`,
* The single staircase index `i = 0 : Fin 1` has only top/bottom faces,
  no interior side-faces.

So we can prove the comm condition at i = 0 using only the existing
`prismSimplex_top_face` and `prismSimplex_bottom_face`.
-/

/-- Boundary identity at degree 0: a self-contained warmup case. -/
theorem prismChain_hom_comm_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0 =
      dNext 0 (prismChain_hom H) + prevD 0 (prismChain_hom H) +
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)).f 0 := by
  -- Apply per-basis extensionality to reduce to s : SingSimplex 0 X.
  apply singChain_hom_ext
  intro s
  -- LHS becomes singChain_basis (f.comp s) by singChain_map_basis.
  rw [singChain_map_basis]
  -- RHS: distribute composition over sum, simplify dNext 0 = 0,
  -- evaluate prevD 0 using prismChain_hom_succ, and use singChain_d_basis
  -- for the differential.
  rw [Preadditive.comp_add, Preadditive.comp_add]
  -- dNext 0 hom = 0 because c.next 0 doesn't relate (down ℕ has no Rel 0 j).
  have hdN : dNext 0 (prismChain_hom H) = 0 := by
    rw [dNext_nat]
    show (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d 0 (0 - 1) ≫
        prismChain_hom H (0 - 1) 0 = 0
    rw [show (0 : ℕ) - 1 = 0 from rfl]
    rw [HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.down_Rel])]
    simp
  rw [hdN]
  simp only [Limits.comp_zero, zero_add]
  -- prevD 0 hom = hom 0 (c.prev 0) ≫ d_Y (c.prev 0) 0
  --             = hom 0 1 ≫ d_Y 1 0 = prismChain_op H 0 ≫ d_Y 1 0.
  rw [show prevD 0 (prismChain_hom H)
        = prismChain_hom H 0 1 ≫
          (((singularChainComplexFunctor (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)).d 1 0 by
    exact prevD_eq _ (j := 0) (j' := 1) (by simp [ComplexShape.down_Rel])]
  rw [prismChain_hom_succ]
  rw [singChain_map_basis]
  -- Goal now: basis(f ∘ s) = singChain_basis s ≫ (prismChain_op H 0 ≫ d 1 0) + basis(g ∘ s)
  -- Reassociate then simplify singChain_basis s ≫ prismChain_op H 0
  rw [← Category.assoc]
  rw [show singChain_basis s ≫ prismChain_op H 0
        = ∑ i : Fin 1, prismChain_summand H 0 i s from
      prismChain_op_basis H 0 s]
  -- Sum over Fin 1: only one term, i = ⟨0, _⟩.
  rw [Fin.sum_univ_one]
  -- Goal: basis(f∘s) = (prismChain_summand H 0 ⟨0,_⟩ s ≫ d 1 0) + basis(g∘s)
  -- prismChain_summand H 0 ⟨0,_⟩ s = (-1)^1 • basis(prismSimplex 0 ⟨0,_⟩ H s) = -basis(...)
  unfold prismChain_summand
  -- (-1)^(0+1) = -1; reduce the smul-of-comp.
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul,
    Preadditive.neg_comp]
  -- Apply singChain_d_basis
  rw [singChain_d_basis]
  -- Sum over Fin 2: j = 0 (top face) and j = 1 (bottom face)
  rw [Fin.sum_univ_two]
  -- j = 0 face: prismSimplex_top_face says prismSimplex 0 ⟨0,_⟩ H s ∘ δ_0 = g ∘ s
  -- j = 1 face: prismSimplex_bottom_face says prismSimplex 0 ⟨0,_⟩ H s ∘ δ_1 = f ∘ s
  --   (since for n = 0, ⟨n, _⟩ = ⟨0, _⟩ and the bottom face index is n + 1 = 1).
  -- htop : prismSimplex 0 0 H s ∘ stdSimplexFaceInclusion 0 0 = g.comp s
  -- This follows from prismSimplex_top_face (i = 0, face index 0 = δ₀).
  have htop : (prismSimplex 0 (0 : Fin 1) H s).comp
        (stdSimplexFaceInclusion 0 0) = g.comp s := by
    ext p
    exact prismSimplex_top_face 0 H s p
  -- hbot : prismSimplex 0 0 H s ∘ stdSimplexFaceInclusion 0 1 = f.comp s
  -- This follows from prismSimplex_bottom_face (i = n = 0, face index n + 1 = 1).
  have hbot : (prismSimplex 0 (0 : Fin 1) H s).comp
        (stdSimplexFaceInclusion 0 1) = f.comp s := by
    ext p
    -- bottom face uses Fin.succAbove (Fin.last (n+1)). For n = 0, Fin.last 1 = 1.
    exact prismSimplex_bottom_face 0 H s p
  rw [htop, hbot]
  -- Goal: basis (f ∘ s) = -((-1)^0 • basis(g∘s) + (-1)^1 • basis(f∘s)) + basis(g∘s)
  --                     = -(basis(g∘s) - basis(f∘s)) + basis(g∘s)
  --                     = -basis(g∘s) + basis(f∘s) + basis(g∘s) = basis(f∘s).
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, neg_add_rev, neg_neg]
  abel

/-!
### The core combinatorial identity for the boundary at degree ≥ 1

The boundary equation at degree `i' + 1` reduces (after applying
`singChain_d_basis` and `prismChain_op_basis`) to the following purely
combinatorial identity over a 2D index sum:

prevD_sum = -basis(g.comp s) + basis(f.comp s) - dNext_sum

where:
* `dNext_sum = ∑_{j, l} (-1)^(j+l+1) • basis(prismSimplex i' l H (s.comp face_j))`
  is the dNext expansion.
* `prevD_sum = ∑_{l, j} (-1)^(l+1+j) • basis(prismSimplex (i'+1) l H s ∘ face_j)`
  is the prevD expansion.

The proof of this identity decomposes the prevD double-sum into 5 parts
via face identities:
* `(0, 0)` (top): contributes `-basis(g.comp s)`.
* `(i'+1, i'+2)` (bottom): contributes `+basis(f.comp s)`.
* Diagonal pairs `(l, l+1) | (l+1, l+1)`: cancel via
  `prismSimplex_diagonal_face`.
* Lower side `j < l`: re-indexes (via `prismSimplex_side_face_lower`)
  to a partial of `-dNext_sum`.
* Upper side `j > l+1`: re-indexes (via `prismSimplex_side_face_upper`)
  to the rest of `-dNext_sum`.

The combined lower + upper re-indexed sums equal `-dNext_sum` exactly.

* `prismChain_topContribution` — proved.
* `prismChain_bottomContribution` — proved.
* `prismChain_diagonalCancellation` — proved.
* `prismChain_lowerSideReindex` — proved via `Finset.sum_nbij'`.
* `prismChain_upperSideReindex` — proved via `Finset.sum_nbij'`.
* `prismChain_LHS_eq_partition` — proved via 6-region partition.
-/
theorem prismChain_succ_combinatorial_identity
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    (∑ l : Fin (i' + 2), prismChain_summand H (i' + 1) l s
      ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of Y)).d (i' + 2) (i' + 1)) =
      -singChain_basis (g.comp s) + singChain_basis (f.comp s)
        - (∑ j : Fin (i' + 2), ((-1 : ℤ) ^ j.val) •
          (singChain_basis (s.comp (stdSimplexFaceInclusion i' j))
          ≫ prismChain_op H i')) := by
  -- Step 1: Fully expand the LHS as a 2D sum.
  have h_lhs_expand :
      (∑ l : Fin (i' + 2), prismChain_summand H (i' + 1) l s
        ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
            (TopCat.of Y)).d (i' + 2) (i' + 1)) =
      ∑ l : Fin (i' + 2), ∑ j : Fin (i' + 3),
        ((-1 : ℤ) ^ (l.val + 1 + j.val)) • singChain_basis
          ((prismSimplex (i' + 1) l H s).comp (stdSimplexFaceInclusion (i' + 1) j)) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold prismChain_summand
    rw [Preadditive.zsmul_comp,
        singChain_d_basis (i' + 1) (prismSimplex (i' + 1) l H s),
        Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, ← pow_add]
  -- Step 2: Fully expand the dNext part of RHS as a 2D sum.
  have h_dNext_expand :
      (∑ j : Fin (i' + 2), ((-1 : ℤ) ^ j.val) •
        (singChain_basis (s.comp (stdSimplexFaceInclusion i' j))
          ≫ prismChain_op H i')) =
      ∑ j : Fin (i' + 2), ∑ l : Fin (i' + 1),
        ((-1 : ℤ) ^ (j.val + l.val + 1)) • singChain_basis
          (prismSimplex i' l H (s.comp (stdSimplexFaceInclusion i' j))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [prismChain_op_basis H i' (s.comp (stdSimplexFaceInclusion i' j))]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold prismChain_summand
    rw [smul_smul, ← pow_add, show j.val + (l.val + 1) = j.val + l.val + 1 from by omega]
  -- Step 3: Rewrite the goal using the expanded forms.
  rw [h_lhs_expand, h_dNext_expand]
  -- Step 4: Convert nested 2D sums to single sums over Cartesian products,
  -- so that we can apply `prismChain_LHS_eq_partition` (in
  -- `Jacobian/Periods/PrismChainCombinatorialIdentity.lean`).
  rw [show (∑ l : Fin (i' + 2), ∑ j : Fin (i' + 3),
        ((-1 : ℤ) ^ (l.val + 1 + j.val)) • singChain_basis
          ((prismSimplex (i' + 1) l H s).comp (stdSimplexFaceInclusion (i' + 1) j))) =
      ∑ lj : prismIndex i', prismChain_LHS_summand H i' s lj from by
    rw [← Finset.sum_product']
    rfl]
  rw [show (∑ j : Fin (i' + 2), ∑ l : Fin (i' + 1),
        ((-1 : ℤ) ^ (j.val + l.val + 1)) • singChain_basis
          (prismSimplex i' l H (s.comp (stdSimplexFaceInclusion i' j)))) =
      ∑ jl : Fin (i' + 2) × Fin (i' + 1),
        prismChain_dNext_summand H i' s jl.1 jl.2 from by
    rw [← Finset.sum_product']
    rfl]
  -- Step 5: Apply the partition identity.
  exact prismChain_LHS_eq_partition H i' s

/--
This is the chain-level expression of the prism boundary equation
`∂P + P∂ = f_* − g_*` (matching Mathlib's homotopy convention).

For `i = 0` it is fully proven (`prismChain_hom_comm_zero`) using only
top/bottom face identities.

Together with the existing
* `prismSimplex_top_face`     (j = 0, i = 0)
* `prismSimplex_bottom_face`  (j = n + 1, i = n)
* `prismSimplex_diagonal_face` (j = i + 1, paired with j = i + 1 of P_{i+1})

these cover ALL face combinations.

To discharge for `i = i' + 1`:

1. Reduce to a per-basis-element equation by `singChain_hom_ext`.
2. Unfold `dNext i (prismChain_hom H)` via `dNext_nat` —
   gives `d_X i (i-1) ≫ prismChain_op H (i-1)`.
3. Unfold `prevD i (prismChain_hom H)` via `prevD_eq` —
   gives `prismChain_op H i ≫ d_Y (i+1) i`.
4. Apply `singChain_d_basis` to expand differentials to alternating
   sums of face precompositions.
5. Apply `prismChain_op_basis` to expand prism operator to sum over
   staircase indices.
6. Apply each face identity case-by-case:
   * Outer-pair: top/bottom give `g_* σ` and `f_* σ` (with signs).
   * Diagonal pairs: `_diagonal_face` produces telescoping cancellation.
   * Lower side-faces: `_side_face_lower` matches `P_{n-1}(σ ∘ δ_j)`.
   * Upper side-faces: `_side_face_upper` matches `P_{n-1}(σ ∘ δ_{j-1})`.
7. The two side-face contributions reassemble into `P ∂ σ`, while the
   outer pair and diagonal cancellations leave `f_* σ - g_* σ`.
-/
theorem prismChain_hom_comm
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f i =
      dNext i (prismChain_hom H) + prevD i (prismChain_hom H) +
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)).f i := by
  cases i with
  | zero => exact prismChain_hom_comm_zero H
  | succ i' =>
    apply singChain_hom_ext
    intro s
    rw [singChain_map_basis]
    rw [Preadditive.comp_add, Preadditive.comp_add]
    rw [singChain_map_basis]
    -- Goal: basis (f.comp s) = (basis s ≫ dNext) + (basis s ≫ prevD) + basis (g.comp s)
    -- where dNext, prevD are at degree (i' + 1).
    -- Step 1: Unfold dNext (i' + 1) (prismChain_hom H).
    rw [show dNext (i' + 1) (prismChain_hom H)
          = (((singularChainComplexFunctor (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (i' + 1) i'
            ≫ prismChain_op H i' from by
        rw [dNext_nat]
        show (((singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (i' + 1) (i' + 1 - 1) ≫
            prismChain_hom H (i' + 1 - 1) (i' + 1) = _
        rw [show (i' + 1 - 1 : ℕ) = i' from rfl, prismChain_hom_succ]]
    -- Step 2: Unfold prevD (i' + 1) (prismChain_hom H).
    rw [show prevD (i' + 1) (prismChain_hom H)
          = prismChain_op H (i' + 1)
            ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)).d (i' + 2) (i' + 1) from by
        rw [prevD_eq _ (j := i' + 1) (j' := i' + 2)
            (by simp [ComplexShape.down_Rel])]
        rw [prismChain_hom_succ]]
    -- Step 3: Reassociate compositions.
    rw [← Category.assoc, ← Category.assoc]
    -- Step 4: Apply singChain_d_basis to expand differentials, prismChain_op_basis
    -- to expand the prism operators. After this, the goal has double sums on each side.
    rw [singChain_d_basis i' s]
    rw [show ((∑ j : Fin (i' + 2), ((-1 : ℤ) ^ j.val) •
            singChain_basis (s.comp (stdSimplexFaceInclusion i' j)))
          ≫ prismChain_op H i') =
          ∑ j : Fin (i' + 2), ((-1 : ℤ) ^ j.val) •
            (singChain_basis (s.comp (stdSimplexFaceInclusion i' j))
            ≫ prismChain_op H i') from by
        rw [Preadditive.sum_comp]
        simp]
    rw [prismChain_op_basis H (i' + 1) s]
    rw [show ((∑ l : Fin (i' + 2), prismChain_summand H (i' + 1) l s)
          ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
              (TopCat.of Y)).d (i' + 2) (i' + 1)) =
          ∑ l : Fin (i' + 2), prismChain_summand H (i' + 1) l s
            ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
              (TopCat.of Y)).d (i' + 2) (i' + 1) from by
        rw [Preadditive.sum_comp]]
    -- At this point the goal is a sum equation. The key combinatorial identity
    -- is captured by `prismChain_succ_combinatorial_identity` below: the
    -- prevD double-sum equals -basis(g.comp s) + basis(f.comp s) minus the
    -- dNext double-sum (i.e., the side-face contributions cancel exactly).
    rw [prismChain_succ_combinatorial_identity H i' s]
    abel

/-! ### Assembly into a `Homotopy` -/

/--
The chain-level prism homotopy, assembled from the prism operator,
the zero condition, and the boundary identity.
-/
noncomputable def prismChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    Homotopy
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) where
  hom := prismChain_hom H
  zero := prismChain_hom_zero H
  comm := prismChain_hom_comm H

/--
**Chain-level prism homotopy, existence form.** Given a homotopy
`H : f ≃ g` between continuous maps `f, g : X → Y`, the singular chain
complex functor (with ℤ-coefficients) sends `f` and `g` to chain maps
that are homotopic via the prism construction.
-/
theorem prism_chainHomotopy_exists
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    Nonempty (Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g))) :=
  ⟨prismChainHomotopy H⟩

end JacobianChallenge.Periods

end
