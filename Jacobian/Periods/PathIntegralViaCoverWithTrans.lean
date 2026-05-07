import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant
import Jacobian.Periods.PathIntegralCongr

/-!
# Path-additivity (`_trans`) for `pathIntegralViaCoverWith` (aligned partition)

**Phase 6 deliverable**, used to discharge Sorry 1
(`pathIntegralViaCover_trans_eq_add` in `PullbackNaturality.lean`).

States: for an aligned uniform chart partition of `γ.trans γ'` of size
`2 * n` whose first `n` segments cover `γ` (with `pickA`) and last `n`
segments cover `γ'` (with `pickB`), the cover-with sum splits:

  `pathIntegralViaCoverWith ω (γ.trans γ') (2*n) _ pickT hcovT =
   pathIntegralViaCoverWith ω γ n hn pickA hcovA +
   pathIntegralViaCoverWith ω γ' n hn pickB hcovB`.

## Strategy

`pathIntegralViaCoverWith ω (γ.trans γ') (2*n) _ pickT hcovT` unfolds
to a `Finset.sum` over `Fin (2*n)`. Reindex via `Fin n ⊕ Fin n ≃
Fin (n + n) ≃ Fin (2*n)` (`finSumFinEquiv` composed with `finCongr`).
The first-half summands correspond to subpaths of `γ.trans γ'` on
`[0, 1/2]`, which by `Path.extend_trans_of_le_half` are pointwise equal
to subpaths of `γ` on `[0, 1]`. The second-half summands correspond to
subpaths on `[1/2, 1]`, pointwise equal to subpaths of `γ'`.

Path equality across different endpoint types is bridged via the
`pathIntegralViaChartCorrect_eq_of_heq` congruence lemma, which only
needs HEq of the underlying paths plus the endpoint equalities.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The aligned-`pickT` for `γ.trans γ'` of size `2 * n`: the first
`n` indices use `pickA`, the last `n` use `pickB`. -/
noncomputable def alignedPickT
    (n : ℕ) (pickA pickB : Fin n → X) (j : Fin (2 * n)) : X :=
  if hlt : j.val < n then pickA ⟨j.val, hlt⟩
  else pickB ⟨j.val - n, by have h := j.isLt; omega⟩

/-- Heterogeneous path equality from pointwise function equality. -/
private lemma path_heq_of_pointwise
    {Y : Type*} [TopologicalSpace Y]
    {a b a' b' : Y} {γ : Path a b} {γ' : Path a' b'}
    (h_eq : ∀ s : unitInterval, γ s = γ' s) :
    HEq γ γ' := by
  have ha : a = a' := γ.source.symm.trans ((h_eq 0).trans γ'.source)
  have hb : b = b' := γ.target.symm.trans ((h_eq 1).trans γ'.target)
  subst ha
  subst hb
  exact heq_of_eq (Path.ext (funext h_eq))

/-- Combined congruence: `pathIntegralViaChartCorrect` is invariant under
heterogeneous path equality and chart-pick equality. -/
private lemma pathIntegralViaChartCorrect_eq_of_heq_charts
    (ω : HolomorphicOneForm E X)
    {a b a' b' : X} {γ : Path a b} {γ' : Path a' b'}
    {p p' : X} (hp : p = p')
    (ha : a = a') (hb : b = b')
    (hγ : HEq γ γ')
    (h : range γ ⊆ (chartAt E p).source)
    (h' : range γ' ⊆ (chartAt E p').source) :
    pathIntegralViaChartCorrect (chartAt E p) ω γ h =
      pathIntegralViaChartCorrect (chartAt E p') ω γ' h' := by
  subst hp
  exact pathIntegralViaChartCorrect_eq_of_heq _ _ ha hb hγ h h'

/-- A `Fin (2 * n)` sum splits into two `Fin n` sums via the standard
`Fin n ⊕ Fin n ≃ Fin (2 * n)` equivalence: first half indices are
`⟨i.val, _⟩`, second half are `⟨n + k.val, _⟩`. -/
private lemma sum_aligned_split
    {α : Type*} [AddCommMonoid α] (n : ℕ) (f : Fin (2 * n) → α) :
    ∑ j : Fin (2 * n), f j =
      (∑ i : Fin n, f ⟨i.val, by have := i.isLt; omega⟩) +
      (∑ k : Fin n, f ⟨n + k.val, by have := k.isLt; omega⟩) := by
  let e : Fin n ⊕ Fin n ≃ Fin (2 * n) := finSumFinEquiv.trans (finCongr (two_mul n).symm)
  rw [← e.sum_comp f, Fintype.sum_sum_type]
  rfl

/-- Pointwise: For j ≤ n, `(γ.trans γ') (divFinIcc (2n) j) = γ (divFinIcc n j)`. -/
private lemma trans_at_first_half_endpt
    {a b c : X} (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : j ≤ n)
    (h_2n_pos : (0 : ℕ) < 2 * n) (h_jle : j ≤ 2 * n) :
    (γ.trans γ') (divFinIcc (2 * n) h_2n_pos j h_jle) =
      γ (divFinIcc n hn j hj) := by
  have h_n_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_2n_R_pos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast h_2n_pos
  have h_2n_eq : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  have h_v_le_half : ((j : ℝ) / ((2 * n : ℕ) : ℝ)) ≤ 1/2 := by
    rw [div_le_iff₀ h_2n_R_pos, h_2n_eq]
    have h1 : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  have h_jn_in : ((j : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one h_n_R_pos]
    exact_mod_cast hj
  calc (γ.trans γ') (divFinIcc (2 * n) h_2n_pos j h_jle)
      = (γ.trans γ').extend (divFinIcc (2 * n) h_2n_pos j h_jle : ℝ) :=
        (Path.extend_apply _ (divFinIcc (2 * n) h_2n_pos j h_jle).2).symm
    _ = γ.extend (2 * ((j : ℝ) / ((2 * n : ℕ) : ℝ))) := by
        rw [show (divFinIcc (2 * n) h_2n_pos j h_jle : ℝ) = (j : ℝ) / ((2 * n : ℕ) : ℝ) from rfl]
        exact Path.extend_trans_of_le_half γ γ' h_v_le_half
    _ = γ.extend ((j : ℝ) / n) := by
        congr 1
        rw [h_2n_eq]
        field_simp
    _ = γ (divFinIcc n hn j hj) := by
        rw [show ((j : ℝ) / n) = (divFinIcc n hn j hj : ℝ) from rfl]
        exact Path.extend_apply _ (divFinIcc n hn j hj).2

/-- Pointwise: For k ≤ n, `(γ.trans γ') (divFinIcc (2n) (n+k)) = γ' (divFinIcc n k)`. -/
private lemma trans_at_second_half_endpt
    {a b c : X} (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (h_2n_pos : (0 : ℕ) < 2 * n) (h_nkle : n + k ≤ 2 * n) :
    (γ.trans γ') (divFinIcc (2 * n) h_2n_pos (n + k) h_nkle) =
      γ' (divFinIcc n hn k hk) := by
  have h_n_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_2n_R_pos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast h_2n_pos
  have h_2n_eq : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  have h_v_ge_half : (1 : ℝ) / 2 ≤ ((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ) := by
    rw [le_div_iff₀ h_2n_R_pos, h_2n_eq]
    push_cast
    linarith
  have h_kn_in : ((k : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one h_n_R_pos]
    exact_mod_cast hk
  calc (γ.trans γ') (divFinIcc (2 * n) h_2n_pos (n + k) h_nkle)
      = (γ.trans γ').extend (divFinIcc (2 * n) h_2n_pos (n + k) h_nkle : ℝ) :=
        (Path.extend_apply _ (divFinIcc (2 * n) h_2n_pos (n + k) h_nkle).2).symm
    _ = γ'.extend (2 * (((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) - 1) := by
        rw [show (divFinIcc (2 * n) h_2n_pos (n + k) h_nkle : ℝ) =
              ((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ) from rfl]
        exact Path.extend_trans_of_half_le γ γ' h_v_ge_half
    _ = γ'.extend ((k : ℝ) / n) := by
        congr 1
        rw [h_2n_eq]
        push_cast
        field_simp
        ring
    _ = γ' (divFinIcc n hn k hk) := by
        rw [show ((k : ℝ) / n) = (divFinIcc n hn k hk : ℝ) from rfl]
        exact Path.extend_apply _ (divFinIcc n hn k hk).2

/-- Pointwise equality: for `j < n`, the j-th aligned-2n subpath of `γ.trans γ'`
agrees pointwise with the j-th aligned-n subpath of `γ`. -/
private lemma trans_subpath_first_half_pointwise
    {a b c : X} (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : j + 1 ≤ n)
    (h_2n_pos : (0 : ℕ) < 2 * n)
    (s : unitInterval) :
    ((γ.trans γ').subpath
        (divFinIcc (2 * n) h_2n_pos j (by omega))
        (divFinIcc (2 * n) h_2n_pos (j + 1) (by omega))) s =
      (γ.subpath
        (divFinIcc n hn j (Nat.le_of_succ_le hj))
        (divFinIcc n hn (j + 1) hj)) s := by
  have h_n_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_2n_R_pos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast h_2n_pos
  have h_2n_eq : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  show (γ.trans γ') (Path.subpathAux _ _ s) = γ (Path.subpathAux _ _ s)
  have h_s_nn : (0 : ℝ) ≤ s := s.2.1
  have h_s_le : (s : ℝ) ≤ 1 := s.2.2
  have h_1ms_nn : (0 : ℝ) ≤ 1 - s := by linarith
  have h_j_le : (j : ℝ) ≤ n := by exact_mod_cast Nat.le_of_succ_le hj
  have h_j1_le : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hj
  have h_div_lo : (((j : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) ≤ 1/2 := by
    rw [div_le_iff₀ h_2n_R_pos, h_2n_eq]; linarith
  have h_div_hi : ((((j + 1) : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) ≤ 1/2 := by
    rw [div_le_iff₀ h_2n_R_pos, h_2n_eq]; push_cast at h_j1_le ⊢; linarith
  set u_path : unitInterval :=
    Path.subpathAux (divFinIcc (2 * n) h_2n_pos j (by omega))
                    (divFinIcc (2 * n) h_2n_pos (j + 1) (by omega)) s with hu_def
  have hu_le : (u_path : ℝ) ≤ 1/2 := by
    rw [hu_def]
    show ((1 - s) * (divFinIcc (2 * n) h_2n_pos j _ : ℝ) +
          s * (divFinIcc (2 * n) h_2n_pos (j + 1) _ : ℝ)) ≤ 1/2
    show ((1 - s) * ((j : ℝ) / ((2 * n : ℕ) : ℝ)) +
          s * (((j + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ))) ≤ 1/2
    calc (1 - s) * ((j : ℝ) / ((2 * n : ℕ) : ℝ)) +
          s * ((((j + 1) : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ))
        ≤ (1 - s) * (1/2) + s * (1/2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h_div_lo h_1ms_nn
          · exact mul_le_mul_of_nonneg_left h_div_hi h_s_nn
      _ = 1/2 := by ring
  have h_u_in : (u_path : ℝ) ∈ Set.Icc (0 : ℝ) 1 := u_path.2
  rw [show (γ.trans γ') u_path = (γ.trans γ').extend u_path from
        (Path.extend_apply _ h_u_in).symm]
  rw [Path.extend_trans_of_le_half γ γ' hu_le]
  have h_2u_in : (2 * (u_path : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    have h_u_nn : (0 : ℝ) ≤ u_path := u_path.2.1
    refine ⟨by linarith, by linarith⟩
  rw [Path.extend_apply γ h_2u_in]
  congr 1
  apply Subtype.ext
  show (2 : ℝ) * (u_path : ℝ) =
       (Path.subpathAux (divFinIcc n hn j _) (divFinIcc n hn (j + 1) _) s : ℝ)
  rw [hu_def]
  show (2 : ℝ) * ((1 - s) * ((j : ℝ) / ((2 * n : ℕ) : ℝ)) +
                  s * (((j + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ))) =
       ((1 - s) * ((j : ℝ) / n) + s * (((j + 1 : ℕ) : ℝ) / n))
  rw [h_2n_eq]
  push_cast
  field_simp

/-- Pointwise equality: for `k < n`, the (n+k)-th aligned-2n subpath of `γ.trans γ'`
agrees pointwise with the k-th aligned-n subpath of `γ'`. -/
private lemma trans_subpath_second_half_pointwise
    {a b c : X} (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 ≤ n)
    (h_2n_pos : (0 : ℕ) < 2 * n)
    (s : unitInterval) :
    ((γ.trans γ').subpath
        (divFinIcc (2 * n) h_2n_pos (n + k) (by omega))
        (divFinIcc (2 * n) h_2n_pos (n + k + 1) (by omega))) s =
      (γ'.subpath
        (divFinIcc n hn k (Nat.le_of_succ_le hk))
        (divFinIcc n hn (k + 1) hk)) s := by
  have h_n_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_2n_R_pos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast h_2n_pos
  have h_2n_eq : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  show (γ.trans γ') (Path.subpathAux _ _ s) = γ' (Path.subpathAux _ _ s)
  have h_s_nn : (0 : ℝ) ≤ s := s.2.1
  have h_s_le : (s : ℝ) ≤ 1 := s.2.2
  have h_1ms_nn : (0 : ℝ) ≤ 1 - s := by linarith
  have h_k_le : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_succ_le hk
  have h_k1_le : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
  have h_div_lo : (1 : ℝ) / 2 ≤ (((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) := by
    rw [le_div_iff₀ h_2n_R_pos, h_2n_eq]
    push_cast
    linarith
  have h_div_hi : (1 : ℝ) / 2 ≤ (((n + k + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) := by
    rw [le_div_iff₀ h_2n_R_pos, h_2n_eq]
    push_cast
    linarith
  set u_path : unitInterval :=
    Path.subpathAux (divFinIcc (2 * n) h_2n_pos (n + k) (by omega))
                    (divFinIcc (2 * n) h_2n_pos (n + k + 1) (by omega)) s with hu_def
  have hu_ge : (1 : ℝ) / 2 ≤ (u_path : ℝ) := by
    rw [hu_def]
    show (1 : ℝ) / 2 ≤ ((1 - s) * (divFinIcc (2 * n) h_2n_pos (n + k) _ : ℝ) +
                       s * (divFinIcc (2 * n) h_2n_pos (n + k + 1) _ : ℝ))
    show (1 : ℝ) / 2 ≤ ((1 - s) * (((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) +
                       s * (((n + k + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)))
    calc (1 : ℝ) / 2
        = (1 - s) * (1/2) + s * (1/2) := by ring
      _ ≤ (1 - s) * (((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) +
          s * (((n + k + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h_div_lo h_1ms_nn
          · exact mul_le_mul_of_nonneg_left h_div_hi h_s_nn
  have h_u_in : (u_path : ℝ) ∈ Set.Icc (0 : ℝ) 1 := u_path.2
  rw [show (γ.trans γ') u_path = (γ.trans γ').extend u_path from
        (Path.extend_apply _ h_u_in).symm]
  rw [Path.extend_trans_of_half_le γ γ' hu_ge]
  have h_u_le : (u_path : ℝ) ≤ 1 := u_path.2.2
  have h_2u_in : (2 * (u_path : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by linarith, by linarith⟩
  rw [Path.extend_apply γ' h_2u_in]
  congr 1
  apply Subtype.ext
  show (2 : ℝ) * (u_path : ℝ) - 1 =
       (Path.subpathAux (divFinIcc n hn k _) (divFinIcc n hn (k + 1) _) s : ℝ)
  rw [hu_def]
  show (2 : ℝ) * ((1 - s) * (((n + k : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) +
                  s * (((n + k + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ))) - 1 =
       ((1 - s) * ((k : ℝ) / n) + s * (((k + 1 : ℕ) : ℝ) / n))
  rw [h_2n_eq]
  push_cast
  field_simp
  ring

/-- **Phase 6 (single named gap): With-level path additivity on aligned partition.**

For partitions `(n, pickA, hcovA)` of `γ` and `(n, pickB, hcovB)` of `γ'`
that combine into an aligned partition `(2*n, alignedPickT n pickA pickB,
hcovT)` of `γ.trans γ'`, the cover-with sum splits.

Proof reduces to a Fin-reindexing of the `2*n` sum into two `n`-sums
plus the half-affine reparameterisation invariance — see file-level
docstring. -/
theorem pathIntegralViaCoverWith_aligned_trans
    (ω : HolomorphicOneForm E X) {a b c : X}
    (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n)
    (pickA pickB : Fin n → X)
    (hcovA : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickA i)).source)
    (hcovB : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ' t ∈ (chartAt E (pickB i)).source)
    (hcovT : ∀ (j : Fin (2 * n)) (t : unitInterval),
      (j : ℝ) / ((2 * n : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * n : ℕ) : ℝ) →
      (γ.trans γ') t ∈ (chartAt E (alignedPickT n pickA pickB j)).source) :
    pathIntegralViaCoverWith ω (γ.trans γ') (2 * n)
        (Nat.mul_pos (by omega) hn)
        (alignedPickT n pickA pickB) hcovT =
      pathIntegralViaCoverWith ω γ n hn pickA hcovA +
      pathIntegralViaCoverWith ω γ' n hn pickB hcovB := by
  have h_2n_pos : (0 : ℕ) < 2 * n := Nat.mul_pos (by omega) hn
  unfold pathIntegralViaCoverWith
  -- Split the LHS Fin (2*n) sum into two Fin n sums.
  rw [sum_aligned_split n]
  congr 1
  · -- First half: ∑ i : Fin n, F ⟨i.val, _⟩ = ∑ i : Fin n, G(i)
    apply Finset.sum_congr rfl
    rintro i -
    -- For the LHS index ⟨i.val, _⟩ in Fin (2 * n), .val = i.val < n.
    -- alignedPickT picks pickA i.
    have h_idx_lt : i.val < n := i.isLt
    have h_pick : alignedPickT n pickA pickB ⟨i.val, by omega⟩ = pickA i := by
      unfold alignedPickT
      rw [dif_pos h_idx_lt]
    have hi_succ : i.val + 1 ≤ n := i.isLt
    have hi_le : i.val ≤ n := Nat.le_of_succ_le hi_succ
    refine pathIntegralViaChartCorrect_eq_of_heq_charts ω h_pick ?_ ?_ ?_ _ _
    · exact trans_at_first_half_endpt γ γ' n hn i.val hi_le h_2n_pos (by omega)
    · exact trans_at_first_half_endpt γ γ' n hn (i.val + 1) hi_succ h_2n_pos (by omega)
    · apply path_heq_of_pointwise
      intro s
      exact trans_subpath_first_half_pointwise γ γ' n hn i.val hi_succ h_2n_pos s
  · -- Second half: ∑ k : Fin n, F ⟨n + k.val, _⟩ = ∑ k : Fin n, H(k)
    apply Finset.sum_congr rfl
    rintro k -
    have h_idx_ge : ¬ (n + k.val) < n := by omega
    have h_pick : alignedPickT n pickA pickB ⟨n + k.val, by have := k.isLt; omega⟩ = pickB k := by
      unfold alignedPickT
      rw [dif_neg h_idx_ge]
      apply congr_arg
      apply Fin.ext
      show n + k.val - n = k.val
      omega
    have hk_succ : k.val + 1 ≤ n := k.isLt
    have hk_le : k.val ≤ n := Nat.le_of_succ_le hk_succ
    refine pathIntegralViaChartCorrect_eq_of_heq_charts ω h_pick ?_ ?_ ?_ _ _
    · exact trans_at_second_half_endpt γ γ' n hn k.val hk_le h_2n_pos (by omega)
    · -- Goal: (γ.trans γ') (divFinIcc (2*n) h_2n_pos (⟨n+k.val,_⟩.val + 1) _) = γ' (divFinIcc n hn (k.val + 1) hk_succ)
      -- Note ⟨n+k.val,_⟩.val + 1 = n + k.val + 1 = n + (k.val + 1) (defeq via Nat.add_succ)
      exact trans_at_second_half_endpt γ γ' n hn (k.val + 1) hk_succ h_2n_pos (by omega)
    · -- HEq path equality
      apply path_heq_of_pointwise
      intro s
      exact trans_subpath_second_half_pointwise γ γ' n hn k.val hk_succ h_2n_pos s

/-! ### Existence of aligned partition for `γ.trans γ'`

Given paths `γ`, `γ'` we can extract uniform chart partitions for each
via `exists_uniform_chart_partition`, refine to a common multiple, and
combine into an aligned `(2*n, alignedPickT)` partition for
`γ.trans γ'`. This reduces Sorry 1
(`pathIntegralViaCover_trans_eq_add` in `PullbackNaturality.lean`) to
`pathIntegralViaCoverWith_aligned_trans` plus refinement invariance.

Discharged Phase 6b: the existence theorem is now sorry-free. -/

omit [NormedSpace ℂ E] [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] in
variable (X) in
/-- Existence of a common-multiple aligned chart partition for
`γ.trans γ'` given partition data for `γ` and `γ'` separately.

The bookkeeping aligns:
* a partition of `γ` of size `n_A`, refined to `n_A * n_B`,
* a partition of `γ'` of size `n_B`, refined to `n_A * n_B`,
* combined into a `(2 * n_A * n_B, alignedPickT _ pickA' pickB')`
  partition of `γ.trans γ'` whose first half covers γ and second
  half covers γ'.

The cover hypotheses for the refined and combined partitions follow
mechanically from the originals via `Path.trans_apply`'s formula. -/
theorem exists_aligned_partition_for_trans
    {a b c : X} (γ : Path a b) (γ' : Path b c) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (pickA pickB : Fin n → X)
      (_hcovA : ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt E (pickA i)).source)
      (_hcovB : ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ' t ∈ (chartAt E (pickB i)).source),
      ∀ (j : Fin (2 * n)) (t : unitInterval),
        (j : ℝ) / ((2 * n : ℕ) : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * n : ℕ) : ℝ) →
        (γ.trans γ') t ∈ (chartAt E (alignedPickT n pickA pickB j)).source := by
  -- Step 1: extract uniform chart partitions for γ and γ' separately.
  obtain ⟨nA, hnA, pickArAW, hcovArAW⟩ :=
    exists_uniform_chart_partition E γ.toContinuousMap
  obtain ⟨nB, hnB, pickBraw, hcovBraw⟩ :=
    exists_uniform_chart_partition E γ'.toContinuousMap
  -- Casting helpers for ℝ-side arithmetic.
  have hnA_pos : (0 : ℝ) < (nA : ℝ) := by exact_mod_cast hnA
  have hnB_pos : (0 : ℝ) < (nB : ℝ) := by exact_mod_cast hnB
  have hnAB_pos : (0 : ℝ) < (nA : ℝ) * (nB : ℝ) := mul_pos hnA_pos hnB_pos
  have hcast : ((nA * nB : ℕ) : ℝ) = (nA : ℝ) * (nB : ℝ) := by push_cast; ring
  have hidiv_A : ∀ i : Fin (nA * nB), i.val / nB < nA := fun i =>
    (Nat.div_lt_iff_lt_mul hnB).mpr i.isLt
  have hidiv_B : ∀ i : Fin (nA * nB), i.val / nA < nB := fun i =>
    (Nat.div_lt_iff_lt_mul hnA).mpr (Nat.mul_comm nA nB ▸ i.isLt)
  -- Refined cover hypothesis for γ at granularity nA * nB (mirrors
  -- `pathIntegralViaCover_partition_compat_under_smooth`).
  have hcovA : ∀ (i : Fin (nA * nB)) (t : unitInterval),
      (i : ℝ) / ((nA * nB : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) →
      γ t ∈ (chartAt E (pickArAW ⟨i.val / nB, hidiv_A i⟩)).source := by
    intro i t ht1 ht2
    refine hcovArAW ⟨i.val / nB, hidiv_A i⟩ t ?_ ?_
    · have hmul : ((i.val / nB : ℕ) : ℝ) * (nB : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nB
      have hstep : ((i.val / nB : ℕ) : ℝ) / (nA : ℝ) ≤ (i.val : ℝ) / ((nA * nB : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnA_pos hnAB_pos]
        nlinarith [hmul, hnA_pos, hnB_pos]
      exact hstep.trans ht1
    · have h_nat : i.val + 1 ≤ ((i.val / nB) + 1) * nB := by
        have h_lt : i.val / nB < (i.val / nB) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnB).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nB) + 1 : ℕ) : ℝ) * (nB : ℝ) := by
        push_cast; exact_mod_cast h_nat
      have hstep : ((i.val : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) ≤
          (((i.val / nB : ℕ) + 1 : ℕ) : ℝ) / (nA : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnAB_pos hnA_pos]
        nlinarith [h_real, hnA_pos, hnB_pos]
      have hcast_succ :
          (((i.val / nB : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nB : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep
  have hcovB : ∀ (i : Fin (nA * nB)) (t : unitInterval),
      (i : ℝ) / ((nA * nB : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) →
      γ' t ∈ (chartAt E (pickBraw ⟨i.val / nA, hidiv_B i⟩)).source := by
    intro i t ht1 ht2
    refine hcovBraw ⟨i.val / nA, hidiv_B i⟩ t ?_ ?_
    · have hmul : ((i.val / nA : ℕ) : ℝ) * (nA : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nA
      have hstep : ((i.val / nA : ℕ) : ℝ) / (nB : ℝ) ≤ (i.val : ℝ) / ((nA * nB : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnB_pos hnAB_pos]
        nlinarith [hmul, hnA_pos, hnB_pos]
      exact hstep.trans ht1
    · have h_nat : i.val + 1 ≤ ((i.val / nA) + 1) * nA := by
        have h_lt : i.val / nA < (i.val / nA) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnA).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nA) + 1 : ℕ) : ℝ) * (nA : ℝ) := by
        push_cast; exact_mod_cast h_nat
      have hstep : ((i.val : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) ≤
          (((i.val / nA : ℕ) + 1 : ℕ) : ℝ) / (nB : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnAB_pos hnB_pos]
        nlinarith [h_real, hnA_pos, hnB_pos]
      have hcast_succ :
          (((i.val / nA : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nA : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep
  -- Assemble the existential: choose `n := nA * nB`, the refined chart picks,
  -- the refined cover hypotheses, and discharge the aligned-partition condition.
  refine ⟨nA * nB, Nat.mul_pos hnA hnB,
    fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩,
    fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩,
    hcovA, hcovB, ?_⟩
  intro j t hj1 hj2
  -- Cast helpers for the `2 * n` granularity.
  have hn_pos : (0 : ℝ) < ((nA * nB : ℕ) : ℝ) := by rw [hcast]; exact hnAB_pos
  have h2cast : ((2 * (nA * nB) : ℕ) : ℝ) = 2 * ((nA * nB : ℕ) : ℝ) := by push_cast; ring
  have h2nAB_pos : (0 : ℝ) < 2 * ((nA * nB : ℕ) : ℝ) := by positivity
  by_cases hjn : j.val < nA * nB
  · -- Case: j.val < nA * nB. The aligned pick is `pickA ⟨j.val, hjn⟩`.
    -- From the cell bound `t ≤ (j+1)/(2n)` and `j+1 ≤ n`, conclude `t ≤ 1/2`,
    -- so `(γ.trans γ') t = γ ⟨2 * t, _⟩` by `Path.trans_apply`. Apply hcovA.
    have h_aligned_eq :
        alignedPickT (nA * nB)
          (fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩)
          (fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩) j =
        pickArAW ⟨j.val / nB, hidiv_A ⟨j.val, hjn⟩⟩ := by
      unfold alignedPickT; exact dif_pos hjn
    rw [h_aligned_eq]
    have hjn_real : ((j : ℝ) + 1) ≤ ((nA * nB : ℕ) : ℝ) := by
      have h : j.val + 1 ≤ nA * nB := hjn
      exact_mod_cast h
    have ht_half : (t : ℝ) ≤ 1 / 2 := by
      have hub : ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ 1 / 2 := by
        rw [h2cast, div_le_div_iff₀ h2nAB_pos (by norm_num : (0:ℝ) < 2)]
        linarith
      exact hj2.trans hub
    rw [Path.trans_apply, dif_pos ht_half]
    have h_2t_in : 2 * (t : ℝ) ∈ unitInterval := by
      refine ⟨?_, ?_⟩
      · have := t.2.1; linarith
      · linarith
    have h_jval_eq :
        ((⟨j.val, hjn⟩ : Fin (nA * nB)) : ℝ) = (j : ℝ) := rfl
    refine hcovA ⟨j.val, hjn⟩ ⟨2 * (t : ℝ), h_2t_in⟩ ?_ ?_
    · -- ((j.val : ℕ) : ℝ) / (nA * nB) ≤ 2 * (t : ℝ)
      rw [h_jval_eq]
      have h_jt : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ (t : ℝ) := hj1
      rw [h2cast] at h_jt
      rw [div_le_iff₀ hn_pos]
      rw [div_le_iff₀ h2nAB_pos] at h_jt
      linarith
    · -- 2 * (t : ℝ) ≤ ((j.val : ℕ) : ℝ + 1) / (nA * nB)
      rw [h_jval_eq]
      have h_jt : (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) := hj2
      rw [h2cast] at h_jt
      rw [le_div_iff₀ hn_pos]
      rw [le_div_iff₀ h2nAB_pos] at h_jt
      linarith
  · -- Case: j.val ≥ nA * nB. The aligned pick is `pickB ⟨j.val - n, _⟩`.
    push_neg at hjn
    have h_aligned_eq :
        alignedPickT (nA * nB)
          (fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩)
          (fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩) j =
        pickBraw ⟨(j.val - nA * nB) / nA,
          hidiv_B ⟨j.val - nA * nB, by have h := j.isLt; omega⟩⟩ := by
      unfold alignedPickT; exact dif_neg (not_lt.mpr hjn)
    rw [h_aligned_eq]
    -- `j.val ≥ n` implies `j/(2n) ≥ 1/2`, hence `t ≥ 1/2`.
    have hj_ge_half : (1 : ℝ) / 2 ≤ (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) := by
      rw [h2cast, le_div_iff₀ h2nAB_pos]
      have : ((nA * nB : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hjn
      linarith
    have ht_ge_half : (1 : ℝ) / 2 ≤ (t : ℝ) := hj_ge_half.trans hj1
    by_cases ht_gt_half : 1 / 2 < (t : ℝ)
    · -- Subcase: t > 1/2. Use `Path.trans_apply`'s `dif_neg` branch.
      rw [Path.trans_apply, dif_neg (not_le.mpr ht_gt_half)]
      have h_2t_sub_in : 2 * (t : ℝ) - 1 ∈ unitInterval := by
        refine ⟨?_, ?_⟩
        · linarith
        · have := t.2.2; linarith
      have h_nat_sub : ((j.val - nA * nB : ℕ) : ℝ) = (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) := by
        rw [Nat.cast_sub hjn]
      have h_idx_cast :
          ((⟨j.val - nA * nB, by have h := j.isLt; omega⟩ : Fin (nA * nB)) : ℝ) =
          (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) := by
        change ((j.val - nA * nB : ℕ) : ℝ) = (j.val : ℝ) - ((nA * nB : ℕ) : ℝ)
        exact h_nat_sub
      refine hcovB ⟨j.val - nA * nB, by have h := j.isLt; omega⟩
        ⟨2 * (t : ℝ) - 1, h_2t_sub_in⟩ ?_ ?_
      · rw [h_idx_cast]
        have h_jt : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ (t : ℝ) := hj1
        rw [h2cast] at h_jt
        rw [div_le_iff₀ hn_pos]
        rw [div_le_iff₀ h2nAB_pos] at h_jt
        change (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) ≤ (2 * (t : ℝ) - 1) * ((nA * nB : ℕ) : ℝ)
        have hjr : (j : ℝ) = (j.val : ℝ) := rfl
        rw [hjr] at h_jt
        nlinarith
      · rw [h_idx_cast]
        have h_jt : (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) := hj2
        rw [h2cast] at h_jt
        rw [le_div_iff₀ hn_pos]
        rw [le_div_iff₀ h2nAB_pos] at h_jt
        change (2 * (t : ℝ) - 1) * ((nA * nB : ℕ) : ℝ) ≤
            (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) + 1
        have hjr : (j : ℝ) = (j.val : ℝ) := rfl
        rw [hjr] at h_jt
        nlinarith
    · -- Subcase: t ≤ 1/2. Combined with `t ≥ 1/2`, we have `t = 1/2`, and the
      -- aligned-cell bound forces `j.val = nA * nB`. Then
      -- `(γ.trans γ') t = γ ⟨1, _⟩ = b = γ' 0`, so `γ' 0 ∈ chart` follows
      -- from `hcovBraw` at `i = 0`, `t' = 0`.
      push_neg at ht_gt_half
      have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm ht_gt_half ht_ge_half
      have hj_eq : j.val = nA * nB := by
        have hj1' : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ 1 / 2 := by
          rw [ht_eq] at hj1; exact hj1
        have hj_eq_real : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) = 1 / 2 :=
          le_antisymm hj1' hj_ge_half
        rw [h2cast, div_eq_iff (ne_of_gt h2nAB_pos)] at hj_eq_real
        have h_real : (j.val : ℝ) = ((nA * nB : ℕ) : ℝ) := by
          have hjr : (j : ℝ) = (j.val : ℝ) := rfl
          rw [hjr] at hj_eq_real
          linarith
        exact_mod_cast h_real
      -- Show the chart in the goal equals `chartAt E (pickBraw ⟨0, hnB⟩)`.
      have h_chart_eq :
          chartAt E (pickBraw ⟨(j.val - nA * nB) / nA,
              hidiv_B ⟨j.val - nA * nB, by have h := j.isLt; omega⟩⟩) =
          chartAt E (pickBraw ⟨0, hnB⟩) := by
        congr 2
        apply Fin.ext
        change (j.val - nA * nB) / nA = 0
        rw [hj_eq, Nat.sub_self, Nat.zero_div]
      rw [h_chart_eq]
      -- Now show `(γ.trans γ') t ∈ chartAt E (pickBraw ⟨0, hnB⟩).source`.
      -- Compute `(γ.trans γ') t = γ ⟨1, _⟩ = b = γ' 0` and apply `hcovBraw`.
      rw [Path.trans_apply, dif_pos ht_gt_half]
      have h2t : 2 * (t : ℝ) = 1 := by linarith
      have h_one_in : (1 : ℝ) ∈ unitInterval :=
        ⟨zero_le_one, le_refl 1⟩
      rw [show (⟨2 * (t : ℝ),
            (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht_gt_half⟩⟩ : unitInterval) =
              (1 : unitInterval) from Subtype.ext h2t]
      rw [γ.target]
      rw [show b = γ' (0 : unitInterval) from γ'.source.symm]
      refine hcovBraw ⟨0, hnB⟩ (0 : unitInterval) ?_ ?_
      · simp
      · simp

end JacobianChallenge.Periods
