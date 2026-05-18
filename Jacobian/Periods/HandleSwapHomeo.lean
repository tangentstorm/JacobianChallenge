import Jacobian.Periods.EdgeWord

namespace JacobianChallenge.Periods

open EdgeWord Complex

instance hs_wq_ts (g : ℕ) (w : EdgeWord g) :
    TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance hs_wq_cs (g : ℕ) (w : EdgeWord g) :
    CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))

/-! ### Disk rotation infrastructure -/

lemma diskC_norm_le_one (z : DiskC) : ‖z.1‖ ≤ 1 := by
  have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- Rotation of DiskC by complex multiplication. -/
noncomputable def diskMul (c : ℂ) (hc : ‖c‖ = 1) : DiskC ≃ₜ DiskC where
  toFun z := ⟨c * z, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hc, one_mul]
    exact diskC_norm_le_one z⟩
  invFun z := ⟨c⁻¹ * z, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv, hc, inv_one, one_mul]
    exact diskC_norm_le_one z⟩
  left_inv z := by
    ext; simp only [← mul_assoc]
    have hne : c ≠ 0 := by intro h; simp [h] at hc
    rw [inv_mul_cancel₀ hne, one_mul]
  right_inv z := by
    ext; simp only [← mul_assoc]
    have hne : c ≠ 0 := by intro h; simp [h] at hc
    rw [mul_inv_cancel₀ hne, one_mul]
  continuous_toFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

/-! ### Quotient lemmas -/

/-- Cyclic rotation of the word preserves the quotient. -/
theorem wordQuotient_homeomorph_of_rotate
    {g : ℕ} (w : EdgeWord g) (k : ℕ) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ
              EdgeWord.wordQuotient g (w.rotate k)) := by
  -- Blocked: the honest proof must construct the quotient map induced by a
  -- rotation of `DiskC`, prove the boundary parametrisation identity sending
  -- side `i` for `w` to the corresponding side of `w.rotate k`, and then
  -- descend that map through `Quotient.map'`.  The needed arithmetic bridge
  -- is a modular `boundaryParam'` rotation lemma, not currently available.
  sorry

/-- Rotating the tail of a handle-prefixed word preserves the quotient. -/
theorem handlePrefix_tailRotate_homeomorph
    {g : ℕ} (i : Fin g) (u : List (Letter g)) (m : ℕ) :
    Nonempty (EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) ≃ₜ
              EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate m)) := by
  -- Blocked beyond whole-word rotation: this needs a piecewise disk
  -- homeomorphism fixing the four handle sides while rotating only the tail
  -- boundary arcs, plus a proof that it respects the generated side-pairing
  -- relation.  A global disk rotation does not preserve the fixed prefix.
  sorry

/-! ### Assembly -/

private lemma rotate_app {α : Type*} (a b : List α) :
    (a ++ b).rotate a.length = b ++ a := by
  simp [List.rotate_eq_drop_append_take]

/-- Handle swap = rotate + tail-rotate + rotate. -/
theorem wordQuotient_homeomorph_of_handleSwap_step_v2
    {g : ℕ} {w v : EdgeWord g} (hsw : HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  obtain ⟨i, xs, ys, _, rfl⟩ := hsw
  let hd := [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]
  obtain ⟨f1⟩ := wordQuotient_homeomorph_of_rotate (xs ++ hd ++ ys) xs.length
  have h1 : (xs ++ hd ++ ys).rotate xs.length = hd ++ (ys ++ xs) := by
    rw [List.append_assoc, rotate_app, List.append_assoc]
  rw [h1] at f1
  obtain ⟨f2⟩ := handlePrefix_tailRotate_homeomorph i (ys ++ xs) ys.length
  have h2 : (ys ++ xs).rotate ys.length = xs ++ ys := rotate_app ys xs
  rw [h2] at f2
  obtain ⟨f3⟩ := wordQuotient_homeomorph_of_rotate (hd ++ xs ++ ys) (hd.length + xs.length)
  have h3 : (hd ++ xs ++ ys).rotate (hd.length + xs.length) = ys ++ hd ++ xs := by
    rw [show hd.length + xs.length = (hd ++ xs).length from by simp]
    show ((hd ++ xs) ++ ys).rotate (hd ++ xs).length = ys ++ hd ++ xs
    rw [rotate_app, List.append_assoc]
  rw [h3] at f3
  exact ⟨f1.trans (f2.trans f3)⟩

end JacobianChallenge.Periods
