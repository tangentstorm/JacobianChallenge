import Jacobian.Periods.EdgeWord

namespace JacobianChallenge.Periods

open EdgeWord Complex

instance hs_wq_topologicalSpace (g : ℕ) (w : EdgeWord g) :
    TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance hs_wq_compactSpace (g : ℕ) (w : EdgeWord g) :
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

lemma diskMul_apply (c : ℂ) (hc : ‖c‖ = 1) (z : DiskC) :
    (diskMul c hc z).1 = c * z.1 := rfl

/-- Map a homeomorphism between two types to a homeomorphism between their quotients,
given that the homeomorphism respects the relations. -/
private def Quotient.homeo' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) {s₁ : Setoid α} {s₂ : Setoid β}
    (hf : ∀ x y, s₁.r x y ↔ s₂.r (f x) (f y)) :
    Quotient s₁ ≃ₜ Quotient s₂ where
  toFun := Quotient.map' f (fun x y h => (hf x y).mp h)
  invFun := Quotient.map' f.symm (fun x y h => by
    have h_symm := hf (f.symm x) (f.symm y)
    simp only [Homeomorph.apply_symm_apply] at h_symm
    rwa [h_symm])
  left_inv q := by induction q using Quotient.inductionOn'; simp
  right_inv q := by induction q using Quotient.inductionOn'; simp
  continuous_toFun := Continuous.quotient_map' f.continuous (fun x y h => (hf x y).mp h)
  continuous_invFun := Continuous.quotient_map' f.symm.continuous (fun x y h => by
    have h_symm := hf (f.symm x) (f.symm y); simp only [Homeomorph.apply_symm_apply] at h_symm; rwa [h_symm])

private lemma SideGen_rotate {g : ℕ} (w : EdgeWord g) (k : ℕ) (x y : DiskC) :
    SideGen g w x y → SideGen g (w.rotate k)
      (diskMul (exp (I * (-2 * Real.pi * k / w.length))) (by
        rw [mul_comm, norm_exp_ofReal_mul_I]) x)
      (diskMul (exp (I * (-2 * Real.pi * k / w.length))) (by
        rw [mul_comm, norm_exp_ofReal_mul_I]) y) := by
  intro h
  cases h with
  | pair i j t ht hinv =>
    let L := w.length
    have hL_pos : L ≠ 0 := by intro h0; have := i.is_lt; rw [h0] at this; exact Nat.not_lt_zero _ this
    let i' : Fin (w.rotate k).length := ⟨(i.val + L - k % L) % L, by simp; apply Nat.mod_lt; linarith [hL_pos.bot_lt]⟩
    let j' : Fin (w.rotate k).length := ⟨(j.val + L - k % L) % L, by simp; apply Nat.mod_lt; linarith [hL_pos.bot_lt]⟩
    apply SideGen.pair i' j' t ht
    · -- (w.rotate k).get i' = w.get i
      simp [List.get_rotate, i']
      congr; rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_sub_cancel' (Nat.mod_le _ _), Nat.add_comm, Nat.mod_add_div]
    · -- diskMul c (boundaryParam' L i t) = boundaryParam' L i' t
      ext; unfold boundaryParam' boundaryParamC' boundaryAngle' diskMul diskMul_apply
      simp only [Subtype.coe_mk]
      rw [mul_comm, ← exp_add, ← mul_add]
      congr 1; push_cast; field_simp [hL_pos]
      have : ∃ n : ℤ, (i.val : ℤ) - k = (i'.val : ℤ) + n * L := by
        use - (k / L : ℤ) + (if i.val % L < k % L then -1 else 0)
        push_cast; rw [Int.ofNat_mod]
        split_ifs with h_lt
        · have : (i.val : ℤ) - (k % L : ℤ) + L = (i'.val : ℤ) := by
            rw [show (i'.val : ℤ) = (i.val + L - k % L) % L from rfl]
            rw [Int.ofNat_mod, Int.ofNat_sub, Int.ofNat_add, Int.ofNat_mod]
            · rw [Int.add_mod_self, Int.sub_mod]
            · exact Nat.le_of_lt (Nat.mod_lt k hL_pos.bot_lt)
          linarith [Nat.mod_add_div k L]
        · have : (i.val : ℤ) - (k % L : ℤ) = (i'.val : ℤ) := by
            rw [show (i'.val : ℤ) = (i.val + L - k % L) % L from rfl]
            rw [Nat.add_sub_assoc (Nat.le_of_not_lt h_lt), Nat.add_mod_self]
            exact Nat.mod_eq_of_lt (by linarith [i.is_lt])
          linarith [Nat.mod_add_div k L]
      obtain ⟨n, hn⟩ := this
      rw [show (i.val : ℝ) + t - k = (i'.val : ℝ) + t + n * L from by push_cast; linarith]
      field_simp [hL_pos]; ring_nf; rw [mul_assoc, mul_comm _ (2 * Real.pi)]
      rw [show ↑n * (2 * Real.pi) * I = I * (2 * Real.pi * n) from by ring]
      rw [exp_periodic]
    · -- Similar for j
      ext; unfold boundaryParam' boundaryParamC' boundaryAngle' diskMul diskMul_apply
      simp only [Subtype.coe_mk]
      rw [mul_comm, ← exp_add, ← mul_add]
      congr 1; push_cast; field_simp [hL_pos]
      have : ∃ n : ℤ, (j.val : ℤ) - k = (j'.val : ℤ) + n * L := by
        use - (k / L : ℤ) + (if j.val % L < k % L then -1 else 0)
        push_cast; rw [Int.ofNat_mod]
        split_ifs with h_lt <;>
        (rw [show (j'.val : ℤ) = (j.val + L - k % L) % L from rfl];
         try rw [Int.ofNat_mod, Int.ofNat_sub, Int.ofNat_add, Int.ofNat_mod];
         try rw [Int.add_mod_self, Int.sub_mod];
         try exact Nat.le_of_lt (Nat.mod_lt k hL_pos.bot_lt);
         try rw [Nat.add_sub_assoc (Nat.le_of_not_lt h_lt), Nat.add_mod_self];
         try exact Nat.mod_eq_of_lt (by linarith [j.is_lt]);
         linarith [Nat.mod_add_div k L])
      obtain ⟨n, hn⟩ := this
      rw [show (j.val : ℝ) + (1 - t) - k = (j'.val : ℝ) + (1 - t) + n * L from by push_cast; linarith]
      field_simp [hL_pos]; ring_nf; rw [mul_assoc, mul_comm _ (2 * Real.pi)]
      rw [show ↑n * (2 * Real.pi) * I = I * (2 * Real.pi * n) from by ring]
      rw [exp_periodic]

/-! ### Quotient lemmas -/

/-- Cyclic rotation of the word preserves the quotient. -/
theorem wordQuotient_homeomorph_of_rotate
    {g : ℕ} (w : EdgeWord g) (k : ℕ) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ
              EdgeWord.wordQuotient g (w.rotate k)) := by
  by_cases hL : w.length = 0
  · have hw : w = [] := List.eq_nil_of_length_eq_zero hL
    subst hw; exact ⟨Homeomorph.refl _⟩
  · let L := w.length
    let c := exp (I * (-2 * Real.pi * k / L))
    have hc : ‖c‖ = 1 := by rw [mul_comm, norm_exp_ofReal_mul_I]
    let f := diskMul c hc
    have h_resp : ∀ x y, sidePairingRel g w x y ↔ sidePairingRel g (w.rotate k) (f x) (f y) := by
      intro x y
      constructor
      · intro h; induction h with
        | rel x y h => exact Relation.EqvGen.rel _ _ (SideGen_rotate w k x y h)
        | refl x => exact Relation.EqvGen.refl _
        | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      · intro h
        let c' := exp (I * (2 * Real.pi * k / L))
        have hc' : ‖c'‖ = 1 := by rw [mul_comm, norm_exp_ofReal_mul_I]
        let f' := diskMul c' hc'
        have h_inv : ∀ z, f' (f z) = z := by
          intro z; ext; simp [diskMul_apply]; rw [← mul_assoc, ← exp_add, ← mul_add]
          have hL_pos : (L:ℝ) ≠ 0 := by push_cast; intro h0; rw [h0] at hL; exact hL rfl
          field_simp [hL_pos]; ring_nf; simp
        have h_back : ∀ x' y', sidePairingRel g (w.rotate k) x' y' → sidePairingRel g w (f' x') (f' y') := by
          intro x' y' hr
          induction hr with
          | rel x'' y'' hrr =>
            -- Rotate back: (w.rotate k).rotate (L - k % L) = w
            have h_rot := SideGen_rotate (w.rotate k) (L - k % L) x'' y'' hrr
            rw [List.rotate_rotate, Nat.add_sub_cancel' (Nat.mod_le _ _)] at h_rot
            rw [List.rotate_eq_self_iff.mpr (by rfl)] at h_rot
            have : (w.rotate k).length = L := by simp
            rw [this] at h_rot
            -- exp(I * -2π(L - k%L)/L) = exp(I * 2πk/L)
            have : exp (I * (-2 * Real.pi * (L - k % L) / L)) = exp (I * (2 * Real.pi * k / L)) := by
              have hL_pos : (L:ℝ) ≠ 0 := by push_cast; intro h0; rw [h0] at hL; exact hL rfl
              rw [← exp_periodic (I * (2 * Real.pi * k / L)) (-1)]
              congr 1; push_cast; field_simp [hL_pos]; ring_nf
            rw [this] at h_rot
            exact Relation.EqvGen.rel _ _ h_rot
          | refl x'' => exact Relation.EqvGen.refl _
          | symm x'' y'' _ ih => exact Relation.EqvGen.symm _ _ ih
          | trans x'' y'' z'' _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
        specialize h_back (f x) (f y) h
        rwa [h_inv, h_inv] at h_back
    exact ⟨Quotient.homeo' f h_resp⟩

/-- Rotating the tail of a handle-prefixed word preserves the quotient. -/
theorem handlePrefix_tailRotate_homeomorph
    {g : ℕ} (i : Fin g) (u : List (Letter g)) (m : ℕ) :
    Nonempty (EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) ≃ₜ
              EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate m)) := by
  -- Geometric strategy:
  -- 1. In the quotient of a word starting with [a, b, a⁻¹, b⁻¹], all five
  --    vertices of the handle block are identified to a single point v.
  -- 2. The tail arc u starts and ends at this same vertex v, forming a loop.
  -- 3. The quotient space is the wedge sum of a punctured torus (the handle)
  --    and the loop (the tail) glued at v.
  -- 4. A cyclic rotation of the tail letters u corresponds to a continuous
  --    reparametrisation of this tail loop which fixes the glue point v.
  -- 5. Such a reparametrisation induces a homeomorphism of the whole quotient.
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
    rw [← List.length_append, rotate_app, List.append_assoc]
  rw [h3] at f3
  exact ⟨f1.trans (f2.trans f3)⟩

end JacobianChallenge.Periods
