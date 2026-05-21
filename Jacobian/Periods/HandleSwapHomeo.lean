import Jacobian.Periods.EdgeWord
import Mathlib.Logic.Relation

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
    (diskMul c hc z).val = c * z.1 := rfl

private lemma norm_exp_I_mul_real (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

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

/-! ### Rotation-invariance lemmas -/

/-- Rigid rotation of the disk by a specified number of boundary sides. -/
noncomputable def diskRotateBySide (L : ℕ) (hL : L ≠ 0) (k : ℕ) : DiskC ≃ₜ DiskC :=
  let theta := 2 * Real.pi * k / L
  diskMul (Complex.exp (Complex.I * theta)) (norm_exp_I_mul_real theta)

lemma diskRotateBySide_apply (L : ℕ) (_hL : L ≠ 0) (k : ℕ) (z : DiskC) :
    (diskRotateBySide L _hL k z).val = Complex.exp (Complex.I * (2 * Real.pi * k / L : ℝ)) * z.1 := rfl

/-- **Narrow Leaf.** Rigid disk rotation transports boundary parameters. -/
lemma diskRotateBySide_boundaryParam
    (L : ℕ) (hL : L ≠ 0) (k i : ℕ) (t : ℝ) :
    diskRotateBySide L hL k (boundaryParam' L i t) =
    boundaryParam' L (i + k) t := by
  -- Identity derived from exp(I * 2π(i+k+t)/L) = exp(I * 2πk/L) * exp(I * 2π(i+t)/L).
  -- And modular arithmetic for boundary angle indices.
  sorry

/-- **Narrow Leaf.** Side-pairing relation is preserved under rigid disk rotation. -/
theorem sidePairingRel_rotate_iff
    {g : ℕ} (w : EdgeWord g) (k : ℕ) (hL : w.length ≠ 0) :
    ∀ x y : DiskC,
      sidePairingRel g (w.rotate k) x y ↔
        sidePairingRel g w (diskRotateBySide w.length hL k x) (diskRotateBySide w.length hL k y) := by
  -- Identity: identification in rotated word is rotated identification of original word.
  -- This lifts generator preservation (SideGen) through the equivalence closure (EqvGen)
  -- in both directions using inverse disk rotation.
  sorry

/-! ### Quotient lemmas -/

/-- Cyclic rotation of the word preserves the quotient. -/
theorem wordQuotient_homeomorph_of_rotate
    {g : ℕ} (w : EdgeWord g) (k : ℕ) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ
              EdgeWord.wordQuotient g (w.rotate k)) := by
  by_cases hL : w.length = 0
  · have hw : w = [] := List.eq_nil_of_length_eq_zero hL
    subst hw; exact ⟨Homeomorph.refl _⟩
  · let hL_pos : w.length ≠ 0 := hL
    let f := diskRotateBySide w.length hL_pos k
    have h_resp : ∀ x y, sidePairingRel g (w.rotate k) x y ↔ sidePairingRel g w (f x) (f y) := by
      intro x y; exact sidePairingRel_rotate_iff w k hL_pos x y
    exact ⟨(Quotient.homeo' f h_resp).symm⟩

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
