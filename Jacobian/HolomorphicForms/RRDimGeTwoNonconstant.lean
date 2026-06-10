import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Data.Complex.Basic

namespace JacobianChallenge.HolomorphicForms

theorem exists_outside_oneDim_of_finrank_ge_two
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : Submodule ℂ V) (hC : Module.finrank ℂ C = 1)
    (hV : 2 ≤ Module.finrank ℂ V) :
    ∃ v : V, v ∉ C := by
  by_contra! h
  have hC_top : C = ⊤ := Submodule.eq_top_iff'.mpr h
  have h_finrank : Module.finrank ℂ C = Module.finrank ℂ V := by
    rw [hC_top]
    exact finrank_top ℂ V
  rw [hC] at h_finrank
  linarith

end JacobianChallenge.HolomorphicForms
