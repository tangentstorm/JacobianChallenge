import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.Linarith

/-!
# Divisors on compact Riemann surfaces

This module starts the production substrate for the genus-zero
Riemann-Roch route.  A divisor is represented by a finitely supported
integer-valued function on points.  The analytic content that identifies
these divisors with zero/pole data of meromorphic functions is built in
the neighboring meromorphic modules.
-/

namespace JacobianChallenge.HolomorphicForms

noncomputable section

/-- A divisor on `X`: a finite formal integer combination of points. -/
abbrev Divisor (X : Type*) : Type _ :=
  X →₀ ℤ

namespace Divisor

/-- The degree of a divisor, i.e. the sum of its coefficients. -/
def degree {X : Type*} : Divisor X →+ ℤ :=
  Finsupp.degree

/-- The divisor consisting of the point `P` with coefficient `1`. -/
def point {X : Type*} (P : X) : Divisor X :=
  Finsupp.single P 1

@[simp] theorem degree_zero {X : Type*} :
    degree (0 : Divisor X) = 0 :=
  rfl

@[simp] theorem degree_point {X : Type*} (P : X) :
    degree (point P : Divisor X) = 1 := by
  exact Finsupp.degree_single P 1

/-- An effective divisor has nonnegative coefficient at every point. -/
def Effective {X : Type*} (D : Divisor X) : Prop :=
  ∀ Q : X, 0 ≤ D Q

@[simp] theorem effective_zero {X : Type*} :
    Effective (0 : Divisor X) := by
  intro Q
  simp

@[simp] theorem point_apply_self {X : Type*} [DecidableEq X] (P : X) :
    point P P = 1 := by
  simp [point]

@[simp] theorem point_apply_ne {X : Type*} [DecidableEq X] {P Q : X} (h : Q ≠ P) :
    point P Q = 0 := by
  simp [point, h]

theorem effective_point {X : Type*} [DecidableEq X] (P : X) :
    Effective (point P : Divisor X) := by
  intro Q
  by_cases h : Q = P
  · subst h
    simp [point]
  · simp [point, h]

end Divisor

theorem effective_le_point_iff_grounded {X : Type*} [DecidableEq X] (D : Divisor X) (P : X)
    (heff : Divisor.Effective D) (hle : D ≤ Divisor.point P) (hne : D ≠ 0) :
    D = Divisor.point P := by
  ext Q
  have h_zero_of_ne : ∀ Q, Q ≠ P → D Q = 0 := fun Q hQ =>
    le_antisymm (by simpa [Divisor.point_apply_ne hQ] using hle Q) (heff Q)
  by_cases h : Q = P
  · rw [h]
    have h_le := hle P
    have h_eff := heff P
    rw [Divisor.point_apply_self] at h_le
    have hDP : D P = 1 := by
      by_contra h_ne_one
      have hDP_zero : D P = 0 := by omega
      have hD_zero : D = 0 := by
        ext R
        by_cases hR : R = P
        · rw [hR]; exact hDP_zero
        · exact h_zero_of_ne R hR
      exact hne hD_zero
    rw [hDP, Divisor.point_apply_self]
  · rw [h_zero_of_ne Q h, Divisor.point_apply_ne h]

end

end JacobianChallenge.HolomorphicForms
