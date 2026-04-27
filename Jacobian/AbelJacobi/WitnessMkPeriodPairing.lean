import Jacobian.AbelJacobi.WitnessMk
import Jacobian.AnalyticJacobian.MkPeriodPairingCycle

/-!
# `witnessAbelJacobi` is invariant under `periodPairing` perturbations

Combines `witnessAbelJacobi_eq_mk_sub` with the
`mk_{add,sub}_periodPairing` family. Adding or subtracting any
`periodPairing E X σ` value inside the `mk`-encoded witness leaves
it unchanged — this is what makes the witness well-defined as a
function from a representative pair to an analytic Jacobian class.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Adding a `periodPairing` value inside the witness's `mk` argument
leaves the witness unchanged. -/
theorem witnessAbelJacobi_eq_mk_sub_add_periodPairing
    (basePoint P : X) (v : E) (σ : IntegralOneCycle X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v - evalLinearMap basePoint v +
        periodPairing E X σ) := by
  rw [witnessAbelJacobi_eq_mk_sub, mk_add_periodPairing]

/-- Subtracting a `periodPairing` value inside the witness's `mk`
argument leaves the witness unchanged. -/
theorem witnessAbelJacobi_eq_mk_sub_sub_periodPairing
    (basePoint P : X) (v : E) (σ : IntegralOneCycle X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v - evalLinearMap basePoint v -
        periodPairing E X σ) := by
  rw [witnessAbelJacobi_eq_mk_sub, mk_sub_periodPairing]

/-- Adding an `ℕ`-scaled `periodPairing` doesn't change the witness. -/
theorem witnessAbelJacobi_eq_mk_sub_add_nsmul_periodPairing
    (basePoint P : X) (v : E) (n : ℕ) (σ : IntegralOneCycle X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v - evalLinearMap basePoint v +
        n • periodPairing E X σ) := by
  rw [witnessAbelJacobi_eq_mk_sub, mk_add_nsmul_periodPairing]

/-- Adding an `ℤ`-scaled `periodPairing` doesn't change the witness. -/
theorem witnessAbelJacobi_eq_mk_sub_add_zsmul_periodPairing
    (basePoint P : X) (v : E) (n : ℤ) (σ : IntegralOneCycle X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      mk E X (evalLinearMap P v - evalLinearMap basePoint v +
        n • periodPairing E X σ) := by
  rw [witnessAbelJacobi_eq_mk_sub, mk_add_zsmul_periodPairing]

end JacobianChallenge.AbelJacobi
