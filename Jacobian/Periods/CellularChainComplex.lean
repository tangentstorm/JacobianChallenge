import Jacobian.Periods.FiniteCWStructure
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cellular chain complex (low-dimensional, frontier)

For a finite CW structure `cw : FiniteCWStructure X`, the cellular
chain complex in degree `n` is the free `ℤ`-module on the `n`-cells:

  `C_n(cw) = Fin (cw.cellCount n) →₀ ℤ`.

The cellular boundary `∂_n : C_n → C_{n-1}` is the degree map of the
attaching map, summed over the `(n-1)`-cells.  Mathlib v4.28.0 has no
general "degree of a map between spheres" — that is one of the missing
big inputs for the cellular ↔ singular comparison theorem
(Hatcher 2.35).

This file provides the **low-dimensional** structure (`n ≤ 2`):

* `CellularChainModule cw n` — the free `ℤ`-module on `n`-cells, with
  `Module.Free` and `Module.Finite` instances inferable from
  `Finsupp` infrastructure;
* `CellularH1Witness cw` — the witness type
  `CellularChainModule cw 1`, used as a stand-in for cellular `H₁`
  (in the orientable surface case `∂₁ = 0` and `∂₂ = 0`, hence
  `H₁ = C₁`; in general the witness type and the genuine cellular
  `H₁` differ by sub-sorried boundary data);
* `cellularBoundary_one` and `cellularBoundary_two` — placeholder
  zero linear maps.  Replacing these by genuine degree-of-attaching
  boundaries is left as a sub-sorry inside
  `Jacobian/Periods/CellularSingularComparison.lean`.

The file is intentionally low-dimensional: the umbrella sorry it serves
(`cellularH1_finite_singularIsoData` in `CellularHomologyRS.lean`) only
needs degree-`1` cellular homology of a 2-manifold, so the chain
complex past degree `2` is irrelevant.
-/

namespace JacobianChallenge.Periods

variable {X : Type} [TopologicalSpace X]

/-- The `n`-th cellular chain module: the free `ℤ`-module on the
`n`-cells of the CW structure, modelled by `Fin k →₀ ℤ` where
`k = cw.cellCount n`. The `Finsupp` model gives `Module.Free` and
`Module.Finite` for free. -/
abbrev CellularChainModule
    (cw : FiniteCWStructure X) (n : ℕ) : Type :=
  Fin (cw.cellCount n) →₀ ℤ

/-- The cellular chain module is a free `ℤ`-module — direct from the
`Finsupp` model. -/
instance CellularChainModule.module_free
    (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Free ℤ (CellularChainModule cw n) :=
  inferInstance

/-- The cellular chain module is a finitely generated `ℤ`-module —
direct from the `Finsupp` model on a finite indexing set. -/
noncomputable instance CellularChainModule.module_finite
    (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Finite ℤ (CellularChainModule cw n) :=
  Module.Finite.of_basis (Finsupp.basisSingleOne (R := ℤ) (ι := Fin (cw.cellCount n)))

/-- **Witness type for cellular `H₁`.**

The cellular chain module in degree `1`. For the polygonal model of an
orientable surface (and more generally for any CW structure with a
single `0`-cell and `∂₂ = 0`), this is exactly the cellular `H₁`
because both boundaries vanish. For other CW structures the genuine
cellular `H₁` is the quotient
`ker(∂₁) / im(∂₂)`, but the umbrella obligation
`cellularH1_finite_singularIsoData` only requires *some* finite free
witness with an iso to the singular `H₁`; using the cellular `C₁`
itself as the witness type isolates the iso obligation cleanly inside
`CellularSingularComparison.lean`.

Concretely: this is `Fin (cw.cellCount 1) →₀ ℤ`, hence finite free. -/
abbrev CellularH1Witness (cw : FiniteCWStructure X) : Type :=
  CellularChainModule cw 1

/-- Placeholder cellular boundary `∂₁ : C₁ → C₀`. Replaced by the
genuine degree-of-attaching boundary in a future round; for the
umbrella obligation we only need that *some* low-dimensional cellular
chain complex exists with finite free chain modules. -/
noncomputable def cellularBoundary_one (cw : FiniteCWStructure X) :
    CellularChainModule cw 1 →ₗ[ℤ] CellularChainModule cw 0 :=
  0

/-- Placeholder cellular boundary `∂₂ : C₂ → C₁`. As above. -/
noncomputable def cellularBoundary_two (cw : FiniteCWStructure X) :
    CellularChainModule cw 2 →ₗ[ℤ] CellularChainModule cw 1 :=
  0

/-- With the placeholder boundaries `∂₁ = 0`, `∂₂ = 0`, the cellular
`H₁` (`= ker ∂₁ / im ∂₂`) is canonically `C₁`. We expose this
identification as a definitional convenience: any genuine cellular
chain complex differential will refine the placeholder, and the
sub-sorry in `CellularSingularComparison.lean` records the residual
gap between the placeholder cellular `H₁` and the singular `H₁`. -/
@[simp] theorem cellularBoundary_one_apply
    (cw : FiniteCWStructure X) (c : CellularChainModule cw 1) :
    cellularBoundary_one cw c = 0 := rfl

@[simp] theorem cellularBoundary_two_apply
    (cw : FiniteCWStructure X) (c : CellularChainModule cw 2) :
    cellularBoundary_two cw c = 0 := rfl

end JacobianChallenge.Periods
