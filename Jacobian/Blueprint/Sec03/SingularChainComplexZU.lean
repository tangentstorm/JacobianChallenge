import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Jacobian.Blueprint.Sec03.PeriodHomologyInvariance

/-!
# Universe-polymorphic singular chain complex

`Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` defines the singular
chain complex `singularChainComplexZ (X : Type)` at universe 0, with
coefficients `ModuleCat.of ℤ ℤ` in `ModuleCat.{0} ℤ`. Its homology is the
`Type 0` `IntegralOneCycle X`, and the period pairing
(`Jacobian/Periods/PeriodFunctional.lean`) is built from it as a `descHomology`
of the degree-1 short complex.

This file adds a **separate**, universe-polymorphic companion
`singularChainComplexZU (X : Type u)` in `ChainComplex (ModuleCat.{u} ℤ) ℕ`,
obtained by instantiating Mathlib's `singularChainComplexFunctor` at universe
`u` with coefficients `ULift.{u} ℤ` — the chain-complex analogue of
`IntegralOneCycleU` (`Jacobian/Periods/IntegralOneCycleU.lean`). The `ULift.{u} ℤ`
coefficient is forced: `singularChainComplexFunctor.{u}` demands its coefficient
category be a `Category.{u}`, so `ModuleCat.{u} ℤ` is the only option and
`ULift.{u} ℤ` is the `Type u` copy of the coefficient module `ℤ`.

This is step C1a of the authorized full `Type u` generalization of the period
lattice (Option C containment): the universe-`u` period pairing
(`periodPairingU`, step C1b) will be the `descHomology` of the degree-1 short
complex `(singularChainComplexZU X).sc 1`, mirroring the Type-0 `periodPairing`,
so `periodFullComplexLattice` — and hence the public `Jacobian (X : Type u)` —
will type-check, without disturbing the Type-0 chain-complex / homology
subsystem (the rank/de-Rham/Hurewicz proofs).

For `X : Type 0` this is *not* definitionally equal to `singularChainComplexZ X`
(the coefficient module differs: `ULift.{0} ℤ` vs `ℤ`), but it is canonically
isomorphic.
-/

namespace JacobianChallenge.Blueprint.Sec03

open CategoryTheory

universe u

/--
The singular chain complex `… → C₂ → C₁ → C₀ → 0` of a topological space
`X : Type u` with ℤ coefficients, as a `ChainComplex (ModuleCat.{u} ℤ) ℕ`.

Universe-polymorphic companion to `singularChainComplexZ` (which is pinned to
`Type 0`); see the module docstring for why the two cannot be merged.
-/
noncomputable def singularChainComplexZU (X : Type u) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)

/--
Singular 1-chains on `X : Type u` with ℤ coefficients, as an object of
`ModuleCat.{u} ℤ`. Universe-polymorphic companion to `SingularOneChain`.
-/
noncomputable abbrev SingularOneChainU (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  (singularChainComplexZU X).X 1

/--
Singular 2-chains on `X : Type u` with ℤ coefficients, as an object of
`ModuleCat.{u} ℤ`. Universe-polymorphic companion to `SingularTwoChain`.
-/
noncomputable abbrev SingularTwoChainU (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  (singularChainComplexZU X).X 2

end JacobianChallenge.Blueprint.Sec03
