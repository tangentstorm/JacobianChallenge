import Jacobian.Periods.LoopToIntegralCycle
import Jacobian.Periods.IntegralOneCycle
import Jacobian.HolomorphicForms.DeRhamComparisonMap
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Smooth chain cycles → integer homology bridge

Increment F.1. Defines the ℤ-linear morphism
`smoothCycleToHomology X : smoothOneChainCycleSubmodule X →ₗ[ℤ] IntegralOneCycle X`
sending a smooth 1-chain cycle to its homology class.

Parallel to `loopToIntegralOneCycle'` (`Periods/LoopToIntegralCycle.lean:201`),
which sends a single loop to its homology class; here we generalize to
ℤ-linear combinations of smooth 1-simplices that already satisfy the
boundary-vanishing condition.

Consumed by **F.2** (D.4 decomposition via Hom-pullback iso) and **F.3**
(D.5 decomposition via factorization through integer homology).
-/

namespace JacobianChallenge.Periods

open CategoryTheory
open JacobianChallenge.Blueprint.Sec03 (singularChainComplexZ)
open JacobianChallenge.HolomorphicForms (smoothOneChainCycleSubmodule)

/-- Helper: `(K.iCycles 1).hom` applied to `K.cyclesMk x 0 _ hx` returns `x`.
The `.hom`-flavored variant of Mathlib's `i_cyclesMk` (stated via
`(forget₂ C Ab).map`); they coincide for `C = ModuleCat ℤ`. -/
private theorem iCycles_cyclesMk_apply
    (X : Type) [TopologicalSpace X]
    (x : singChain 1 X)
    (hx : ((singularChainComplexZ X).d 1 0).hom x = 0) :
    ((singularChainComplexZ X).iCycles 1).hom
      ((singularChainComplexZ X).cyclesMk x 0 (ChainComplex.next_nat_succ 0) hx) = x :=
  (singularChainComplexZ X).i_cyclesMk x 0 (ChainComplex.next_nat_succ 0) hx

/-- The underlying additive group homomorphism sending a smooth 1-chain
cycle to its homology class. Linearity over ℤ is then automatic from
the unique ℤ-module structure on each AddCommGroup. -/
private noncomputable def smoothCycleToHomologyAddHom
    (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    smoothOneChainCycleSubmodule X →+
      IntegralOneCycle X where
  toFun := fun smcc =>
    let K := singularChainComplexZ X
    (K.homologyπ 1).hom
      (K.cyclesMk (smcc : singChain 1 X) 0 (ChainComplex.next_nat_succ 0)
        (LinearMap.mem_ker.mp smcc.property.2))
  map_zero' := by
    set K := singularChainComplexZ X with hK_def
    have hiC_inj : Function.Injective ((K.iCycles 1).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have h_cycMk_zero :
        K.cyclesMk ((0 : smoothOneChainCycleSubmodule X) : singChain 1 X) 0
            (ChainComplex.next_nat_succ 0)
            (LinearMap.mem_ker.mp (0 : smoothOneChainCycleSubmodule X).property.2)
          = 0 := by
      apply hiC_inj
      rw [map_zero]
      exact iCycles_cyclesMk_apply X _ _
    show (K.homologyπ 1).hom (K.cyclesMk _ _ _ _) = 0
    rw [h_cycMk_zero, map_zero]
  map_add' := by
    intro smcc₁ smcc₂
    set K := singularChainComplexZ X with hK_def
    have hiC_inj : Function.Injective ((K.iCycles 1).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have h_cycMk_add :
        K.cyclesMk ((smcc₁ + smcc₂ : smoothOneChainCycleSubmodule X) : singChain 1 X) 0
            (ChainComplex.next_nat_succ 0)
            (LinearMap.mem_ker.mp (smcc₁ + smcc₂).property.2)
          = K.cyclesMk (smcc₁ : singChain 1 X) 0 (ChainComplex.next_nat_succ 0)
              (LinearMap.mem_ker.mp smcc₁.property.2)
            + K.cyclesMk (smcc₂ : singChain 1 X) 0 (ChainComplex.next_nat_succ 0)
              (LinearMap.mem_ker.mp smcc₂.property.2) := by
      apply hiC_inj
      have h_lhs := iCycles_cyclesMk_apply X
        ((smcc₁ + smcc₂ : smoothOneChainCycleSubmodule X) : singChain 1 X)
        (LinearMap.mem_ker.mp (smcc₁ + smcc₂).property.2)
      have h_rhs1 := iCycles_cyclesMk_apply X
        (smcc₁ : singChain 1 X) (LinearMap.mem_ker.mp smcc₁.property.2)
      have h_rhs2 := iCycles_cyclesMk_apply X
        (smcc₂ : singChain 1 X) (LinearMap.mem_ker.mp smcc₂.property.2)
      rw [map_add, h_lhs, h_rhs1, h_rhs2]
      rfl
    show (K.homologyπ 1).hom (K.cyclesMk _ _ _ _)
        = (K.homologyπ 1).hom (K.cyclesMk _ _ _ _)
          + (K.homologyπ 1).hom (K.cyclesMk _ _ _ _)
    rw [h_cycMk_add, map_add]

/-- **F.1 — smooth chain cycle → integer homology class.** ℤ-linear
morphism sending a smooth 1-chain cycle to its homology class in
`IntegralOneCycle X = K.homology 1`.

Constructed by upgrading `smoothCycleToHomologyAddHom` via
`AddMonoidHom.toIntLinearMap`. Both source and target are abelian groups,
so every additive homomorphism is automatically ℤ-linear (uniqueness of
`Module ℤ` structure on `AddCommGroup`, `AddCommMonoid.subsingletonIntModule`). -/
noncomputable def smoothCycleToHomology
    (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    smoothOneChainCycleSubmodule X →ₗ[ℤ]
      IntegralOneCycle X := by
  -- Force consistent ℤ-module instances via Subsingleton on Module ℤ.
  haveI h1 : (smoothOneChainCycleSubmodule X).module
            = AddCommGroup.toIntModule _ :=
    Subsingleton.elim _ _
  haveI h2 : (IntegralOneCycle X).isModule
            = AddCommGroup.toIntModule _ :=
    Subsingleton.elim _ _
  -- After this `letI`-style alignment, toIntLinearMap should typecheck.
  exact h2 ▸ h1 ▸ (smoothCycleToHomologyAddHom X).toIntLinearMap

end JacobianChallenge.Periods
