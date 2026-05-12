import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.TensorSheaf
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.CupProduct
import Jacobian.HolomorphicForms.Serre.EvalSheafMap
import Jacobian.HolomorphicForms.Serre.H1Functoriality
import Jacobian.HolomorphicForms.Serre.TraceMap
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Serre pairing on the canonical dual (refined assembly)

The `ℂ`-bilinear Serre pairing

  H⁰(X, F) × H¹(X, Hom(F, K_X)) → ℂ

is assembled (round 4 refinement) as the composition

```
serreCupProductH0H1   :  H⁰(F) × H¹(Hom(F, K_X)) → H¹(F ⊗ Hom(F, K_X))
serreH1Map serreEval  :  H¹(F ⊗ Hom(F, K_X))     → H¹(K_X)
serreTraceMap         :  H¹(K_X)                 → ℂ
```

`serrePairing` itself is now a sorry-free assembly above the four
named obligations:

* `serreCupProductH0H1` (round 10),
* `serreEvalSheafMap` (round 9),
* `serreH1Map` (functoriality bridge),
* `serreTraceMap` (round 5).

The frontier `Module ℂ` instance on `H¹(X, F ⊗ Hom(F, K_X))` is
exposed as a project-level frontier `def`; rounds 21–22 will discharge
specific instances for line bundles via the Hodge identification.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier instance (sorry).** `ℂ`-module structure on the cup-
product target `H¹(X, F ⊗ Hom(F, K_X))`. Required to assemble the
Serre pairing as a chain of `ℂ`-linear maps. -/
instance serrePairing_module_H1Tensor
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    Module ℂ (RSSheafCohomology X (RSTensorAbSheaf X F (serreDualSheaf X F)) 1) :=
  sorry

/-- **Frontier instance (sorry).** `ℂ`-module structure on
`H¹(X, K_X)` required to land the Serre pairing in `ℂ` via the trace
map. -/
instance serrePairing_module_H1Canonical
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})] :
    Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1) :=
    sorry

    /-- **Refined (round 4).**
 The Serre pairing
`H⁰(X, F) × H¹(X, Hom(F, K_X)) → ℂ`, assembled as
`traceMap ∘ H¹(eval) ∘ cupProduct`. -/
noncomputable def serrePairing
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    RSSheafCohomology X F 0 →ₗ[ℂ]
      RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ :=
  letI := serreDualSheaf_module_H0 X F
  letI := serreDualSheaf_module_H1 X F
  letI := serrePairing_module_H1Tensor X F
  letI := serrePairing_module_H1Canonical X
  let cup := serreCupProductH0H1 X F (serreDualSheaf X F)
  let h1eval := serreH1Map X (serreEvalSheafMap X F)
  let trace := serreTraceMap X
  -- Postcompose `cup` (a bilinear map H⁰ → H¹ → H¹(F⊗Fᵛ)) with
  -- `trace ∘ h1eval` (a linear map H¹(F⊗Fᵛ) → ℂ).
  LinearMap.compr₂ cup (trace.comp h1eval)

end JacobianChallenge.HolomorphicForms
