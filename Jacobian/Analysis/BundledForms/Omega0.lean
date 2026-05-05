import Jacobian.Analysis.BundledForms.SmoothFun
import Jacobian.StageB.DifferentialForms

/-!
# Phase 1.3 — `Omega0 M` : the real `ℝ`-vector space of `0`-forms

This file is the bridge between the project's existing placeholder
`Jacobian.StageB.DifferentialForms.Omega M 0 := PUnit` and the
real `ℝ`-vector space of smooth real-valued functions on `M` defined
in `SmoothFun.lean`.

**A `LinearEquiv` between them does not exist** — `Omega M 0` is
trivial (`PUnit`) while `SmoothFun M` is not.  This is intentional:
the downstream R10 stack (L², Δ, spectral kernel) is built against
`Omega0 = SmoothFun`, not against `Omega M 0`, so the placeholder
remains in place for the existing R5/R7/R8 typed scaffolding while
the real analytic content threads through `Omega0`.

For the project's `Module.Finite (Omega M 0)` consumers there is a
trivial back-compat `LinearMap` that factors through `PUnit`; this
is the "additive layer" mentioned in the dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 1).

When higher-`k` real `Ωᵏ` content lands (post-headline Phase 5),
`Omega0` will become `Omega 0` and this file will collapse to a
`def`-equation; until then the two types live alongside each other.
-/

namespace JacobianChallenge.Analysis.BundledForms

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open JacobianChallenge.StageB

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Phase 1.3.**  `Omega0 M` is the real `ℝ`-vector space of
smooth `0`-forms on `M`, i.e.\ smooth real-valued functions.  This
is the substantive replacement for the placeholder `Omega M 0`. -/
abbrev Omega0 : Type := SmoothFun (E := E) M

/-- The placeholder `Omega M 0 = PUnit` admits the unique zero map
into `Omega0 M`.  Documented as a back-compat bridge; downstream
R10 code should consume `Omega0` directly, not `Omega M 0`. -/
noncomputable def omegaZeroToOmega0 :
    Omega (E := E) M 0 →ₗ[ℝ] Omega0 (E := E) M :=
  0

/-- The collapse map `Omega0 M → Omega M 0` is the unique `ℝ`-linear
map into `PUnit` (i.e. the zero map).  Provided for completeness;
useful when downstream typed scaffolds need a witness map back to
the placeholder. -/
noncomputable def omega0ToOmegaZero :
    Omega0 (E := E) M →ₗ[ℝ] Omega (E := E) M 0 :=
  0

/-- The composition `Omega0 → Omega 0 → Omega0` is the zero map
(both factors pass through the trivial `PUnit`). -/
@[simp]
theorem omegaZeroToOmega0_omega0ToOmegaZero :
    (omegaZeroToOmega0 (E := E) M).comp (omega0ToOmegaZero (E := E) M) = 0 := by
  ext f
  simp [omegaZeroToOmega0, omega0ToOmegaZero]

/-- The composition `Omega 0 → Omega0 → Omega 0` is the zero map
(both maps land in `PUnit`). -/
@[simp]
theorem omega0ToOmegaZero_omegaZeroToOmega0 :
    (omega0ToOmegaZero (E := E) M).comp (omegaZeroToOmega0 (E := E) M) = 0 := by
  ext α
  simp [omegaZeroToOmega0, omega0ToOmegaZero]

end JacobianChallenge.Analysis.BundledForms
