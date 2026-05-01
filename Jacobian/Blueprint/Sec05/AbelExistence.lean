/-! Blueprint stubs: `thm:abel-existence` (sec05) sub-leaves classified
**TRIVIAL** and **SHORT** in `ref/plans/abel-existence.md`.

Abel's theorem: for a compact connected Riemann surface `X` of genus
`g ≥ 1` with a fixed base point, a degree-zero divisor `D` is principal
iff its image under the Abel–Jacobi map `AJ : Div⁰(X) → Jac(X)` is zero.

The Grok plan (`ref/plans/abel-existence.md`) decomposes the statement
into five sub-leaves:

1. `Div0` — degree-zero divisors (TRIVIAL)
2. `AJ` — the Abel–Jacobi map (SHORT)
3. `AJ_principal_zero` — `AJ ∘ divisor = 0` on meromorphic functions (MEDIUM)
4. `existence_of_f` — backwards direction via theta/Riemann existence (HARD)
5. `principal_iff_AJ_zero` — assembly of (3) + (4) (MEDIUM)

This file stubs **only the TRIVIAL/SHORT leaves** (`Div0` and `AJ`).
The MEDIUM/HARD leaves remain unstubbed pending dedicated worker
allocations; the table in `ref/scope-out.md` (sec05 row
`thm:abel-existence`) classifies the umbrella theorem as `DECOMPOSE`.

## Conventions

* No Mathlib imports — pure Lean placeholders so the dep-graph node
  is pickup-able without dragging in unrelated infrastructure.
* `Div0` is a `Unit` alias; the eventual real definition is
  `{D : Divisor X // D.degree = 0}` (cf. `Jacobian/Blueprint/Sec01/`
  scaffolding for `Divisor` and `degree`).
* `AJ` is the identity on `Unit`; the eventual real signature is
  `Div0 X →+ Jac X` (additive group hom into the analytic Jacobian
  defined in `Jacobian/AnalyticJacobian/`).
* No production decl exists yet: when the real `Div0`/`AJ` land in
  `Jacobian/AbelJacobi/`, this file should be retargeted via
  `\lean{...}` annotations in the blueprint TeX rather than carrying
  parallel placeholder definitions. -/

namespace JacobianChallenge.Blueprint

/-- **Sub-leaf 1 (TRIVIAL).** Degree-zero divisors on a compact
connected Riemann surface `X`.

Mathematical definition (per `ref/plans/abel-existence.md`):
`Div0 X := {D : Divisor X // D.degree = 0}`. The eventual production
construction will use `Jacobian/Blueprint/Sec01/Divisor.lean`
(`Blueprint.Divisor`) and
`Jacobian/Blueprint/Sec01/DivisorDegree.lean`
(`Blueprint.Divisor.degree`); together they give the subtype carrying
the deg-0 constraint.

Currently a `Unit` placeholder so downstream stubs (`AJ`,
`AJ_principal_zero`, …) can be type-checked without importing the
Sec01 divisor scaffolding. The placeholder is *intentional*: this
file contains no `sorry` and `lake build
Jacobian.Blueprint.Sec05.AbelExistence` succeeds without pulling in
Mathlib. -/
def Div0 (_X : Type) : Type := Unit

/-- **Sub-leaf 2 (SHORT).** The Abel–Jacobi map
`AJ : Div⁰(X) → Jac(X)`.

Mathematical definition: pick a base point `p₀ ∈ X` and a basis
`ω₁, …, ω_g` of holomorphic 1-forms; for `D = ∑ nᵢ [pᵢ] ∈ Div⁰(X)`,
set `AJ(D) := ∑ nᵢ ∫_{p₀}^{pᵢ} ω  (mod Λ)` where `Λ` is the period
lattice. Path independence on `Div⁰` follows from `deg D = 0` plus
homotopy invariance of integrals of closed forms (Stokes); see
production-side `JacobianChallenge.AbelJacobi.analyticOfCurve` and
`Jacobian/Periods/PeriodFunctional.lean` for the eventual real
plumbing.

Currently the identity `Unit → Unit`. The eventual real signature is
an additive group hom `Div0 X →+ Jac X` into the analytic Jacobian
(`Jacobian/AnalyticJacobian/AnalyticJacobianType.lean`).

Path-independence is a separate downstream obligation tracked under
`lem:aj-path-independence` (already discharged production-side as
`AbelJacobi.analyticOfCurve`, see `ref/scope-out.md` sec05 row 1). -/
def AJ (X : Type) (_D : Div0 X) : Unit := ()

end JacobianChallenge.Blueprint
