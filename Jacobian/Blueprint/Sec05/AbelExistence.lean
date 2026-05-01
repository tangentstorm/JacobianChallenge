/-! Blueprint stubs: `thm:abel-existence` (sec05) sub-leaves
classified **TRIVIAL**, **SHORT**, **MEDIUM**, and **HARD** in
`ref/plans/abel-existence.md`.

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

This file stubs **all five leaves**: the TRIVIAL/SHORT leaves
(`Div0`, `AJ`) are sorry-free `Unit` placeholders, and the
MEDIUM/HARD leaves (`AJ_principal_zero`, `existence_of_f`,
`principal_iff_AJ_zero`) carry the concrete Lean signatures from
the Grok plan with `sorry`-bearing proofs (where genuine math is
needed) or full assembly proofs (where the leaf reduces to its
siblings). Per `ref/scope-out.md` the umbrella `thm:abel-existence`
is `DECOMPOSE`; this file is the decomposition target.

## Conventions

* No Mathlib imports — pure Lean placeholders so the dep-graph node
  is pickup-able without dragging in unrelated infrastructure.
* `Div0` is a `Unit` alias; the eventual real definition is
  `{D : Divisor X // D.degree = 0}` (cf. `Jacobian/Blueprint/Sec01/`
  scaffolding for `Divisor` and `degree`).
* `AJ` is the identity on `Unit`; the eventual real signature is
  `Div0 X →+ Jac X` (additive group hom into the analytic Jacobian
  defined in `Jacobian/AnalyticJacobian/`).
* The MEDIUM/HARD leaves and their helper placeholders
  (`MeromorphicFunction`, `divisor`, `IsPrincipal`) live in a nested
  `AbelExistence` namespace to avoid colliding with the genuine
  `JacobianChallenge.Blueprint.MeromorphicFunction` defined in
  `Jacobian/Blueprint/Sec01/MeromorphicFunctionStructure.lean`.
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
file contains no `sorry` for the TRIVIAL/SHORT leaves and `lake build
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

namespace AbelExistence

/-! ## Supporting placeholders for the MEDIUM/HARD leaves

`MeromorphicFunction X`, `divisor f`, and `IsPrincipal D` are needed
to type-check leaves 3–5. Like `Div0` and `AJ`, they are deliberate
`Unit`/`Prop` placeholders so this file can be compiled without
Mathlib; the eventual real definitions live in
`Mathlib.Analysis.Meromorphic.Divisor` (`MeromorphicOn`,
`MeromorphicOn.divisor`) and the Sec01 scaffolding
`JacobianChallenge.Blueprint.MeromorphicFunction` (the *structural*
form in `Jacobian/Blueprint/Sec01/MeromorphicFunctionStructure.lean`).

These helpers are isolated in the nested `AbelExistence` namespace so
they do not collide with the Sec01 `MeromorphicFunction` structure
that already lives at `JacobianChallenge.Blueprint.MeromorphicFunction`. -/

/-- Placeholder for the type of meromorphic functions on `X`, scoped
to the Sec05 Abel-existence stubs. The real definition will use
Mathlib's `MeromorphicOn` from `Mathlib.Analysis.Meromorphic.Basic`
(or the structural Sec01 form
`JacobianChallenge.Blueprint.MeromorphicFunction`) once that chain
is wired up. -/
def MeromorphicFunction (_X : Type) : Type := Unit

/-- Placeholder for the divisor `(f) := ∑_{p ∈ X} ord_p(f) ⋅ [p]`
of a meromorphic function. The real construction uses
`MeromorphicOn.divisor` from
`Mathlib.Analysis.Meromorphic.Divisor`; the resulting divisor lies
in `Div0 X` because the sum of orders of a meromorphic function on
a compact Riemann surface is zero (residue theorem applied to
`df/f`, see `thm:principal-degree-zero` in `ref/scope-out.md`). -/
def divisor {X : Type} (_f : MeromorphicFunction X) : Div0 X := ()

/-- Placeholder predicate: a divisor is **principal** iff it is the
divisor of some meromorphic function `f ≠ 0`. The real definition
will additionally require `f ≠ 0`; here, with `MeromorphicFunction`
a `Unit` placeholder, the nonvanishing constraint is suppressed.

`IsPrincipal D := ∃ f : MeromorphicFunction X, divisor f = D`. -/
def IsPrincipal {X : Type} (D : Div0 X) : Prop :=
  ∃ f : MeromorphicFunction X, divisor f = D

/-! ## MEDIUM/HARD leaves -/

/-- **Sub-leaf 3 (MEDIUM).** The Abel–Jacobi map vanishes on
principal divisors:
`AJ (divisor f) = 0` for every meromorphic `f` on `X`.

**Proof sketch (per `ref/plans/abel-existence.md`).** Apply the
residue theorem (equivalently, Stokes) to the logarithmic
derivative `df/f`. The integral of `df/f` along any cycle in
`X ∖ supp(divisor f)` is `2πi ⋅ ∑ residues = 0`. Restricted to a
homology basis, this means each period of the divisor pulls back
to a lattice element, i.e. `AJ (divisor f) = 0` in `Jac X`.

The Mathlib hooks are
`Mathlib.Analysis.Meromorphic.Divisor.MeromorphicOn.divisor` for
the source side and a not-yet-formalised residue/Stokes statement
on a compact Riemann surface (cf. `thm:stokes-on-rs-with-boundary`
in `ref/scope-out.md`) for the target side. -/
theorem AJ_principal_zero (X : Type) (f : MeromorphicFunction X) :
    AJ X (divisor f) = () := by
  sorry

/-- **Sub-leaf 4 (HARD).** Existence direction of Abel's theorem:
if `AJ D = 0` for a degree-zero divisor `D`, then `D` is the
divisor of some meromorphic function on `X`.

**Proof sketch (per `ref/plans/abel-existence.md`).** Either
(a) construct `f` via the Riemann theta function:
`f(p) := θ(AJ([p] - [p₀]) - e)` for a suitable vector `e`
depending on `D`, then verify `divisor f = D` using the heat-kernel
properties of `θ`; or (b) cut `X` along a symplectic homology basis
to obtain a fundamental polygon, define a multivalued logarithmic
primitive, exponentiate, and check well-definedness using
`AJ D = 0` (the period lattice obstruction vanishes). Both routes
need the period-lattice / theta-function infrastructure listed
**ABSENT** in the plan's Mathlib inventory. ≤250 LOC of glue once
the primitives land. -/
theorem existence_of_f (X : Type) (D : Div0 X) (_h : AJ X D = ()) :
    ∃ f : MeromorphicFunction X, divisor f = D := by
  sorry

/-- **Sub-leaf 5 (MEDIUM).** Abel's theorem assembled:
`D` is principal iff `AJ D = 0`.

**Proof.** The forward direction unpacks `IsPrincipal` to extract
`f` with `divisor f = D` and applies `AJ_principal_zero`. The
backward direction applies `existence_of_f` to obtain the witness.
This assembly is purely propositional and matches the closed-form
proof in §4 of `ref/plans/abel-existence.md`. -/
theorem principal_iff_AJ_zero (X : Type) (D : Div0 X) :
    IsPrincipal D ↔ AJ X D = () := by
  refine ⟨fun ⟨f, hf⟩ => ?_, fun h => existence_of_f X D h⟩
  -- Forward: `D = divisor f` so `AJ X D = AJ X (divisor f) = 0` by `AJ_principal_zero`.
  exact hf ▸ AJ_principal_zero X f

end AbelExistence

end JacobianChallenge.Blueprint
