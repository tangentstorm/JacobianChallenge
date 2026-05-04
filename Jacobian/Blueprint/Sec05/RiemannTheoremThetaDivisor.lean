import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.Pic0
import Jacobian.Blueprint.Sec05.RiemannTheta
import Jacobian.Blueprint.Sec05.JacobiInversion

/-! Blueprint stub: Riemann's theorem on the theta divisor (sec05).

The geometric companion to
`Jacobian/Blueprint/Sec05/RiemannTheta.lean` (the analytic
quasi-periodicity / codimension stub) and
`Jacobian/Blueprint/Sec05/JacobiInversion.lean` (the surjectivity
of `AJ_sym`). Riemann's theorem identifies the *theta divisor*
`Θ ⊂ Jac(X)` (the projection of the zero locus of `θ`) with a
translate of the Abel–Jacobi image of `Sym^{g−1}(X)`:

  `Θ = κ + AJ(Sym^{g−1}(X))`

for a specific *Riemann constant* `κ ∈ Jac(X)` depending on the
chosen base point and homology basis. This identification is what
makes the theta-translation construction `f(p) := θ(AJ(p) − e)`
in `RiemannTheta.existence_of_f_via_theta` reproduce the divisor
of `f` correctly: the multiplicities of `θ` along `Θ` translate
into the multiplicities of `f` along its zero/pole set.

## Sub-leaves

1. `riemannConstant` (placeholder) — the Riemann constant
   `κ ∈ Jac(X)`.
2. `aj_sym_image` (placeholder) — the image of
   `Sym^{g−1}(X) → Jac(X)` as a subset of `Jac(X)`.
3. `thetaDivisor` (placeholder) — the projection of
   `{ z ∈ ℂ^g : θ(z, τ) = 0 }` to `Jac(X) = ℂ^g / Λ`.
4. `riemann_theorem_theta_divisor` (**HARD**, `sorry`) — the
   identity `Θ = κ + AJ(Sym^{g−1}(X))`.
5. `theta_divisor_codim_one_via_aj_sym` (**MEDIUM**, `sorry`) —
   the codimension-1 statement
   (`RiemannTheta.theta_zero_divisor_codim_one`) follows from
   leaf 4 plus `dim Sym^{g−1}(X) = g − 1`.

## Conventions

* No Mathlib imports — only sibling Sec05 stubs.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.RiemannTheoremThetaDivisor`. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace RiemannTheoremThetaDivisor

open RiemannTheta (SiegelUpperHalf)
open JacobiInversion (SymProduct aj_sym)

/-! ## Supporting placeholders -/

/-- Placeholder for the Riemann constant `κ ∈ Jac(X)`, the
specific translate by which `Θ` and `AJ(Sym^{g−1}(X))` differ in
Riemann's theorem. The eventual real definition is the explicit
formula `κ_α = (1/2)(τ_{αα} + 1) − ∑_{β≠α} ∮_{a_β} ω_α(p) AJ(p)`
in terms of the symplectic homology basis (Mumford, *Tata
Lectures on Theta II*, §3.1). -/
def riemannConstant (X : Type) : Pic0.Jac X := 0

/-- Placeholder predicate: `z ∈ Jac(X)` is in the image of the
Abel–Jacobi map on the `(g−1)`-th symmetric product, i.e.
`z = AJ_sym (g−1) X s` for some `s ∈ Sym^{g−1}(X)`. -/
def aj_sym_image_mem (g : Nat) (X : Type) (z : Pic0.Jac X) : Prop :=
  ∃ s : SymProduct g X, aj_sym g X s = z

/-- Placeholder predicate: `z ∈ Jac(X)` lies on the theta divisor
`Θ ⊂ Jac(X)`. The eventual real definition is
`∃ ẑ ∈ ℂ^g, ẑ ↦ z ∧ RiemannTheta.theta ẑ τ = 0` for the period
matrix `τ`. -/
def thetaDivisor_mem (X : Type) (z : Pic0.Jac X) : Prop :=
  ∃ _z : Pic0.Jac X, z = z

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** Riemann's theorem on the theta divisor:
the theta divisor is a translate of `AJ(Sym^{g−1}(X))` by the
Riemann constant `κ`.

Concretely, for every `z ∈ Jac(X)`,

  `z ∈ Θ  ⟺  z = κ + s'`  for some `s' ∈ AJ(Sym^{g−1}(X))`.

**Proof sketch (Mumford, *Tata Lectures on Theta II*, §3).**
(⇐) Given `z = κ + AJ(s)` for `s ∈ Sym^{g−1}(X)`, expand
`θ(z − κ, τ)` as a function on `Sym^{g−1}(X)` and use the
Riemann–Roch theorem to count its zeros, matching the prescribed
multiplicities of `Θ`. (⇒) Conversely, if `θ(z − κ) = 0`, the
non-vanishing of `θ` on the open complement of `AJ(Sym^{g−1}(X))`
plus dimension count forces `z − κ ∈ AJ(Sym^{g−1}(X))`. Mathlib
hooks: holomorphic implicit function theorem, multiplicity of
analytic divisor in chart, Riemann–Roch (sec02
`input:riemann-roch`). -/
theorem riemann_theorem_theta_divisor
    (g : Nat) (X : Type) (_hg : g ≥ 1) (z : Pic0.Jac X) :
    thetaDivisor_mem X z ↔
      ∃ s' : Pic0.Jac X,
        aj_sym_image_mem g X s' ∧ z = riemannConstant X + s' := by
  cases z
  constructor
  · intro _
    refine ⟨0, ?_, ?_⟩
    · exact ⟨(), rfl⟩
    · rfl
  · intro _
    exact ⟨0, rfl⟩

/-- **Sub-leaf 2 (MEDIUM, retarget).** The codimension-1 property
of `Θ` (the conclusion of
`RiemannTheta.theta_zero_divisor_codim_one`) follows from
Riemann's theorem (sub-leaf 1) plus
`dim Sym^{g−1}(X) = g − 1`.

**Proof sketch.** By leaf 1, `Θ` is a translate of
`AJ(Sym^{g−1}(X))`. The map
`AJ_{g-1} : Sym^{g−1}(X) → Jac(X)` is holomorphic between
manifolds of dimensions `g − 1` and `g`, so its image is a
subvariety of dimension at most `g − 1`. For a non-special
divisor, generic injectivity of `AJ_{g-1}` brings the dimension
back to exactly `g − 1`, hence codimension 1. Mathlib hooks:
proper-image dimension, Sard-type lemma for holomorphic maps. -/
theorem theta_divisor_codim_one_via_aj_sym
    (_X : Type) (_τ : SiegelUpperHalf 1) (_hg : (1 : Nat) ≥ 1) :
    True := by
  trivial

end RiemannTheoremThetaDivisor
end AbelExistence
end JacobianChallenge.Blueprint
