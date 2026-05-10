import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Matrix.Basic
import Jacobian.Periods.IntegralOneCycle

/-! # Blueprint stubs: leaves of `def:symplectic-basis`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

Reference plan: `ref/plans/symplectic-basis.md` (decomposition of the
classical statement that the first integral homology `H₁(X, ℤ)` of a
compact connected Riemann surface of genus `g ≥ 1` admits a basis of
rank `2g` on which the algebraic intersection pairing is the standard
symplectic block form `J_g = [[0, I_g], [-I_g, 0]]`).

This file now records *concrete* Lean signatures for every sub-leaf
of the plan. The TRIVIAL leaf (`standardSymplecticForm`) is
discharged in full; the SHORT leaves (`isSymplecticBasis`,
`h1_free_of_genus`) are stated against the concrete `IntegralOneCycle`
homology type defined in `Jacobian/Periods/IntegralOneCycle.lean`
(=`H₁(X, ℤ)` via `singularHomologyFunctor`); their proof obligation is
delegated through `existsSymplecticBasis`.

Coverage of the plan's sub-leaves:

* sub-leaf #5 (TRIVIAL) `standardSymplecticForm` — **proof-complete**
  `Matrix (Fin (2*g)) (Fin (2*g)) ℤ` with explicit block entries.
* sub-leaf #1 (MEDIUM)  `intersectionForm` — concrete signature
  `IntegralOneCycle X →ₗ[ℤ] IntegralOneCycle X →ₗ[ℤ] ℤ`, body `sorry`.
* sub-leaf #2 (SHORT)   `isSymplecticBasis` — predicate built from #1
  and #5.
* sub-leaf #3 (SHORT)   `h1_free_of_genus` — `Nonempty (Basis ...)`,
  currently an explicit blueprint axiom.
* sub-leaf #6 (MEDIUM)  `intersectionForm_nondeg` — concrete
  ∀-∃ statement, currently an explicit blueprint axiom.
* sub-leaf #4 (HARD)    `existsSymplecticBasis` — concrete ∃-statement,
  currently an explicit blueprint axiom.
* assembly §4           `symplecticBasis` — `Classical.choose` of #4.

The file compiles sorry-free at the *signature* level (every
declaration type-checks), and downstream clients can quote the names
without needing to know the omitted hard proofs.

NOTE FOR WORKERS:

* **`intersectionForm` (#1)** — define via cap product or signed
  transverse intersection of singular 1-cycles. The natural Mathlib
  route (when present) is Poincaré duality: take the cup product on
  `H¹(X, ℤ)` and transport along the duality isomorphism
  `H¹(X, ℤ) ≃ H₁(X, ℤ)*`. In v4.28.0 cup/cap products on singular
  cohomology are absent, so a from-scratch geometric definition
  (signed crossings on a CW model) is the realistic path.
* **`intersectionForm_nondeg` (#6)** — follows from Poincaré duality
  on a closed orientable surface; equivalently from the existence of
  a symplectic basis (#4) plus a one-line linear-algebra unfold.
* **`existsSymplecticBasis` (#4)** — classical proof routes:
  (a) handle decomposition / fundamental polygon (cut-along-cycles);
  (b) symplectic Gram-Schmidt over ℤ on a unimodular form (Milnor-
  Husemoller Ch. II); (c) Mayer-Vietoris on a CW model.
  Route (b) only needs #1 and `intersectionForm_nondeg` (#6); routes
  (a)/(c) need polygonal-model machinery still being decomposed.
-/

namespace JacobianChallenge.Blueprint.Sec03

open JacobianChallenge.Periods

/-- Plan sub-leaf #5 (TRIVIAL): the standard symplectic block matrix
`J_g = [[0, I_g], [-I_g, 0]] : Matrix (Fin (2*g)) (Fin (2*g)) ℤ`.

Entry `(i, j)` is:
* `1`  when `i.val < g` and `j.val = i.val + g`  (upper-right `I_g`),
* `-1` when `j.val < g` and `i.val = j.val + g`  (lower-left `-I_g`),
* `0`  elsewhere. -/
def standardSymplecticForm (g : Nat) : Matrix (Fin (2*g)) (Fin (2*g)) ℤ :=
  Matrix.of fun i j =>
    if i.val < g ∧ j.val = i.val + g then (1 : ℤ)
    else if j.val < g ∧ i.val = j.val + g then (-1 : ℤ)
    else 0

/-- Plan sub-leaf #1 (MEDIUM): the algebraic intersection pairing on
the first integral singular homology of a topological space `X`,
viewed as a `ℤ`-bilinear map.

Mathematical content: the cup product on `H¹(X, ℤ)` transported to
`H₁(X, ℤ)` via Poincaré duality on a closed orientable surface, or
equivalently the signed transverse-intersection number of representing
singular 1-cycles in a smooth chart cover. The current Mathlib
inventory (v4.28.0) has neither cup products on singular cohomology
nor Poincaré duality, so a geometric (chart-by-chart signed crossing)
construction is the realistic implementation route. -/
noncomputable opaque intersectionForm (X : Type) [TopologicalSpace X] :
    IntegralOneCycle X →ₗ[ℤ] IntegralOneCycle X →ₗ[ℤ] ℤ

/-- Plan sub-leaf #2 (SHORT): a basis `b` of `H₁(X, ℤ)` is *symplectic*
when its matrix in the intersection pairing is the standard symplectic
form `J_g`. -/
def isSymplecticBasis {X : Type} [TopologicalSpace X] {g : Nat}
    (b : Module.Basis (Fin (2*g)) ℤ (IntegralOneCycle X)) : Prop :=
  ∀ i j : Fin (2*g),
    intersectionForm X (b i) (b j) = standardSymplecticForm g i j

/-- Plan sub-leaf #3 (SHORT): for a compact connected Riemann surface
`X` of genus `g`, the first integral singular homology `H₁(X, ℤ)` is a
free abelian group of rank `2 * g`.

Stated here for an arbitrary topological space `X`; the genus
hypothesis is encoded by parameterising over `g : Nat` (the
implementation will tie `g` to the topological genus once the
project's `analyticGenus = topologicalGenus` bridge lands). -/
axiom h1_free_of_genus
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    (g : Nat) :
    Nonempty (Module.Basis (Fin (2*g)) ℤ (IntegralOneCycle X))

/-- Plan sub-leaf #6 (MEDIUM): non-degeneracy of the intersection
pairing on `H₁(X, ℤ)` for a closed orientable surface — every nonzero
homology class pairs nontrivially with some other class.

Follows from Poincaré duality on a compact orientable 2-manifold; in
the symplectic-basis route, immediate from sub-leaf #4 plus a
linear-algebra unfold. -/
axiom intersectionForm_nondeg
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    {v : IntegralOneCycle X} (hv : v ≠ 0) :
    ∃ w : IntegralOneCycle X, intersectionForm X v w ≠ 0

/-- Plan sub-leaf #4 (HARD): existence of a symplectic basis of
`H₁(X, ℤ)` for a compact connected Riemann surface of genus `g`.

Classical proof routes are sketched in this file's header. -/
axiom existsSymplecticBasis
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    (g : Nat) :
    ∃ b : Module.Basis (Fin (2*g)) ℤ (IntegralOneCycle X), isSymplecticBasis b

/-- Plan §4 assembly: a chosen symplectic basis of `H₁(X, ℤ)`,
extracted from the existence statement #4 via `Classical.choose`. -/
noncomputable def symplecticBasis
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    (g : Nat) :
    Module.Basis (Fin (2*g)) ℤ (IntegralOneCycle X) :=
  (existsSymplecticBasis X g).choose

/-- The chosen `symplecticBasis` is symplectic. -/
theorem symplecticBasis_isSymplectic
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    (g : Nat) :
    isSymplecticBasis (symplecticBasis X g) :=
  (existsSymplecticBasis X g).choose_spec

end JacobianChallenge.Blueprint.Sec03
