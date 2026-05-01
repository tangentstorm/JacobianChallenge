/-! # Blueprint stub: TRIVIAL / SHORT sub-leaves of `def:symplectic-basis`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

Reference plan: `ref/plans/symplectic-basis.md` (decomposition of the
classical statement that the first integral homology `H₁(X, ℤ)` of a
compact connected Riemann surface of genus `g ≥ 1` admits a basis of
rank `2g` on which the algebraic intersection pairing is the standard
symplectic block form `J_g = [[0, I_g], [-I_g, 0]]`).

This file records *only* the leaves the plan classified as TRIVIAL or
SHORT — pure data wrappers and propositional placeholders that can be
named today without committing to a concrete homology / intersection
infrastructure (which is still ABSENT in the pinned Mathlib v4.28.0
inventory). Each declaration is a `Unit`-valued `def` or a `True`-valued
`theorem` so the module is sorry-free and import-light; the real
mathematical content is deferred to the MEDIUM / HARD sub-leaves
(`intersectionForm`, `existsSymplecticBasis`, `intersectionForm_nondeg`)
which need separate cloud-worker assignments.

Coverage of the plan's sub-leaves:

* sub-leaf #2 (SHORT) `isSymplecticBasis` — propositional placeholder.
* sub-leaf #3 (SHORT) `h1_free_of_genus`  — propositional placeholder.
* sub-leaf #5 (TRIVIAL) `standardSymplecticForm` — `Unit`-valued data
  placeholder for the standard `2g × 2g` symplectic block matrix.

Out of scope here (tracked elsewhere):

* sub-leaf #1 (MEDIUM) `intersectionForm`
* sub-leaf #4 (HARD)   `existsSymplecticBasis`
* sub-leaf #6 (MEDIUM) `intersectionForm_nondeg`

NOTE FOR WORKERS: when the homology API and intersection pairing land,
each placeholder here should be replaced (not added to) by a real
declaration with the signature listed in
`ref/plans/symplectic-basis.md` §3. Until then these stubs exist purely
to make the blueprint nodes pick-up-able and to give downstream
assembly code a stable name to forward-reference.
-/

namespace JacobianChallenge.Blueprint.Sec03

/-- Plan sub-leaf #5 (TRIVIAL): the standard symplectic block matrix
`J_g = [[0, I_g], [-I_g, 0]] : Matrix (Fin (2*g)) (Fin (2*g)) ℤ`.

Recorded here as a `Unit`-valued placeholder, since the real signature
needs `Matrix` from Mathlib and a paired homology rank `2*g` that is
not yet committed to a definition. The eventual replacement is

```
def standardSymplecticForm (g : ℕ) : Matrix (Fin (2*g)) (Fin (2*g)) ℤ
```

with entries `1` on the upper-right `g × g` block, `-1` on the
lower-left `g × g` block, and `0` elsewhere. -/
def standardSymplecticForm (_g : Nat) : Unit := ()

/-- Plan sub-leaf #2 (SHORT): predicate stating that a basis of the
homology lattice has standard symplectic intersection pairings, i.e.

```
∀ i j, intersectionForm (b i) (b j) = standardSymplecticForm g i j
```

Recorded here as a `True`-valued propositional placeholder. The eventual
replacement takes a basis `b : Basis (Fin (2*g)) ℤ (H₁ X ℤ)` together
with the intersection form (sub-leaf #1, MEDIUM) and the standard form
(sub-leaf #5, TRIVIAL) once both are available. -/
def isSymplecticBasis (_g : Nat) : Prop := True

/-- `isSymplecticBasis` placeholder is trivially inhabited. Useful as a
forward-reference target so downstream assembly code (`symplecticBasis`
in the plan's §4) can say "the chosen basis is symplectic" without
unfolding the placeholder. -/
theorem isSymplecticBasis_holds (g : Nat) : isSymplecticBasis g := trivial

/-- Plan sub-leaf #3 (SHORT): for a compact connected Riemann surface
`X` of genus `g`, the first integral singular homology `H₁(X, ℤ)` is a
free abelian group of rank `2 * g`.

Recorded here as a `True`-valued propositional placeholder so the
blueprint label has a Lean handle. The eventual replacement is

```
lemma h1_free_of_genus (X : CompactRiemannSurface g) :
    Module.Free ℤ (H₁ X ℤ) ∧ Module.rank ℤ (H₁ X ℤ) = 2 * g
```

(or the equivalent `Basis (Fin (2*g)) ℤ (H₁ X ℤ)` form), provable from
the classification of compact orientable surfaces plus the singular
homology computation. -/
theorem h1_free_of_genus (_g : Nat) : True := trivial

end JacobianChallenge.Blueprint.Sec03
