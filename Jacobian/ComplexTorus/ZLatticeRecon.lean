import Mathlib.Algebra.Module.ZLattice.Basic
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ZLatticeFundDom

/-!
# Reconnaissance: bridging `FullComplexLattice` and `ZLattice.IsZLattice`

This file is a Queue B reconnaissance packet. The goal is *not* a full
proof but a concrete attempt to construct a `FullComplexLattice V` from
a Mathlib `ZLattice.IsZLattice` predicate, leaving sorries that
explicitly name the missing bridge lemmas. This will tell us whether
the eventual replacement of our placeholder structure with a Mathlib
predicate is straightforward or needs intermediate work.

## Compatibility findings (Aristotle a68d37f4, 2026-04-25)

`IsZLattice K L` requires `NormedSpace K E`, parametric in `K`. Our
space `V` has `NormedSpace ℂ V`, which gives `NormedSpace ℝ V` via the
`ℝ → ℂ` scalar-tower. The signature uses `IsZLattice ℝ L`, which is
compatible: `ℝ` has `FloorRing`, `HasSolidNorm`, `LinearOrder`, and
`IsStrictOrderedRing`.

`FiniteDimensional ℝ V` follows from `FiniteDimensional ℂ V` via
`Module.Finite.trans`, and `ProperSpace V` from
`FiniteDimensional.proper_real`.

The five `FullComplexLattice` fields can be addressed as follows:

1. **`subgroup`**: Direct — `L.toAddSubgroup`.
2. **`isClosed`**: Available via `AddSubgroup.isClosed_of_discrete`, but
   requires `DiscreteTopology L.toAddSubgroup` which must be
   transferred from the given `DiscreteTopology L` (on the
   `Submodule`). Type-level mismatch — small bridge below
   (`discreteTopology_toAddSubgroup`).
3. **`fundamentalDomain`**: Use `closure (ZSpan.fundamentalDomain bR)`
   where `bR := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L`. The
   closure is needed because `ZSpan.fundamentalDomain` uses half-open
   intervals `[0,1)` and is not closed.
4. **`fundamentalDomain_isCompact`**: Follows from
   `ZSpan.fundamentalDomain_isBounded` +
   `Bornology.IsBounded.isCompact_closure` in `ProperSpace V`.
5. **`fundamentalDomain_covers`**: Reduces to
   `ZSpan.exist_unique_vadd_mem_fundamentalDomain` plus a small
   packaging step that converts `vadd` to subtraction and identifies
   `span ℤ (Set.range bR) = L.toAddSubgroup`. Aristotle's attempt
   (using `grind`) failed to compile; left as `sorry` here pending a
   small dedicated helper:
   `ZLattice.exists_sub_mem_closure_fundamentalDomain`. The helper is
   purely a packaging lemma over `ℝ`-linear data and does not need any
   `ℂ`-specific material.

**Overall verdict**: the bridge is feasible. The non-trivial gap is
the covering-property packaging.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

/-! ### Auxiliary instances -/

/-- Transfer `DiscreteTopology` from a `Submodule ℤ V` to its
underlying `AddSubgroup V`. The carrier sets are definitionally equal,
but the Lean types differ, so we transfer via the inclusion map. -/
private theorem discreteTopology_toAddSubgroup
    (L : Submodule ℤ V) [DiscreteTopology L] :
    DiscreteTopology L.toAddSubgroup :=
  DiscreteTopology.of_continuous_injective
    (f := fun (x : L.toAddSubgroup) => (⟨x.1, x.2⟩ : L))
    (continuous_induced_rng.mpr continuous_subtype_val)
    (fun _ _ h => Subtype.ext (congr_arg Subtype.val h))

/--
Attempt to package a `ZLattice` as a `FullComplexLattice`. Four of the
five fields admit clean proofs via the `ZSpan` / `ZLattice` API; the
covering field is left as a documented `sorry` pending the small
packaging helper described in the file header.
-/
noncomputable def fullComplexLatticeOfZLattice
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    FullComplexLattice V where
  subgroup := L.toAddSubgroup
  isClosed := by
    haveI := discreteTopology_toAddSubgroup L
    exact AddSubgroup.isClosed_of_discrete
  isDiscrete := discreteTopology_toAddSubgroup L
  fundamentalDomain := by
    haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) (A := ℂ) (M := V)
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    haveI := ZLattice.module_free ℝ L
    haveI := ZLattice.module_finite ℝ L
    exact closure (ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))
  fundamentalDomain_isCompact := by
    haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) (A := ℂ) (M := V)
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    haveI := ZLattice.module_free ℝ L
    haveI := ZLattice.module_finite ℝ L
    exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  fundamentalDomain_covers := by
    haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) (A := ℂ) (M := V)
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    intro v
    exact exists_sub_mem_closure_fundamentalDomain L v

end JacobianChallenge.ComplexTorus
