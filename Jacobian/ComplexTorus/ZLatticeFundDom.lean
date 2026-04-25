import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Packaging helper: `ZLattice` fundamental domain covers in subtraction form

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

This is the small dedicated packaging lemma flagged by the
`ZLatticeRecon.lean` reconnaissance packet. The Mathlib API exposes the
fundamental-domain covering property in `vadd` form via
`ZSpan.exist_unique_vadd_mem_fundamentalDomain`. To plug into our
`FullComplexLattice.fundamentalDomain_covers` (which is in subtraction
form on the underlying `AddSubgroup`), we need:

- rewrite `v +ᵥ x ∈ fundamentalDomain` as `x - (-↑v) ∈ fundamentalDomain`;
- transport membership in `Submodule.span ℤ (Set.range basis)` to
  membership in the lattice's `toAddSubgroup`, using
  `Module.Basis.ofZLatticeBasis_span`;
- weaken `∈ fundamentalDomain` to `∈ closure fundamentalDomain`.

The result is purely a ℝ-linear packaging lemma — no ℂ-specific
material.
-/

namespace JacobianChallenge.ComplexTorus

open Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]

/-- The covering property of a `ZLattice`'s fundamental domain stated in
the subtraction-and-AddSubgroup form that `FullComplexLattice` expects. -/
lemma exists_sub_mem_closure_fundamentalDomain
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : E) :
    ∃ g ∈ L.toAddSubgroup,
      v - g ∈
        closure (ZSpan.fundamentalDomain
          ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
  set bR := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  obtain ⟨w, hw, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain bR v
  refine ⟨-(w : E), ?_, ?_⟩
  · have hmem : (w : E) ∈ (L : Set E) := by
      have h := w.2
      change (w : E) ∈ (span ℤ (Set.range bR) : Set E) at h
      rwa [show (span ℤ (Set.range bR) : Set E) = (L : Set E) from
        congr_arg _ (Basis.ofZLatticeBasis_span ℝ L (Free.chooseBasis ℤ L))] at h
    exact L.toAddSubgroup.neg_mem hmem
  · apply subset_closure
    show v - -(w : E) ∈ ZSpan.fundamentalDomain bR
    have : v - -(w : E) = (w : E) + v := by abel
    rw [this, show (w : E) + v = w +ᵥ v from rfl]
    exact hw

end JacobianChallenge.ComplexTorus
