/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite chart cover for compact charted spaces

A compact charted space modelled on `EuclideanSpace ℝ (Fin 2)` admits a finite
chart cover drawn from its atlas.

This is leaf A1.1 of the surface-classification plan (§ 4).
-/

open Set in
theorem compact_2manifold_has_finite_chart_cover
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [CompactSpace M] :
    ∃ (n : ℕ) (cover : Fin n → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))),
      (∀ i, cover i ∈ atlas (EuclideanSpace ℝ (Fin 2)) M) ∧
      (⋃ i : Fin n, (cover i).source) = (Set.univ : Set M) := by
  -- A compact cover of M by open sets is given by the sources of the charts.
  have hchart : ∀ x : M, x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source ∧ (chartAt (EuclideanSpace ℝ (Fin 2)) x) ∈ atlas (EuclideanSpace ℝ (Fin 2)) M := by
    aesop;
  -- By compactness, there exists a finite subcover of this cover.
  obtain ⟨t, ht⟩ : ∃ t : Finset M, ⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin 2)) x).source = Set.univ := by
    have h_compact : IsCompact (Set.univ : Set M) := by
      exact isCompact_univ;
    have := h_compact.elim_finite_subcover ( fun x => ( chartAt ( EuclideanSpace ℝ ( Fin 2 ) ) x ).source ) ( fun x => ( OpenPartialHomeomorph.open_source _ ) );
    exact Exists.elim ( this fun x _ => Set.mem_iUnion.2 ⟨ x, hchart x |>.1 ⟩ ) fun t ht => ⟨ t, Set.Subset.antisymm ( Set.subset_univ _ ) ht ⟩;
  -- We can re-index the finite subcover to be indexed by `Fin n` for some `n`.
  obtain ⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n ≃ t, True := by
    exact ⟨ t.card, Fintype.equivOfCardEq ( by simp +decide ), trivial ⟩;
  refine' ⟨ n, fun i => chartAt ( EuclideanSpace ℝ ( Fin 2 ) ) ( e i ), _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
  exact fun x => by rcases ht x with ⟨ i, hi, hx ⟩ ; exact ⟨ e.symm ⟨ i, hi ⟩, by simpa using hx ⟩ ;