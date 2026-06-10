import Jacobian.HolomorphicForms.StageExhaustion

/-!
# Stage eventual-containment bounds (Perron engine A4)

Blueprint node: `lem:stage-eventual-containment-bounds`
(subtree A4 of `docs/perron-engine-phase1.md`).

The A2/A3 interfaces (`StageExhaustion.lean`) state containment of the
selected Montel compacta and avoidance of the cuts as filter facts
(`∀ᶠ n in atTop, …`).  This file is the concrete-bound bridge layer that
the analytic stage consumers actually invoke:

* single-compactum bounds `∃ N, ∀ n, N ≤ n → …` for stage domains, cut
  domains, and cut avoidance;
* the and-combined form (contained in the cut domain AND disjoint from the
  cuts, simultaneously);
* uniform bounds over a finite family of selected compacta — one `N`
  valid for every Montel chart-ball compactum in play;
* subset wrappers, so consumers can shrink to closed coordinate subballs
  without re-deriving filter facts.

Everything is pure filter algebra over the interface fields; nothing here
depends on the open A2/A3 provider obligations
(`exists_stageBorderedExhaustion` / `exists_stageCutSystem`).
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {selected : StageSelectedCompactFamily X}

namespace StageBorderedExhaustion

variable (E : StageBorderedExhaustion X selected)

/-- Concrete single-compactum bound for stage containment. -/
theorem exists_stage_bound (i : selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → selected.compact i ⊆ E.stage n :=
  eventually_atTop.mp (E.eventually_contains_selected i)

/-- Uniform stage-containment bound over a finite family of selected
compacta: one `N` works for every index in the family. -/
theorem exists_uniform_stage_bound (s : Finset selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i ∈ s, selected.compact i ⊆ E.stage n :=
  eventually_atTop.mp
    ((eventually_all_finset s).mpr fun i _ =>
      E.eventually_contains_selected i)

/-- Subset wrapper: any set inside a selected compactum inherits its
stage-containment bound. -/
theorem exists_stage_bound_of_subset {K : Set X} {i : selected.Index}
    (hK : K ⊆ selected.compact i) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ E.stage n := by
  obtain ⟨N, hN⟩ := E.exists_stage_bound i
  exact ⟨N, fun n hn => hK.trans (hN n hn)⟩

end StageBorderedExhaustion

namespace StageCutSystem

variable {E : StageBorderedExhaustion X selected}
variable (C : StageCutSystem X selected E)

/-- Concrete single-compactum bound for cut-domain containment. -/
theorem exists_cutDomain_bound (i : selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → selected.compact i ⊆ C.cutDomain n :=
  eventually_atTop.mp (C.eventually_contains_selected i)

/-- Concrete single-compactum bound for cut avoidance. -/
theorem exists_cutSet_avoid_bound (i : selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Disjoint (selected.compact i) (C.cutSet n) :=
  eventually_atTop.mp (C.cuts_avoid_selected_eventually i)

/-- And-combined bound: past one `N`, the selected compactum is contained
in the cut domain AND disjoint from the cuts, simultaneously. -/
theorem exists_contains_and_avoids_bound (i : selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      selected.compact i ⊆ C.cutDomain n ∧
      Disjoint (selected.compact i) (C.cutSet n) :=
  eventually_atTop.mp
    ((C.eventually_contains_selected i).and
      (C.cuts_avoid_selected_eventually i))

/-- Uniform and-combined bound over a finite family of selected compacta:
one `N` past which every compactum in the family is contained in the cut
domain and disjoint from the cuts. -/
theorem exists_uniform_contains_and_avoids_bound
    (s : Finset selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i ∈ s,
      selected.compact i ⊆ C.cutDomain n ∧
      Disjoint (selected.compact i) (C.cutSet n) :=
  eventually_atTop.mp
    ((eventually_all_finset s).mpr fun i _ =>
      (C.eventually_contains_selected i).and
        (C.cuts_avoid_selected_eventually i))

/-- Subset wrapper for the and-combined bound: any set inside a selected
compactum is past the same `N` contained in the cut domain and disjoint
from the cuts. -/
theorem exists_contains_and_avoids_bound_of_subset
    {K : Set X} {i : selected.Index} (hK : K ⊆ selected.compact i) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K ⊆ C.cutDomain n ∧ Disjoint K (C.cutSet n) := by
  obtain ⟨N, hN⟩ := C.exists_contains_and_avoids_bound i
  exact ⟨N, fun n hn =>
    ⟨hK.trans (hN n hn).1, (hN n hn).2.mono_left hK⟩⟩

include C in
/-- The cut-domain bounds land inside the ambient stage as well: the
combined containment is compatible with `cutDomain_subset_stage`. -/
theorem exists_stage_via_cutDomain_bound (i : selected.Index) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → selected.compact i ⊆ E.stage n := by
  obtain ⟨N, hN⟩ := C.exists_cutDomain_bound i
  exact ⟨N, fun n hn => (hN n hn).trans (C.cutDomain_subset_stage n)⟩

end StageCutSystem

end JacobianChallenge.HolomorphicForms
