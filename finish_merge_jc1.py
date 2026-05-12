import os
path = "Jacobian/StageA/CellularSingular.lean"
with open(path, "r") as f:
    content = f.read()

proof = """by
  obtain ⟨e_quot⟩ := skeletal_h1_quotient_substantive K
  let phi1 := cellularToSingularChain K 1
  let e_cell : cellularH K 1 ≃ₗ[ℤ] cellularChain K 1 := (e_quot.trans (LinearEquiv.ofEq _ _ (by
    rw [cellularBoundary]; simp))).symm
  obtain ⟨e_rel⟩ := _hLES 1
  let e_sing : relativeSkeletalH K 1 ≃ₗ[ℤ] singularH1 (AbstractSimplicialComplex.Geometric K) :=
    sorry
  exact ⟨e_cell.trans (e_rel.symm.trans e_sing.symm)⟩"""

content = content.replace("skeletal_h1_five_lemma_identity\n    [TopologicalSpace V] (K : AbstractSimplicialComplex V)\n    [AbstractSimplicialComplex.Finite K] :\n    Nonempty (cellularH K 1 ≃ₗ[ℤ]\n      singularH1 (AbstractSimplicialComplex.Geometric K)) :=\n  sorry",
                         "skeletal_h1_five_lemma_identity\n    [TopologicalSpace V] (K : AbstractSimplicialComplex V)\n    [AbstractSimplicialComplex.Finite K] :\n    Nonempty (cellularH K 1 ≃ₗ[ℤ]\n      singularH1 (AbstractSimplicialComplex.Geometric K)) := " + proof)

with open(path, "w") as f:
    f.write(content)
