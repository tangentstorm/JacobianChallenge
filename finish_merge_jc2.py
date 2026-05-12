import os
path = "Jacobian/StageA/CellularSingular.lean"
with open(path, "r") as f:
    content = f.read()

proof = """by
  let p := LinearMap.range (cellularBoundary K 1)
  have hp : p = ⊥ := by
    rw [cellularBoundary]
    ext x
    simp
  refine ⟨LinearEquiv.refl ℤ _ |>.trans (Submodule.quotEquivOfEqBot p hp).symm⟩"""

content = content.replace("skeletal_h1_quotient_substantive\n    [TopologicalSpace V] (K : AbstractSimplicialComplex V) :\n    Nonempty (cellularH K 1 ≃ₗ[ℤ]\n      cellularChain K 1 ⧸ (LinearMap.range (cellularBoundary K 1))) :=\n  sorry",
                         "skeletal_h1_quotient_substantive\n    [TopologicalSpace V] (K : AbstractSimplicialComplex V) :\n    Nonempty (cellularH K 1 ≃ₗ[ℤ]\n      cellularChain K 1 ⧸ (LinearMap.range (cellularBoundary K 1))) := " + proof)

with open(path, "w") as f:
    f.write(content)
