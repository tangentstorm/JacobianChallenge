import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite CW structure (real frontier structure)

A `FiniteCWStructure X` records the discrete data of a finite CW
decomposition of a topological space `X`:

* `cellCount n`     — the number of `n`-cells, eventually zero;
* `attachingMap`    — for each `n` and each `i : Fin (cellCount n)`, an
                      attaching map `S^{n-1} → X`;
* `characteristic`  — for each `n`, `i`, the characteristic map
                      `D^n → X`.

The structure is *not* an axiomatised CW complex: it does not enforce
the gluing/closure conditions of Hatcher's CW axioms, only records the
data that those axioms would constrain. Down-stream uses that need the
discrete data (cell counts, indexing) work directly with the fields;
uses that would need the topological CW axioms must request named
companions.

This intentionally replaces the earlier placeholder
`FiniteCWStructure := PUnit` so that proofs can use the data inside the
structure. The previous `Nonempty (FiniteCWStructure X)` provider for a
compact Riemann surface (`compactRiemannSurface_hasFiniteCWStructure`,
in `Jacobian/Periods/CellularHomologyRS.lean`) becomes a proper
sub-sorry — namely Radó triangulation — once `FiniteCWStructure` carries
real data.
-/

namespace JacobianChallenge.Periods

/-- **Finite CW structure (frontier real structure).**

A `FiniteCWStructure X` records the discrete data of a finite CW
decomposition of a topological space `X`: cell counts (eventually zero)
together with attaching/characteristic maps for each cell.

This structure **does not** enforce CW gluing/closure axioms; it
records the data that those axioms would constrain. The fields are
populated by named providers (e.g. `compactRiemannSurface_hasFiniteCWStructure`,
which is itself a Radó-triangulation sub-sorry in v4.28.0). -/
structure FiniteCWStructure
    (X : Type) [TopologicalSpace X] : Type where
  /-- Number of `n`-cells in the decomposition. -/
  cellCount : ℕ → ℕ
  /-- The cell counts are eventually zero (finite total dimension and
  finitely many cells). -/
  cellCount_eventually_zero : ∃ N : ℕ, ∀ n, N ≤ n → cellCount n = 0
  /-- Attaching map of the `i`-th `n`-cell: a continuous map
  `S^{n-1} → X` (here `S^{n-1} = Metric.sphere (0 : ℝ^n) 1`; for `n = 0`
  this sphere is empty, so the field is automatically a constant map
  out of the empty type). -/
  attachingMap (n : ℕ) (i : Fin (cellCount n)) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, X)
  /-- Characteristic map of the `i`-th `n`-cell: a continuous map
  `D^n → X` (here `D^n = Metric.closedBall (0 : ℝ^n) 1`). The CW
  axioms (not enforced here) would require this map to restrict to
  `attachingMap n i` along the boundary sphere. -/
  characteristic (n : ℕ) (i : Fin (cellCount n)) :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, X)

namespace FiniteCWStructure

variable {X : Type} [TopologicalSpace X]

/-- The total number of cells across all dimensions, summed over the
dimensions below the eventually-zero threshold. Implementation choice:
we sum up to a witness `N` of `cellCount_eventually_zero`. -/
noncomputable def totalCells (cw : FiniteCWStructure X) : ℕ :=
  ∑ n ∈ Finset.range cw.cellCount_eventually_zero.choose, cw.cellCount n

/-- A trivial `FiniteCWStructure` with no cells in any dimension. Used
as a default for the `Inhabited` instance and as a sanity check that
the structure has a non-empty type. -/
def empty (X : Type) [TopologicalSpace X] : FiniteCWStructure X where
  cellCount := fun _ => 0
  cellCount_eventually_zero := ⟨0, fun _ _ => rfl⟩
  attachingMap := fun _ i => Fin.elim0 i
  characteristic := fun _ i => Fin.elim0 i

instance (X : Type) [TopologicalSpace X] : Inhabited (FiniteCWStructure X) :=
  ⟨empty X⟩

end FiniteCWStructure

end JacobianChallenge.Periods
