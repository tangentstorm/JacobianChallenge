import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic

/-!
# Stage A — Spanning trees on finite connected graphs

Bottom-up sketch (Stage A2.a, sub-leaf): every finite connected
graph admits a spanning tree. The dual-graph of a triangulation is
finite and connected (when `M` is), so this directly produces the
spanning tree used in the cut-and-unfold step.

Mathlib v4.28.0 has `SimpleGraph`, `IsAcyclic`, `IsTree`, and partial
spanning-subgraph machinery; the existence theorem at the level
needed here is not packaged.

Estimated LOC for a full implementation: ~250.
-/

namespace JacobianChallenge.StageA

variable {V : Type*} (G : SimpleGraph V)

/-- A *spanning subgraph* of `G`: a subgraph whose vertex set is all
of `V`. -/
def IsSpanning (H : SimpleGraph V) : Prop :=
  H ≤ G

/-- A *spanning tree* of `G`: a spanning subgraph that is a tree. -/
def IsSpanningTree (H : SimpleGraph V) : Prop :=
  IsSpanning G H ∧ H.IsTree

/-! ### Existence -/

/-- **Spanning-tree existence (finite, connected).** Every finite
connected `SimpleGraph` admits a spanning tree.

Bottom-up content: greedy construction by edge-count induction.
Take a spanning subgraph; if it has a cycle, remove one of its
edges (still spanning, still connected since the cycle gave a
redundant path). Iterate until acyclic. -/
theorem exists_spanningTree_of_finite_connected
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (_hConn : G.Connected) :
    ∃ H : SimpleGraph V, IsSpanningTree G H := sorry

/-- The *complement of a spanning tree*: edges of `G` not in `T`. -/
def cotreeEdges (T : SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ e ∉ T.edgeSet}

/-- Edge count formula: `|E(G)| = (|V| - 1) + |cotreeEdges|`. -/
theorem edge_count_eq_vertex_count_sub_one_add_cotree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {T : SimpleGraph V} (_hT : IsSpanningTree G T) :
    True := sorry

/-! ### Properties -/

/-- A tree has a unique path between any two vertices. -/
theorem tree_unique_path {T : SimpleGraph V} (_hT : T.IsTree)
    (u v : V) : True := sorry

/-- Removing any edge from a tree disconnects it. -/
theorem tree_edge_removal_disconnects
    {T : SimpleGraph V} (_hT : T.IsTree) (e : Sym2 V)
    (_he : e ∈ T.edgeSet) : True := sorry

/-- Adding an edge `e` (with endpoints in `T`) creates exactly one
cycle, namely the path-in-T plus `e`. -/
theorem tree_edge_addition_creates_unique_cycle
    {T : SimpleGraph V} (_hT : T.IsTree) (_e : Sym2 V) :
    True := sorry

/-! ### DFS / BFS construction -/

/-- A *depth-first search* tree from a root vertex. Implementable as
a recursive procedure on `Fintype V`; produces a spanning tree
when `G` is connected. -/
noncomputable def dfsTree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (_root : V) : SimpleGraph V := sorry

/-- The DFS tree is a spanning tree. -/
theorem dfsTree_isSpanningTree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (_hConn : G.Connected) :
    IsSpanningTree G (dfsTree G root) := sorry

/-! ### TOPDOWN drill — sub-leaves -/

/-- **Round 1.** *Sub-leaf of `exists_spanningTree_of_finite_connected`.*
For a connected graph, the *full subgraph on any vertex* is a connected
1-vertex starting tree. -/
theorem singleton_subgraph_is_tree
    [Fintype V] [DecidableEq V] (_v : V) : True := sorry

/-- **Round 1.** *Sub-leaf:* extending a tree by adding any *boundary
edge* (one endpoint in tree, one outside) produces a strictly larger
tree. -/
theorem tree_extend_by_boundary_edge
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (T : SimpleGraph V) (_hT : T.IsTree) : True := sorry

/-- **Round 1.** *Sub-leaf:* the extension procedure terminates when
all of `V` is included. -/
theorem tree_extend_terminates_at_spanning
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : True := sorry

/-- **Round 2.** *Sub-leaf of `tree_unique_path`.* In a tree, any walk
between two vertices reduces to a unique simple path. -/
theorem tree_walk_reduces_to_simple_path
    {T : SimpleGraph V} (_hT : T.IsTree) (_u _v : V) : True := sorry

/-- **Round 2.** *Sub-leaf:* two simple paths between the same
endpoints in a tree must coincide. -/
theorem tree_simple_paths_unique
    {T : SimpleGraph V} (_hT : T.IsTree) (_u _v : V) : True := sorry

/-- **Round 3.** *Sub-leaf of `tree_edge_removal_disconnects`.* Removing
an edge `e = {u, v}` from a tree creates two components. -/
theorem tree_minus_edge_two_components
    {T : SimpleGraph V} (_hT : T.IsTree) (e : Sym2 V)
    (_he : e ∈ T.edgeSet) : True := sorry

/-- **Round 3.** *Sub-leaf:* the components are characterised by
"reachable from `u`" vs "reachable from `v`" after edge removal. -/
theorem tree_minus_edge_components_characterisation
    {T : SimpleGraph V} (_hT : T.IsTree) (_e : Sym2 V) : True := sorry

/-- **Round 4.** *Sub-leaf of `tree_edge_addition_creates_unique_cycle`.*
Adding an edge between two vertices already connected by a unique
tree path creates a cycle = (tree path) ∪ (new edge). -/
theorem tree_plus_edge_creates_cycle
    {T : SimpleGraph V} (_hT : T.IsTree) : True := sorry

/-- **Round 4.** *Sub-leaf:* the resulting cycle is unique (since the
tree path is unique). -/
theorem tree_plus_edge_cycle_unique
    {T : SimpleGraph V} (_hT : T.IsTree) : True := sorry

/-- **Round 5.** *Sub-leaf of `edge_count_eq_vertex_count_sub_one_add_cotree`.*
A tree on `n` vertices has exactly `n - 1` edges. -/
theorem tree_edge_count
    [Fintype V] {T : SimpleGraph V}
    [DecidableRel T.Adj]
    (_hT : T.IsTree) : True := sorry

/-- **Round 5.** *Sub-leaf:* edges of `G` partition into "in-tree" and
"out-of-tree". -/
theorem edge_partition_tree_cotree
    {T : SimpleGraph V} (_hT : IsSpanningTree G T) : True := sorry

end JacobianChallenge.StageA
