import CircularLaw.FiniteLabeledTrees

/-!
# The two sides of a tree edge

Deleting a tree edge separates its endpoints. Reachability from its first
endpoint is constant across every other edge, so it provides the side
predicate used to analyze paired closed-walk excursions.
-/

noncomputable section
open Classical

namespace CircularLaw

def treeEdgeSide {V : Type*} (G : SimpleGraph V) (u v w : V) : Prop :=
  (G.deleteEdges {Sym2.mk (u, v)}).Reachable u w

theorem tree_edge_side_start {V : Type*} (G : SimpleGraph V) (u v : V) :
    treeEdgeSide G u v u := SimpleGraph.Reachable.rfl

theorem tree_edge_side_not_end {V : Type*} (G : SimpleGraph V) {u v : V}
    (hBridge : G.IsBridge (Sym2.mk (u, v))) : ¬treeEdgeSide G u v v :=
  (SimpleGraph.isBridge_iff.mp hBridge).2

theorem tree_edge_is_bridge {V : Type*} (G : SimpleGraph V) (hTree : G.IsTree)
    {u v : V} (hAdj : G.Adj u v) : G.IsBridge (Sym2.mk (u, v)) :=
  SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hTree.IsAcyclic hAdj

theorem tree_edge_side_of_deleted_reachable {V : Type*} (G : SimpleGraph V)
    (u v : V) {x y : V}
    (h : (G.deleteEdges {Sym2.mk (u, v)}).Reachable x y) :
    treeEdgeSide G u v x ↔ treeEdgeSide G u v y :=
  ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩

theorem tree_edge_side_of_other_adj {V : Type*} (G : SimpleGraph V)
    (u v : V) {x y : V} (hAdj : G.Adj x y)
    (hOther : Sym2.mk (x, y) ≠ Sym2.mk (u, v)) :
    treeEdgeSide G u v x ↔ treeEdgeSide G u v y := by
  apply tree_edge_side_of_deleted_reachable
  exact (SimpleGraph.deleteEdges_adj.mpr
    ⟨hAdj, by simpa only [Set.mem_singleton_iff] using hOther⟩).reachable

end CircularLaw
