import CircularLaw.TreeEdgeCuts

/-!
# Edge-separating vertex predicates force a labeled tree

For each label a vertex predicate separates its endpoints and is constant
across all other labels. Each edge is therefore a bridge, loops and
repeated edges are excluded, and a connected endpoint graph is a tree
with exactly one more vertex than labels.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem graph_predicate_constant_of_reachable {V : Type*} (G : SimpleGraph V)
    (F : V → Prop) (hAdj : ∀ x y, G.Adj x y → (F x ↔ F y)) {u v : V}
    (hReach : G.Reachable u v) : F u ↔ F v := by
  obtain ⟨w⟩ := hReach
  induction w with
  | nil => rfl
  | cons h _ ih => exact (hAdj _ _ h).trans ih

theorem finite_labeled_separator_nonloop {α V : Type*} (p q : α → V) (F : α → V → Prop)
    (hStart : ∀ a, F a (p a)) (hEnd : ∀ a, ¬F a (q a)) (a : α) : p a ≠ q a := by
  intro h
  exact hEnd a (h ▸ hStart a)

theorem finite_labeled_separator_bridge {α V : Type*} (p q : α → V) (F : α → V → Prop)
    (hStart : ∀ a, F a (p a)) (hEnd : ∀ a, ¬F a (q a))
    (hOther : ∀ a c, c ≠ a → (F a (p c) ↔ F a (q c))) (a : α) :
    (finiteLabeledGraph p q).IsBridge (Sym2.mk (p a, q a)) := by
  apply SimpleGraph.isBridge_iff.mpr
  refine ⟨⟨finite_labeled_separator_nonloop p q F hStart hEnd a, a, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
  intro hReach
  have hConst : ∀ x y, ((finiteLabeledGraph p q).deleteEdges {Sym2.mk (p a, q a)}).Adj x y →
      (F a x ↔ F a y) := by
    intro x y hAdj
    obtain ⟨hLabelAdj, hNotEdge⟩ := SimpleGraph.deleteEdges_adj.mp hAdj
    obtain ⟨_, c, hLabel⟩ := hLabelAdj
    have hEdgeC : Sym2.mk (p c, q c) = Sym2.mk (x, y) := by
      rcases hLabel with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · rw [hp, hq]
      · rw [hp, hq]
        exact Sym2.eq_swap
    have hca : c ≠ a := by
      intro hca
      apply hNotEdge
      simp only [Set.mem_singleton_iff]
      exact hEdgeC.symm.trans (congrArg (fun c => Sym2.mk (p c, q c)) hca)
    rcases hLabel with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [← hp, ← hq]
      exact hOther a c hca
    · rw [← hq, ← hp]
      exact (hOther a c hca).symm
  exact hEnd a ((graph_predicate_constant_of_reachable _ (F a) hConst hReach).mp (hStart a))

theorem finite_labeled_separator_tree {α V : Type*} (p q : α → V) (F : α → V → Prop)
    (hStart : ∀ a, F a (p a)) (hEnd : ∀ a, ¬F a (q a))
    (hOther : ∀ a c, c ≠ a → (F a (p c) ↔ F a (q c)))
    (hConnected : (finiteLabeledGraph p q).Connected) : (finiteLabeledGraph p q).IsTree := by
  refine ⟨hConnected, SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr ?_⟩
  intro x y hAdj
  obtain ⟨_, a, hLabel⟩ := hAdj
  have hEdge : Sym2.mk (p a, q a) = Sym2.mk (x, y) := by
    rcases hLabel with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [hp, hq]
    · rw [hp, hq]
      exact Sym2.eq_swap
  rw [← hEdge]
  exact finite_labeled_separator_bridge p q F hStart hEnd hOther a

theorem finite_labeled_separator_edge_injective {α V : Type*} (p q : α → V)
    (F : α → V → Prop) (hStart : ∀ a, F a (p a)) (hEnd : ∀ a, ¬F a (q a))
    (hOther : ∀ a c, c ≠ a → (F a (p c) ↔ F a (q c)))
    (hNoLoops : ∀ a, p a ≠ q a) :
    Function.Injective (finiteLabeledTotalEdge p q hNoLoops) := by
  intro a c hEdge
  by_contra hac
  have hca : c ≠ a := fun h => hac h.symm
  have hSame := hOther a c hca
  have hPair : Sym2.mk (p a, q a) = Sym2.mk (p c, q c) := congrArg Subtype.val hEdge
  rcases Sym2.eq_iff.mp hPair with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [← hp, ← hq] at hSame
    exact hEnd a (hSame.mp (hStart a))
  · rw [← hq, ← hp] at hSame
    exact hEnd a (hSame.mpr (hStart a))

theorem finite_labeled_separator_vertex_card {α V : Type*} [Fintype α] [Fintype V]
    (p q : α → V) (F : α → V → Prop) (hStart : ∀ a, F a (p a)) (hEnd : ∀ a, ¬F a (q a))
    (hOther : ∀ a c, c ≠ a → (F a (p c) ↔ F a (q c)))
    (hConnected : (finiteLabeledGraph p q).Connected) :
    Fintype.card V = Fintype.card α + 1 := by
  apply (finite_labeled_maximal_vertex_iff_tree_labels p q hConnected).mpr
  let hNoLoops := finite_labeled_separator_nonloop p q F hStart hEnd
  exact ⟨hNoLoops, finite_labeled_separator_tree p q F hStart hEnd hOther hConnected,
    finite_labeled_separator_edge_injective p q F hStart hEnd hOther hNoLoops,
    finite_labeled_total_edge_surjective p q hNoLoops⟩

end CircularLaw
