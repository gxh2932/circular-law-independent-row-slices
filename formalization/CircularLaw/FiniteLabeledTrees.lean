import CircularLaw.FiniteLabeledGraph

/-!
# Maximal vertex counts force distinct nonloop labels and a tree

The endpoint graph may initially have loops or repeated unordered edges.
If its connected vertex count is `labels + 1`, both losses disappear:
every label is a nonloop, the labels biject with the actual edges, and
the graph is a tree. This applies to nonalternating paired walks.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem finite_labeled_maximal_vertex_edge_card {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1) :
    Nat.card (finiteLabeledGraph p q).edgeSet = Nat.card α := by
  have hV := h.card_vert_le_card_edgeSet_add_one
  have hE := finite_labeled_edge_card_le p q
  simp only [Nat.card_eq_fintype_card] at hV hE ⊢
  rw [hMax] at hV
  omega

theorem finite_labeled_maximal_vertex_nonloop_card {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1) :
    Nat.card {a // p a ≠ q a} = Nat.card α := by
  have hE := finite_labeled_maximal_vertex_edge_card p q h hMax
  have hLower := Nat.card_le_card_of_surjective _ (finite_labeled_edge_surjective p q)
  have hUpper := Nat.card_le_card_of_injective
    (Subtype.val : {a // p a ≠ q a} → α) Subtype.val_injective
  omega

theorem finite_labeled_maximal_vertex_nonloop {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1) (a : α) : p a ≠ q a := by
  have hCard := finite_labeled_maximal_vertex_nonloop_card p q h hMax
  have hSurj := (Subtype.val_injective : Function.Injective
    (Subtype.val : {a // p a ≠ q a} → α)).bijective_of_nat_card_le hCard.ge
  obtain ⟨b, hb⟩ := hSurj.2 a
  simpa only [hb] using b.property

theorem finite_labeled_maximal_vertex_tree {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1) :
    (finiteLabeledGraph p q).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨h, ?_⟩
  rw [finite_labeled_maximal_vertex_edge_card p q h hMax]
  simpa only [Nat.card_eq_fintype_card] using hMax.symm

def finiteLabeledTotalEdge {α V : Type*} (p q : α → V)
    (hNoLoops : ∀ a, p a ≠ q a) (a : α) : (finiteLabeledGraph p q).edgeSet :=
  finiteLabeledEdge p q ⟨a, hNoLoops a⟩

theorem finite_labeled_total_edge_surjective {α V : Type*} (p q : α → V)
    (hNoLoops : ∀ a, p a ≠ q a) : Function.Surjective (finiteLabeledTotalEdge p q hNoLoops) := by
  intro e
  obtain ⟨a, ha⟩ := finite_labeled_edge_surjective p q e
  exact ⟨a.val, ha⟩

theorem finite_labeled_maximal_vertex_label_bijective {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1)
    (hNoLoops : ∀ a, p a ≠ q a) :
    Function.Bijective (finiteLabeledTotalEdge p q hNoLoops) :=
  (finite_labeled_total_edge_surjective p q hNoLoops).bijective_of_nat_card_le
    (finite_labeled_maximal_vertex_edge_card p q h hMax).ge

theorem finite_labeled_maximal_vertex_label_eq_of_edge_eq {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected)
    (hMax : Fintype.card V = Fintype.card α + 1) {a b : α}
    (hEdge : Sym2.mk (p a, q a) = Sym2.mk (p b, q b)) : a = b := by
  let hNoLoops := finite_labeled_maximal_vertex_nonloop p q h hMax
  apply (finite_labeled_maximal_vertex_label_bijective p q h hMax hNoLoops).1
  exact Subtype.ext hEdge

theorem finite_labeled_maximal_vertex_iff_tree_labels {α V : Type*}
    [Fintype α] [Fintype V] (p q : α → V)
    (h : (finiteLabeledGraph p q).Connected) :
    Fintype.card V = Fintype.card α + 1 ↔
      ∃ hNoLoops : ∀ a, p a ≠ q a,
        (finiteLabeledGraph p q).IsTree ∧
          Function.Bijective (finiteLabeledTotalEdge p q hNoLoops) := by
  constructor
  · intro hMax
    let hNoLoops := finite_labeled_maximal_vertex_nonloop p q h hMax
    exact ⟨hNoLoops, finite_labeled_maximal_vertex_tree p q h hMax,
      finite_labeled_maximal_vertex_label_bijective p q h hMax hNoLoops⟩
  · rintro ⟨hNoLoops, hTree, hLabels⟩
    have hCard := (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
    have hEdge := Nat.card_eq_of_bijective _ hLabels
    rw [← hEdge] at hCard
    simpa only [Nat.card_eq_fintype_card] using hCard.symm

end CircularLaw
