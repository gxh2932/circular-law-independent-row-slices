import CircularLaw.FiniteIncidenceGraph

/-!
# Finite graphs supplied by labeled pairs of endpoints

Unlike the bipartite incidence graph, endpoints may belong to the same
type and a label may give a loop. Loops supply no simple-graph edge;
repeated pairs also supply only one edge. A connected graph still has
at most one more vertex than labels.
-/

noncomputable section
open Classical

namespace CircularLaw

def finiteLabeledGraph {α V : Type*} (p q : α → V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ a, (p a = v ∧ q a = w) ∨ (p a = w ∧ q a = v)
  symm := by
    rintro v w ⟨h, a, ha⟩
    exact ⟨h.symm, a, ha.symm⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

def finiteLabeledEdge {α V : Type*} (p q : α → V) (a : {a // p a ≠ q a}) :
    (finiteLabeledGraph p q).edgeSet :=
  ⟨Sym2.mk (p a, q a), a.property, a, Or.inl ⟨rfl, rfl⟩⟩

theorem finite_labeled_edge_surjective {α V : Type*} (p q : α → V) :
    Function.Surjective (finiteLabeledEdge p q) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf v w =>
    obtain ⟨hne, a, ha⟩ := he
    rcases ha with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · refine ⟨⟨a, by simpa only [hp, hq] using hne⟩, Subtype.ext ?_⟩
      change Sym2.mk (p a, q a) = Sym2.mk (v, w)
      rw [hp, hq]
    · refine ⟨⟨a, by simpa only [hp, hq] using hne.symm⟩, Subtype.ext ?_⟩
      change Sym2.mk (p a, q a) = Sym2.mk (v, w)
      rw [hp, hq]
      exact Sym2.eq_swap

theorem finite_labeled_edge_card_le {α V : Type*} [Finite α] (p q : α → V) :
    Nat.card (finiteLabeledGraph p q).edgeSet ≤ Nat.card α := by
  exact (Nat.card_le_card_of_surjective _ (finite_labeled_edge_surjective p q)).trans
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

theorem finite_labeled_endpoints_reachable {α V : Type*} (p q : α → V) (a : α) :
    (finiteLabeledGraph p q).Reachable (p a) (q a) := by
  by_cases h : p a = q a
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, a, Or.inl ⟨rfl, rfl⟩⟩

theorem finite_labeled_vertex_card_bound {α V : Type*} [Fintype α] [Fintype V]
    (p q : α → V) (h : (finiteLabeledGraph p q).Connected) :
    Fintype.card V ≤ Fintype.card α + 1 := by
  have hV := h.card_vert_le_card_edgeSet_add_one
  have hE := finite_labeled_edge_card_le p q
  simpa only [Nat.card_eq_fintype_card] using
    hV.trans (Nat.add_le_add_right hE 1)

end CircularLaw
