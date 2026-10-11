import CircularLaw.PermutationCycleColorings
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Finite incidence graphs with edges supplied by actual labels

Two maps from the label type give a bipartite graph. Every graph edge
comes from a label, even when several labels give the same edge. A
connected incidence graph therefore has at most `labels+1` vertices.
-/

noncomputable section
open Classical

namespace CircularLaw

def finiteIncidenceGraph {α P Q : Type*} (p : α → P) (q : α → Q) :
    SimpleGraph (P ⊕ Q) where
  Adj v w := match v, w with
    | Sum.inl b, Sum.inr c => ∃ a, p a = b ∧ q a = c
    | Sum.inr c, Sum.inl b => ∃ a, p a = b ∧ q a = c
    | _, _ => False
  symm := by
    intro v w h
    cases v <;> cases w <;> exact h
  loopless := by
    constructor
    intro v
    cases v <;> exact not_false

theorem finite_incidence_graph_adj {α P Q : Type*} (p : α → P) (q : α → Q) (a : α) :
    (finiteIncidenceGraph p q).Adj (Sum.inl (p a)) (Sum.inr (q a)) :=
  ⟨a, rfl, rfl⟩

def finiteIncidenceEdge {α P Q : Type*} (p : α → P) (q : α → Q) (a : α) :
    (finiteIncidenceGraph p q).edgeSet :=
  ⟨Sym2.mk (Sum.inl (p a), Sum.inr (q a)), finite_incidence_graph_adj p q a⟩

theorem finite_incidence_edge_surjective {α P Q : Type*} (p : α → P) (q : α → Q) :
    Function.Surjective (finiteIncidenceEdge p q) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf v w =>
    cases v with
    | inl b =>
      cases w with
      | inl b' => exact False.elim he
      | inr c =>
        obtain ⟨a, hp, hq⟩ := he
        refine ⟨a, Subtype.ext ?_⟩
        change Sym2.mk (Sum.inl (p a), Sum.inr (q a)) = Sym2.mk (Sum.inl b, Sum.inr c)
        rw [hp, hq]
    | inr c =>
      cases w with
      | inl b =>
        obtain ⟨a, hp, hq⟩ := he
        refine ⟨a, Subtype.ext ?_⟩
        change Sym2.mk (Sum.inl (p a), Sum.inr (q a)) = Sym2.mk (Sum.inr c, Sum.inl b)
        rw [hp, hq]
        exact Sym2.eq_swap
      | inr c' => exact False.elim he

theorem finite_incidence_edge_card_le {α P Q : Type*} [Finite α]
    (p : α → P) (q : α → Q) :
    Nat.card (finiteIncidenceGraph p q).edgeSet ≤ Nat.card α :=
  Nat.card_le_card_of_surjective _ (finite_incidence_edge_surjective p q)

theorem finite_incidence_vertex_card_bound {α P Q : Type*}
    [Fintype α] [Fintype P] [Fintype Q] (p : α → P) (q : α → Q)
    (h : (finiteIncidenceGraph p q).Connected) :
    Fintype.card P + Fintype.card Q ≤ Fintype.card α + 1 := by
  have hV := h.card_vert_le_card_edgeSet_add_one
  have hE := finite_incidence_edge_card_le p q
  have hBound := hV.trans (Nat.add_le_add_right hE 1)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using hBound

theorem finite_incidence_maximal_vertex_edge_card {α P Q : Type*}
    [Fintype α] [Fintype P] [Fintype Q] (p : α → P) (q : α → Q)
    (h : (finiteIncidenceGraph p q).Connected)
    (hMax : Fintype.card P + Fintype.card Q = Fintype.card α + 1) :
    Nat.card (finiteIncidenceGraph p q).edgeSet = Nat.card α := by
  have hV := h.card_vert_le_card_edgeSet_add_one
  have hE := finite_incidence_edge_card_le p q
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum] at hV hE ⊢
  rw [hMax] at hV
  omega

theorem finite_incidence_maximal_vertex_tree {α P Q : Type*}
    [Fintype α] [Fintype P] [Fintype Q] (p : α → P) (q : α → Q)
    (h : (finiteIncidenceGraph p q).Connected)
    (hMax : Fintype.card P + Fintype.card Q = Fintype.card α + 1) :
    (finiteIncidenceGraph p q).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨h, ?_⟩
  rw [finite_incidence_maximal_vertex_edge_card p q h hMax]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using hMax.symm

theorem finite_incidence_maximal_vertex_edge_bijective {α P Q : Type*}
    [Fintype α] [Fintype P] [Fintype Q] (p : α → P) (q : α → Q)
    (h : (finiteIncidenceGraph p q).Connected)
    (hMax : Fintype.card P + Fintype.card Q = Fintype.card α + 1) :
    Function.Bijective (finiteIncidenceEdge p q) :=
  (finite_incidence_edge_surjective p q).bijective_of_nat_card_le
    (finite_incidence_maximal_vertex_edge_card p q h hMax).ge

end CircularLaw
