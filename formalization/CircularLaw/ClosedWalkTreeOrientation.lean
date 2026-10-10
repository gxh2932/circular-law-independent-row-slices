import CircularLaw.BernoulliWalkVertexBounds
import CircularLaw.TreeEdgeCuts

/-!
# A maximal closed-walk pattern traverses each entry in both directions

Maximal vertex count makes the visited graph a tree with distinct
unordered entry labels. Deleting one edge gives a side predicate.
A finite permutation cannot move that predicate in only one direction.
Thus the same ordered entry occurs at a position with the opposite
direct/adjoint flag. This supplies the compatibility needed to identify
Bernoulli leading patterns with complex Gaussian matchings.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem finite_permutation_predicate_invariant_of_imp {α : Type*} [Finite α]
    (ρ : Equiv.Perm α) (P : α → Prop) (h : ∀ a, P (ρ a) → P a) :
    ∀ a, P (ρ a) ↔ P a := by
  let f : {a // P (ρ a)} → {a // P a} := fun a => ⟨a.val, h a.val a.property⟩
  have hInj : Function.Injective f := by
    intro a c he
    apply Subtype.ext
    exact congrArg (fun z : {a // P a} => z.val) he
  have hCard : Nat.card {a // P (ρ a)} = Nat.card {a // P a} :=
    Nat.card_congr (Equiv.subtypeEquivOfSubtype ρ)
  have hSurj := (hInj.bijective_of_nat_card_le hCard.ge).2
  intro a
  refine ⟨h a, ?_⟩
  intro ha
  obtain ⟨c, hc⟩ := hSurj ⟨a, ha⟩
  have hVal : c.val = a := congrArg Subtype.val hc
  exact hVal ▸ c.property

theorem closed_walk_entry_edge_eq_position_edge {α V : Type*}
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V) (a : α) :
    Sym2.mk (closedWalkEntryFirst ρ b v ⟨orientedClosedWalkEntry ρ b v a, ⟨a, rfl⟩⟩,
      closedWalkEntrySecond ρ b v ⟨orientedClosedWalkEntry ρ b v a, ⟨a, rfl⟩⟩) =
      Sym2.mk (closedWalkVisitedVertex v a, closedWalkVisitedVertex v (ρ a)) := by
  cases h : b a
  · simp [closedWalkEntryFirst, closedWalkEntrySecond, closedWalkVisitedVertex,
      orientedClosedWalkEntry, h]
  · simp [closedWalkEntryFirst, closedWalkEntrySecond, closedWalkVisitedVertex,
      orientedClosedWalkEntry, h]

theorem closed_walk_maximal_entry_eq_of_position_edge_eq {α V : Type*}
    [Fintype α] [Fintype V] [Nonempty α]
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hMax : Nat.card (Set.range v) =
      Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1) {a c : α}
    (hEdge : Sym2.mk (closedWalkVisitedVertex v a, closedWalkVisitedVertex v (ρ a)) =
      Sym2.mk (closedWalkVisitedVertex v c, closedWalkVisitedVertex v (ρ c))) :
    orientedClosedWalkEntry ρ b v a = orientedClosedWalkEntry ρ b v c := by
  let ea : Set.range (orientedClosedWalkEntry ρ b v) :=
    ⟨orientedClosedWalkEntry ρ b v a, ⟨a, rfl⟩⟩
  let ec : Set.range (orientedClosedWalkEntry ρ b v) :=
    ⟨orientedClosedWalkEntry ρ b v c, ⟨c, rfl⟩⟩
  have hLabels : ea = ec := finite_labeled_maximal_vertex_label_eq_of_edge_eq
    (closedWalkEntryFirst ρ b v) (closedWalkEntrySecond ρ b v)
    (closed_walk_visited_graph_connected ρ b v hOrbit)
    (by simpa only [Nat.card_eq_fintype_card] using hMax)
    ((closed_walk_entry_edge_eq_position_edge ρ b v a).trans
      (hEdge.trans (closed_walk_entry_edge_eq_position_edge ρ b v c).symm))
  exact congrArg Subtype.val hLabels

theorem closed_walk_maximal_position_adj {α V : Type*}
    [Fintype α] [Fintype V] [Nonempty α]
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hMax : Nat.card (Set.range v) =
      Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1) (a : α) :
    (closedWalkVisitedGraph ρ b v).Adj (closedWalkVisitedVertex v a)
      (closedWalkVisitedVertex v (ρ a)) := by
  let e : Set.range (orientedClosedWalkEntry ρ b v) :=
    ⟨orientedClosedWalkEntry ρ b v a, ⟨a, rfl⟩⟩
  have hNoLoop := closed_walk_maximal_vertices_nonloop ρ b v hOrbit hMax e
  cases h : b a
  · simp only [e, orientedClosedWalkEntry, h, Bool.false_eq_true, if_false] at hNoLoop
    refine ⟨?_, e, Or.inl ⟨?_, ?_⟩⟩
    · exact fun he => hNoLoop (congrArg Subtype.val he)
    · simp [closedWalkEntryFirst, closedWalkVisitedVertex, e, orientedClosedWalkEntry, h]
    · simp [closedWalkEntrySecond, closedWalkVisitedVertex, e, orientedClosedWalkEntry, h]
  · simp only [e, orientedClosedWalkEntry, h, if_true] at hNoLoop
    refine ⟨?_, e, Or.inr ⟨?_, ?_⟩⟩
    · exact fun he => hNoLoop (congrArg Subtype.val he.symm)
    · simp [closedWalkEntryFirst, closedWalkVisitedVertex, e, orientedClosedWalkEntry, h]
    · simp [closedWalkEntrySecond, closedWalkVisitedVertex, e, orientedClosedWalkEntry, h]

theorem closed_walk_maximal_opposite_entry {α V : Type*}
    [Fintype α] [Fintype V] [Nonempty α]
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hMax : Nat.card (Set.range v) =
      Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1) (a : α) :
    ∃ c, orientedClosedWalkEntry ρ b v c = orientedClosedWalkEntry ρ b v a ∧ b c ≠ b a := by
  by_contra hNot
  push_neg at hNot
  let G := closedWalkVisitedGraph ρ b v
  let u := closedWalkVisitedVertex v a
  let w := closedWalkVisitedVertex v (ρ a)
  let P : α → Prop := fun c => treeEdgeSide G u w (closedWalkVisitedVertex v c)
  have hStart : P a := tree_edge_side_start G u w
  have hEnd : ¬P (ρ a) := tree_edge_side_not_end G
    (tree_edge_is_bridge G (closed_walk_maximal_vertices_tree ρ b v hOrbit hMax)
      (closed_walk_maximal_position_adj ρ b v hOrbit hMax a))
  have hStep : ∀ c, P (ρ c) → P c := by
    intro c hc
    by_cases he : orientedClosedWalkEntry ρ b v c = orientedClosedWalkEntry ρ b v a
    · have hb := hNot c he
      have hVertex : v c = v a := by
        cases ha : b a
        · simpa [orientedClosedWalkEntry, ha, hb] using congrArg Prod.fst he
        · simpa [orientedClosedWalkEntry, ha, hb] using congrArg Prod.snd he
      change treeEdgeSide G u w (closedWalkVisitedVertex v c)
      have hV : closedWalkVisitedVertex v c = u := Subtype.ext hVertex
      rw [hV]
      exact hStart
    · have hOther : Sym2.mk (closedWalkVisitedVertex v c, closedWalkVisitedVertex v (ρ c)) ≠
          Sym2.mk (u, w) := fun hEdge => he
        (closed_walk_maximal_entry_eq_of_position_edge_eq ρ b v hOrbit hMax hEdge)
      exact (tree_edge_side_of_other_adj G u w
        (closed_walk_maximal_position_adj ρ b v hOrbit hMax c) hOther).mpr hc
  exact hEnd ((finite_permutation_predicate_invariant_of_imp ρ P hStep a).mpr hStart)

end CircularLaw
