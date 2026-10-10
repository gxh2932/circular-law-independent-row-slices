import CircularLaw.BernoulliWalkVertexBounds
import CircularLaw.PairedTwoClosedWalks

/-!
# A shared vertex or entry connects two actual closed walks

Every visited vertex is reachable along its own successor orbit. If the
two walks share a vertex, their graph is connected. Equality of ordered
entries supplies such a shared vertex. Distinct entry labels therefore
bound the complete visited-vertex count by entries plus one, supplying
the dimension loss in Bernoulli covariance terms.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem closed_two_walk_graph_connected_of_shared_vertex {α β V : Type*}
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (b : α ⊕ β → Bool) (v : α ⊕ β → V)
    (hLeft : ∀ a c, ρ.SameCycle a c) (hRight : ∀ a c, τ.SameCycle a c)
    (hShared : ∃ a c, v (Sum.inl a) = v (Sum.inr c)) :
    (closedWalkVisitedGraph (Equiv.sumCongr ρ τ) b v).Connected := by
  obtain ⟨a, c, hShared⟩ := hShared
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨closedWalkVisitedVertex v (Sum.inl a), ?_⟩
  rintro ⟨w, p, rfl⟩
  cases p with
  | inl p =>
    exact closed_walk_visited_graph_same_cycle_reachable _ b v
      (sum_permutation_same_cycle_left ρ τ (hLeft a p))
  | inr p =>
    have hVertex : closedWalkVisitedVertex v (Sum.inl a) =
        closedWalkVisitedVertex v (Sum.inr c) := Subtype.ext hShared
    rw [hVertex]
    exact closed_walk_visited_graph_same_cycle_reachable _ b v
      (sum_permutation_same_cycle_right ρ τ (hRight c p))

theorem closed_two_walk_shared_entry_vertex {α β V : Type*}
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (b : α ⊕ β → Bool) (v : α ⊕ β → V)
    (a : α) (c : β)
    (hEntry : orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inl a) =
      orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inr c)) :
    ∃ a c, v (Sum.inl a) = v (Sum.inr c) := by
  cases hL : b (Sum.inl a) <;> cases hR : b (Sum.inr c)
  · exact ⟨a, c, congrArg Prod.fst (by simpa only [orientedClosedWalkEntry,
      hL, hR, Bool.false_eq_true, if_false] using hEntry)⟩
  · exact ⟨a, τ c, congrArg Prod.fst (by simpa only [orientedClosedWalkEntry,
      hL, hR, Bool.false_eq_true, if_false, if_true] using hEntry)⟩
  · exact ⟨ρ a, c, congrArg Prod.fst (by simpa only [orientedClosedWalkEntry,
      hL, hR, Bool.false_eq_true, if_false, if_true] using hEntry)⟩
  · exact ⟨ρ a, τ c, congrArg Prod.fst (by simpa only [orientedClosedWalkEntry,
      hL, hR, if_true] using hEntry)⟩

theorem closed_two_walk_graph_connected_of_shared_entry {α β V : Type*}
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (b : α ⊕ β → Bool) (v : α ⊕ β → V)
    (hLeft : ∀ a c, ρ.SameCycle a c) (hRight : ∀ a c, τ.SameCycle a c)
    (hShared : ∃ a c,
      orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inl a) =
        orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inr c)) :
    (closedWalkVisitedGraph (Equiv.sumCongr ρ τ) b v).Connected := by
  obtain ⟨a, c, hEntry⟩ := hShared
  exact closed_two_walk_graph_connected_of_shared_vertex ρ τ b v hLeft hRight
    (closed_two_walk_shared_entry_vertex ρ τ b v a c hEntry)

theorem closed_two_walk_shared_entry_vertex_bound {α β V : Type*}
    [Fintype α] [Fintype β] [Fintype V]
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (b : α ⊕ β → Bool) (v : α ⊕ β → V)
    (hLeft : ∀ a c, ρ.SameCycle a c) (hRight : ∀ a c, τ.SameCycle a c)
    (hShared : ∃ a c,
      orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inl a) =
        orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v (Sum.inr c)) :
    Nat.card (Set.range v) ≤
      Nat.card (Set.range (orientedClosedWalkEntry (Equiv.sumCongr ρ τ) b v)) + 1 := by
  simpa only [← Nat.card_eq_fintype_card] using
    finite_labeled_vertex_card_bound _ _
      (closed_two_walk_graph_connected_of_shared_entry ρ τ b v hLeft hRight hShared)

end CircularLaw
