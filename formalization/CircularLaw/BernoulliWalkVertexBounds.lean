import CircularLaw.BernoulliMatrixWordMeans
import CircularLaw.FiniteLabeledTrees
import CircularLaw.GaussianMomentCycleBound

/-!
# Free vertices in actual Bernoulli closed walks

Distinct ordered entries label a graph on the visited vertices. The
closed walk makes this graph connected, including loops and repeated
entries. Thus the number of visited vertices is at most one more than
the number of distinct entries. Equality forces a tree and distinct
nonloop unordered edges. Together with singleton cancellation, this
is the dimension bound needed by the sparse moment enumeration.
-/

noncomputable section
open Classical

namespace CircularLaw

local instance bernoulliWalkVertexBEq (n : ℕ) : BEq (Fin n × Fin n) := instBEqOfDecidableEq

def orientedClosedWalkEntry {α V : Type*} (ρ : Equiv.Perm α)
    (b : α → Bool) (v : α → V) (a : α) : V × V :=
  if b a then (v (ρ a), v a) else (v a, v (ρ a))

def closedWalkVisitedVertex {α V : Type*} (v : α → V) (a : α) : Set.range v :=
  ⟨v a, ⟨a, rfl⟩⟩

def closedWalkEntryFirst {α V : Type*} (ρ : Equiv.Perm α)
    (b : α → Bool) (v : α → V) (e : Set.range (orientedClosedWalkEntry ρ b v)) :
    Set.range v :=
  ⟨e.val.1, by
    obtain ⟨a, ha⟩ := e.property
    rw [← ha]
    cases h : b a
    · exact ⟨a, by simp [orientedClosedWalkEntry, h]⟩
    · exact ⟨ρ a, by simp [orientedClosedWalkEntry, h]⟩⟩

def closedWalkEntrySecond {α V : Type*} (ρ : Equiv.Perm α)
    (b : α → Bool) (v : α → V) (e : Set.range (orientedClosedWalkEntry ρ b v)) :
    Set.range v :=
  ⟨e.val.2, by
    obtain ⟨a, ha⟩ := e.property
    rw [← ha]
    cases h : b a
    · exact ⟨ρ a, by simp [orientedClosedWalkEntry, h]⟩
    · exact ⟨a, by simp [orientedClosedWalkEntry, h]⟩⟩

def closedWalkVisitedGraph {α V : Type*} (ρ : Equiv.Perm α)
    (b : α → Bool) (v : α → V) : SimpleGraph (Set.range v) :=
  finiteLabeledGraph (closedWalkEntryFirst ρ b v) (closedWalkEntrySecond ρ b v)

theorem closed_walk_visited_graph_successor_reachable {α V : Type*}
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V) (a : α) :
    (closedWalkVisitedGraph ρ b v).Reachable (closedWalkVisitedVertex v a)
      (closedWalkVisitedVertex v (ρ a)) := by
  let e : Set.range (orientedClosedWalkEntry ρ b v) :=
    ⟨orientedClosedWalkEntry ρ b v a, ⟨a, rfl⟩⟩
  have hEdge := finite_labeled_endpoints_reachable
    (closedWalkEntryFirst ρ b v) (closedWalkEntrySecond ρ b v) e
  cases h : b a
  · simpa [closedWalkVisitedGraph, closedWalkEntryFirst, closedWalkEntrySecond,
      closedWalkVisitedVertex, e, orientedClosedWalkEntry, h] using hEdge
  · simpa [closedWalkVisitedGraph, closedWalkEntryFirst, closedWalkEntrySecond,
      closedWalkVisitedVertex, e, orientedClosedWalkEntry, h] using hEdge.symm

theorem closed_walk_visited_graph_same_cycle_reachable {α V : Type*}
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V) {a c : α}
    (hCycle : ρ.SameCycle a c) :
    (closedWalkVisitedGraph ρ b v).Reachable (closedWalkVisitedVertex v a)
      (closedWalkVisitedVertex v c) := by
  have hPow (m : ℤ) (x : α) :
      (closedWalkVisitedGraph ρ b v).Reachable (closedWalkVisitedVertex v x)
        (closedWalkVisitedVertex v ((ρ ^ m) x)) := by
    induction m using Int.induction_on generalizing x with
    | zero => simp
    | succ m ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply]
      exact (closed_walk_visited_graph_successor_reachable ρ b v x).trans (ih (ρ x))
    | pred m ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply]
      have hBack : (closedWalkVisitedGraph ρ b v).Reachable (closedWalkVisitedVertex v x)
          (closedWalkVisitedVertex v (ρ⁻¹ x)) := by
        simpa using (closed_walk_visited_graph_successor_reachable ρ b v (ρ.symm x)).symm
      exact hBack.trans (ih (ρ⁻¹ x))
  obtain ⟨m, rfl⟩ := hCycle
  exact hPow m a

theorem closed_walk_visited_graph_connected {α V : Type*} [Nonempty α]
    (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c) : (closedWalkVisitedGraph ρ b v).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨a₀⟩ := ‹Nonempty α›
  refine ⟨closedWalkVisitedVertex v a₀, ?_⟩
  rintro ⟨w, a, rfl⟩
  exact closed_walk_visited_graph_same_cycle_reachable ρ b v (hOrbit a₀ a)

theorem closed_walk_visited_vertex_bound {α V : Type*} [Fintype α] [Fintype V]
    [Nonempty α] (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c) :
    Nat.card (Set.range v) ≤ Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1 :=
  by
    simpa only [← Nat.card_eq_fintype_card] using
      finite_labeled_vertex_card_bound _ _ (closed_walk_visited_graph_connected ρ b v hOrbit)

theorem closed_walk_maximal_vertices_tree {α V : Type*} [Fintype α] [Fintype V]
    [Nonempty α] (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hMax : Nat.card (Set.range v) =
      Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1) :
    (closedWalkVisitedGraph ρ b v).IsTree :=
  finite_labeled_maximal_vertex_tree _ _
    (closed_walk_visited_graph_connected ρ b v hOrbit)
      (by simpa only [Nat.card_eq_fintype_card] using hMax)

theorem closed_walk_maximal_vertices_nonloop {α V : Type*} [Fintype α] [Fintype V]
    [Nonempty α] (ρ : Equiv.Perm α) (b : α → Bool) (v : α → V)
    (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hMax : Nat.card (Set.range v) =
      Nat.card (Set.range (orientedClosedWalkEntry ρ b v)) + 1)
    (e : Set.range (orientedClosedWalkEntry ρ b v)) : e.val.1 ≠ e.val.2 := by
  have h := finite_labeled_maximal_vertex_nonloop
    (closedWalkEntryFirst ρ b v) (closedWalkEntrySecond ρ b v)
    (closed_walk_visited_graph_connected ρ b v hOrbit)
      (by simpa only [Nat.card_eq_fintype_card] using hMax) e
  exact fun he => h (Subtype.ext he)

theorem bernoulli_walk_entry_range_card {n k : ℕ} (b : Fin (k + 1) → Bool)
    (v : Fin (k + 1) → Fin n) :
    Nat.card (Set.range (orientedClosedWalkEntry (finRotate (k + 1)) b v)) =
      (bernoulliWalkEntries b v).toFinset.card := by
  let e : Set.range (orientedClosedWalkEntry (finRotate (k + 1)) b v) ≃
      (bernoulliWalkEntries b v).toFinset :=
    Equiv.subtypeEquivRight (fun a => by
      simp only [List.mem_toFinset, bernoulliWalkEntries, List.mem_ofFn']
      rfl)
  exact (Nat.card_congr e).trans (by simp only [Nat.card_eq_fintype_card, Fintype.card_coe])

theorem bernoulli_walk_visited_vertex_bound {n k : ℕ} (b : Fin (k + 1) → Bool)
    (v : Fin (k + 1) → Fin n) :
    Nat.card (Set.range v) ≤ (bernoulliWalkEntries b v).toFinset.card + 1 := by
  rw [← bernoulli_walk_entry_range_card]
  exact closed_walk_visited_vertex_bound _ b v (fin_rotate_same_cycle k)

theorem bernoulli_walk_surviving_vertex_bound {n k : ℕ} (b : Fin (k + 1) → Bool)
    (v : Fin (k + 1) → Fin n)
    (hNoSingleton : ∀ e, (bernoulliWalkEntries b v).count e ≠ 1) :
    2 * Nat.card (Set.range v) ≤ k + 3 := by
  have hVertex := bernoulli_walk_visited_vertex_bound b v
  have hEntry := bernoulli_centered_walk_distinct_entry_bound b v hNoSingleton
  omega

end CircularLaw
