import CircularLaw.FiniteIncidenceGraph

/-!
# Cycle incidence graphs for a transitive product of permutations

Each label joins its cycle under the first permutation to its cycle
under the second. Labels along an orbit of the product give reachable
vertices. If the product has one orbit, the actual incidence graph is
connected, yielding the sum-of-cycle-counts bound.
-/

noncomputable section
open Classical

namespace CircularLaw

def permutationCycleClass {α : Type*} (σ : Equiv.Perm α) (a : α) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) := Quotient.mk _ a

theorem permutation_cycle_class_apply {α : Type*} (σ : Equiv.Perm α) (a : α) :
    permutationCycleClass σ (σ a) = permutationCycleClass σ a := by
  apply Quotient.sound
  exact Equiv.Perm.SameCycle.symm ⟨1, by simp⟩

def permutationCycleGraph {α : Type*} (σ τ : Equiv.Perm α) :=
  finiteIncidenceGraph (permutationCycleClass σ) (permutationCycleClass τ)

theorem permutation_cycle_graph_reachable_product {α : Type*} (σ τ : Equiv.Perm α) (a : α) :
    (permutationCycleGraph σ τ).Reachable (Sum.inl (permutationCycleClass σ a))
      (Sum.inl (permutationCycleClass σ ((τ * σ) a))) := by
  have hFirst := (finite_incidence_graph_adj
    (permutationCycleClass σ) (permutationCycleClass τ) (σ a)).reachable
  have hSecond := (finite_incidence_graph_adj
    (permutationCycleClass σ) (permutationCycleClass τ) ((τ * σ) a)).reachable.symm
  simp only [Equiv.Perm.mul_apply, permutation_cycle_class_apply] at hFirst hSecond ⊢
  exact hFirst.trans hSecond

theorem permutation_cycle_graph_reachable_same_cycle {α : Type*} (σ τ : Equiv.Perm α)
    {a b : α} (hab : (τ * σ).SameCycle a b) :
    (permutationCycleGraph σ τ).Reachable (Sum.inl (permutationCycleClass σ a))
      (Sum.inl (permutationCycleClass σ b)) := by
  have hPow (m : ℤ) (x : α) :
      (permutationCycleGraph σ τ).Reachable (Sum.inl (permutationCycleClass σ x))
        (Sum.inl (permutationCycleClass σ (((τ * σ) ^ m) x))) := by
    induction m using Int.induction_on generalizing x with
    | zero => simp
    | succ m ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply]
      exact (permutation_cycle_graph_reachable_product σ τ x).trans (ih ((τ * σ) x))
    | pred m ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply]
      have hBack : (permutationCycleGraph σ τ).Reachable
          (Sum.inl (permutationCycleClass σ x))
          (Sum.inl (permutationCycleClass σ ((τ * σ)⁻¹ x))) := by
        simpa using (permutation_cycle_graph_reachable_product σ τ ((τ * σ).symm x)).symm
      exact hBack.trans (ih ((τ * σ)⁻¹ x))
  obtain ⟨m, rfl⟩ := hab
  exact hPow m a

theorem permutation_cycle_graph_connected {α : Type*} [Nonempty α] (σ τ : Equiv.Perm α)
    (hOrbit : ∀ a b, (τ * σ).SameCycle a b) :
    (permutationCycleGraph σ τ).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨a₀⟩ := ‹Nonempty α›
  refine ⟨Sum.inl (permutationCycleClass σ a₀), ?_⟩
  intro v
  cases v with
  | inl c =>
    induction c using Quotient.inductionOn with
    | h b => exact permutation_cycle_graph_reachable_same_cycle σ τ (hOrbit a₀ b)
  | inr c =>
    induction c using Quotient.inductionOn with
    | h b =>
      exact (permutation_cycle_graph_reachable_same_cycle σ τ (hOrbit a₀ b)).trans
        (finite_incidence_graph_adj (permutationCycleClass σ) (permutationCycleClass τ) b).reachable

theorem permutation_cycle_count_product_bound {α : Type*} [Fintype α] [Nonempty α]
    (σ τ : Equiv.Perm α) (hOrbit : ∀ a b, (τ * σ).SameCycle a b) :
    permutationCycleCount σ + permutationCycleCount τ ≤ Fintype.card α + 1 := by
  exact finite_incidence_vertex_card_bound (permutationCycleClass σ) (permutationCycleClass τ)
    (permutation_cycle_graph_connected σ τ hOrbit)

end CircularLaw
