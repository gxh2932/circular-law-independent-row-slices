import CircularLaw.GaussianMomentCycleBound

/-!
# Leading Gaussian pairings are exactly labeled cycle trees

Attaining the maximal dimension exponent forces the connected cycle
incidence graph to have as many edges as labels and one more vertex.
Thus it is a tree and its label-to-edge map is bijective. Conversely,
these two properties force the maximal exponent. This identifies the
objects whose enumeration must supply the limiting moment values.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem gaussian_gram_cycle_graph_connected (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    (permutationCycleGraph σ (finRotate (k + 1) * σ⁻¹)).Connected := by
  apply permutation_cycle_graph_connected
  intro a b
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using fin_rotate_same_cycle k a b

theorem gaussian_leading_pairing_is_tree (k : ℕ) (σ : Equiv.Perm (Fin (k + 1)))
    (h : gaussianGramCycleExponent k σ = k + 2) :
    (permutationCycleGraph σ (finRotate (k + 1) * σ⁻¹)).IsTree := by
  apply finite_incidence_maximal_vertex_tree (permutationCycleClass σ)
    (permutationCycleClass (finRotate (k + 1) * σ⁻¹))
    (gaussian_gram_cycle_graph_connected k σ)
  simpa only [gaussianGramCycleExponent, permutationCycleCount, Fintype.card_fin] using h

theorem gaussian_leading_pairing_edge_bijective (k : ℕ) (σ : Equiv.Perm (Fin (k + 1)))
    (h : gaussianGramCycleExponent k σ = k + 2) :
    Function.Bijective (finiteIncidenceEdge (permutationCycleClass σ)
      (permutationCycleClass (finRotate (k + 1) * σ⁻¹))) := by
  apply finite_incidence_maximal_vertex_edge_bijective (permutationCycleClass σ)
    (permutationCycleClass (finRotate (k + 1) * σ⁻¹))
    (gaussian_gram_cycle_graph_connected k σ)
  simpa only [gaussianGramCycleExponent, permutationCycleCount, Fintype.card_fin] using h

theorem gaussian_leading_pairing_iff_labeled_tree (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    gaussianGramCycleExponent k σ = k + 2 ↔
      (permutationCycleGraph σ (finRotate (k + 1) * σ⁻¹)).IsTree ∧
      Function.Bijective (finiteIncidenceEdge (permutationCycleClass σ)
        (permutationCycleClass (finRotate (k + 1) * σ⁻¹))) := by
  constructor
  · intro h
    exact ⟨gaussian_leading_pairing_is_tree k σ h, gaussian_leading_pairing_edge_bijective k σ h⟩
  · rintro ⟨hTree, hLabels⟩
    have hCard := (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
    have hEdge := Nat.card_eq_of_bijective _ hLabels
    change Nat.card (Fin (k + 1)) =
      Nat.card (permutationCycleGraph σ (finRotate (k + 1) * σ⁻¹)).edgeSet at hEdge
    rw [← hEdge] at hCard
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at hCard
    change k + 1 + 1 = gaussianGramCycleExponent k σ at hCard
    omega

end CircularLaw
