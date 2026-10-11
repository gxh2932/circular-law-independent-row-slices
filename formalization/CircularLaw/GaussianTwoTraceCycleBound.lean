import CircularLaw.GaussianMomentCycleBound

/-!
# Pairings connecting two Gram traces lose a dimension power

The successor acts separately on the two trace blocks. A matching that
moves one label between them identifies their first-permutation cycle
vertices. Together with reachability inside each successor orbit this
makes the full cycle incidence graph connected. Its exponent is at most
`2*order+1`, strictly below the product's normalization `2*order+2`.
-/

noncomputable section
open Classical

namespace CircularLaw

def permutationSecondFactorHom (α β : Type*) :
    Equiv.Perm β →* Equiv.Perm (α × β) where
  toFun σ := Equiv.prodCongr (Equiv.refl α) σ
  map_one' := by ext a <;> simp
  map_mul' := by intro σ τ; ext a <;> simp [Equiv.Perm.mul_apply]

def gaussianTwoTraceSuccessor (k : ℕ) : Equiv.Perm (Bool × Fin (k + 1)) :=
  permutationSecondFactorHom Bool (Fin (k + 1)) (finRotate (k + 1))

theorem gaussian_two_trace_same_cycle_in_block (k : ℕ) (b : Bool) (i j : Fin (k + 1)) :
    (gaussianTwoTraceSuccessor k).SameCycle (b, i) (b, j) := by
  obtain ⟨m, hm⟩ := fin_rotate_same_cycle k i j
  refine ⟨m, ?_⟩
  change ((permutationSecondFactorHom Bool (Fin (k + 1)) (finRotate (k + 1))) ^ m) (b, i) = (b, j)
  rw [← map_zpow]
  change (b, ((finRotate (k + 1)) ^ m) i) = (b, j)
  rw [hm]

theorem gaussian_two_trace_cycle_graph_connected (k : ℕ)
    (σ : Equiv.Perm (Bool × Fin (k + 1)))
    (hCross : ∃ a, (σ a).1 ≠ a.1) :
    (permutationCycleGraph σ (gaussianTwoTraceSuccessor k * σ⁻¹)).Connected := by
  let τ := gaussianTwoTraceSuccessor k * σ⁻¹
  have hWithin (b : Bool) (i j : Fin (k + 1)) :
      (permutationCycleGraph σ τ).Reachable (Sum.inl (permutationCycleClass σ (b, i)))
        (Sum.inl (permutationCycleClass σ (b, j))) := by
    apply permutation_cycle_graph_reachable_same_cycle
    simpa only [τ, mul_assoc, inv_mul_cancel, mul_one] using
      gaussian_two_trace_same_cycle_in_block k b i j
  obtain ⟨⟨b, i⟩, hCross⟩ := hCross
  rcases hσ : σ (b, i) with ⟨b', j⟩
  have hb : b' ≠ b := by simpa only [hσ, Prod.fst] using hCross
  have hBridge : (permutationCycleGraph σ τ).Reachable
      (Sum.inl (permutationCycleClass σ (b, i)))
      (Sum.inl (permutationCycleClass σ (b', j))) := by
    rw [← hσ, permutation_cycle_class_apply]
  have hChoices (c : Bool) : c = b ∨ c = b' := by
    cases b <;> cases b' <;> cases c
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (hb rfl)
  have hAll (a : Bool × Fin (k + 1)) :
      (permutationCycleGraph σ τ).Reachable (Sum.inl (permutationCycleClass σ (b, i)))
        (Sum.inl (permutationCycleClass σ a)) := by
    obtain ⟨c, t⟩ := a
    rcases hChoices c with hc | hc
    · subst c
      exact hWithin b i t
    · subst c
      exact hBridge.trans (hWithin b' j t)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl (permutationCycleClass σ (b, i)), ?_⟩
  intro v
  cases v with
  | inl c =>
    induction c using Quotient.inductionOn with
    | h a => exact hAll a
  | inr c =>
    induction c using Quotient.inductionOn with
    | h a =>
      exact (hAll a).trans
        (finite_incidence_graph_adj (permutationCycleClass σ) (permutationCycleClass τ) a).reachable

def gaussianTwoTraceCycleExponent (k : ℕ) (σ : Equiv.Perm (Bool × Fin (k + 1))) : ℕ :=
  permutationCycleCount σ + permutationCycleCount (gaussianTwoTraceSuccessor k * σ⁻¹)

theorem gaussian_two_trace_mixed_cycle_exponent_bound (k : ℕ)
    (σ : Equiv.Perm (Bool × Fin (k + 1))) (hCross : ∃ a, (σ a).1 ≠ a.1) :
    gaussianTwoTraceCycleExponent k σ ≤ 2 * (k + 1) + 1 := by
  have h := finite_incidence_vertex_card_bound (permutationCycleClass σ)
    (permutationCycleClass (gaussianTwoTraceSuccessor k * σ⁻¹))
    (gaussian_two_trace_cycle_graph_connected k σ hCross)
  simpa only [gaussianTwoTraceCycleExponent, permutationCycleCount,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using h

end CircularLaw
