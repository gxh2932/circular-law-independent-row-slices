import CircularLaw.BlockPreservingPermutations
import CircularLaw.GaussianMixedPairingDecay

/-!
# Separate trace pairings give exactly the squared mean

The first coordinate records the trace block. A matching that preserves
it splits into two arbitrary one-trace permutations. Both cycle counts
add, and the finite sum of these contributions is the squared one-trace
sum. All remaining matchings cross the two blocks.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem gaussian_two_trace_successor_eq_block (k : ℕ) :
    gaussianTwoTraceSuccessor k = blockPermutation (fun _ : Bool => finRotate (k + 1)) := by
  apply Equiv.ext
  intro a
  rfl

theorem gaussian_two_trace_block_exponent (k : ℕ)
    (τ : Bool → Equiv.Perm (Fin (k + 1))) :
    gaussianTwoTraceCycleExponent k (blockPermutation τ) =
      gaussianGramCycleExponent k (τ true) + gaussianGramCycleExponent k (τ false) := by
  rw [gaussianTwoTraceCycleExponent, gaussian_two_trace_successor_eq_block,
    block_permutation_inv, block_permutation_mul, block_permutation_two_cycle_count,
    block_permutation_two_cycle_count]
  unfold gaussianGramCycleExponent
  omega

theorem gaussian_two_trace_separate_pairing_sum (n k : ℕ) :
    (∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
      if ∀ a, (σ a).1 = a.1 then (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ else 0) =
      (∑ τ : Equiv.Perm (Fin (k + 1)), (n : ℝ) ^ gaussianGramCycleExponent k τ) ^ 2 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun σ : Equiv.Perm (Bool × Fin (k + 1)) => ∀ a, (σ a).1 = a.1)
    _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun σ => (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ)]
  rw [← (blockPreservingPermutationsEquiv Bool (Fin (k + 1))).symm.sum_comp]
  change (∑ τ : Bool → Equiv.Perm (Fin (k + 1)),
    (n : ℝ) ^ gaussianTwoTraceCycleExponent k (blockPermutation τ)) = _
  simp only [gaussian_two_trace_block_exponent, pow_add]
  rw [← (Equiv.boolArrowEquivProd (Equiv.Perm (Fin (k + 1)))).symm.sum_comp,
    Fintype.sum_prod_type]
  change (∑ τ : Equiv.Perm (Fin (k + 1)), ∑ υ : Equiv.Perm (Fin (k + 1)),
    (n : ℝ) ^ gaussianGramCycleExponent k υ * (n : ℝ) ^ gaussianGramCycleExponent k τ) = _
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro υ _
  exact mul_comm _ _

theorem gaussian_two_trace_cycle_sum_split (n k : ℕ) :
    (∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
      (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ) =
      (∑ τ : Equiv.Perm (Fin (k + 1)), (n : ℝ) ^ gaussianGramCycleExponent k τ) ^ 2 +
      ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        if ∃ a, (σ a).1 ≠ a.1 then (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ else 0 := by
  rw [← gaussian_two_trace_separate_pairing_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : ∀ a, (σ a).1 = a.1
  · rw [if_pos h, if_neg (by simpa only [not_exists, not_not] using h), add_zero]
  · have hCross : ∃ a, (σ a).1 ≠ a.1 := by simpa only [not_forall] using h
    rw [if_neg h, if_pos hCross, zero_add]

end CircularLaw
