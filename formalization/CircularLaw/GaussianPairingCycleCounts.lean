import CircularLaw.GaussianGramTracePairings
import CircularLaw.PermutationCycleColorings

/-!
# Exact cycle-count formula for Gaussian Gram moments

For each matching permutation, the column indices are constant on its
cycles. The row indices are constant on the cycles of the cyclic
successor composed with the inverse matching. Their exact contribution
is the dimension to the sum of these two cycle counts. The formula keeps
every permutation, including nonleading ones.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem finite_complex_indicator_sum {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    (∑ a, if p a then (1 : ℂ) else 0) = (Fintype.card {a // p a} : ℂ) := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

theorem permutation_row_matching_iff {α β : Type*} (σ ρ : Equiv.Perm α) (r : α → β) :
    (∀ a, r (σ a) = r (ρ a)) ↔ ∀ a, r ((ρ * σ⁻¹) a) = r a := by
  constructor
  · intro h a
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using (h (σ.symm a)).symm
  · intro h a
    simpa [Equiv.Perm.mul_apply] using (h (σ a)).symm

theorem permutation_row_matching_card {α : Type*} [Fintype α] [DecidableEq α]
    (σ ρ : Equiv.Perm α) (n : ℕ) :
    Fintype.card {r : α → Fin n // ∀ a, r (σ a) = r (ρ a)} =
      n ^ permutationCycleCount (ρ * σ⁻¹) := by
  let e : {r : α → Fin n // ∀ a, r (σ a) = r (ρ a)} ≃
      {r : α → Fin n // ∀ a, r ((ρ * σ⁻¹) a) = r a} :=
    Equiv.subtypeEquivRight (permutation_row_matching_iff σ ρ)
  exact (Fintype.card_congr e).trans (permutation_invariant_fin_coloring_card (ρ * σ⁻¹) n)

theorem gaussian_pairing_assignment_count {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (σ ρ : Equiv.Perm α) :
    (∑ r : α → Fin n, ∑ s : α → Fin n,
      if ∀ a, r (σ a) = r (ρ a) ∧ s (σ a) = s a then (1 : ℂ) else 0) =
      (n : ℂ) ^ (permutationCycleCount σ + permutationCycleCount (ρ * σ⁻¹)) := by
  calc
    _ = (∑ r : α → Fin n, if ∀ a, r (σ a) = r (ρ a) then (1 : ℂ) else 0) *
        (∑ s : α → Fin n, if ∀ a, s (σ a) = s a then (1 : ℂ) else 0) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      simp only [forall_and]
      by_cases hr : ∀ a, r (σ a) = r (ρ a)
      · by_cases hs : ∀ a, s (σ a) = s a
        · rw [if_pos ⟨hr, hs⟩, if_pos hr, if_pos hs, one_mul]
        · rw [if_neg (fun h => hs h.2), if_pos hr, if_neg hs, mul_zero]
      · by_cases hs : ∀ a, s (σ a) = s a
        · rw [if_neg (fun h => hr h.1), if_neg hr, if_pos hs, zero_mul]
        · rw [if_neg (fun h => hr h.1), if_neg hr, if_neg hs, zero_mul]
    _ = (Fintype.card {r : α → Fin n // ∀ a, r (σ a) = r (ρ a)} : ℂ) *
        (Fintype.card {s : α → Fin n // ∀ a, s (σ a) = s a} : ℂ) := by
      rw [finite_complex_indicator_sum, finite_complex_indicator_sum]
    _ = _ := by
      rw [permutation_row_matching_card σ ρ n, permutation_invariant_fin_coloring_card σ n]
      push_cast
      rw [pow_add, mul_comm]

theorem gaussian_gram_trace_pow_cycle_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace
      ∂gaussianSquareMatrixLaw n) =
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        (n : ℂ) ^ (permutationCycleCount σ +
          permutationCycleCount (finRotate (k + 1) * σ⁻¹)) := by
  rw [gaussian_gram_trace_pow_pairing_integral]
  apply Finset.sum_congr rfl
  intro σ _
  apply Eq.trans ?_ (gaussian_pairing_assignment_count n σ (finRotate (k + 1)))
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> rfl

theorem gaussian_gram_trace_pow_cycle_real_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re
      ∂gaussianSquareMatrixLaw n) =
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        (n : ℝ) ^ (permutationCycleCount σ +
          permutationCycleCount (finRotate (k + 1) * σ⁻¹)) := by
  change (∫ x, RCLike.re ((gaussianSquareMatrix x *
    (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace
    ∂gaussianSquareMatrixLaw n) = _
  rw [integral_re (gaussian_gram_trace_pow_pairing_integrable n k),
    gaussian_gram_trace_pow_cycle_integral]
  change (∑ σ : Equiv.Perm (Fin (k + 1)),
    (n : ℂ) ^ (permutationCycleCount σ +
      permutationCycleCount (finRotate (k + 1) * σ⁻¹))).re = _
  simp only [Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    Complex.ofReal_re]

theorem gaussian_zero_shift_singular_moment_cycle_integral (n k : ℕ) :
    (∫ x, (∫ t, (t : ℝ) ^ (2 * (k + 1)) ∂gaussianSingularMeasure 0 x)
      ∂gaussianSquareMatrixLaw n) =
      (∑ σ : Equiv.Perm (Fin (k + 1)),
        (n : ℝ) ^ (permutationCycleCount σ +
          permutationCycleCount (finRotate (k + 1) * σ⁻¹))) / (n : ℝ) ^ (k + 2) := by
  simp only [gaussianSingularMeasure, normalizedShiftedGaussianMatrix, zero_smul, sub_zero]
  simp only [square_singular_measure_even_moment]
  simp only [square_gram_trace_pow_smul, pow_mul, inverse_sqrt_dimension_norm_sq]
  rw [integral_div, integral_const_mul, gaussian_gram_trace_pow_cycle_real_integral]
  simp only [div_eq_mul_inv, one_mul, inv_pow, pow_succ]
  ring

end CircularLaw
