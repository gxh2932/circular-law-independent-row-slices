import CircularLaw.GaussianSeparateWordPairings
import CircularLaw.GaussianWordPairingBalance
import CircularLaw.DimensionPowerLimit

/-!
# Connected-pairing formula and decay for arbitrary word covariances

Separate matchings cancel the exact product of the actual trace means.
Every remaining matching crosses the word blocks and loses a dimension
power. After division by `n^(direct factors + 2)`, its contribution is
at most `1/n` and the whole finite sum tends to zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianTwoWordRawCovariance (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) : ℂ :=
  (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace *
    (gaussianMatrixWord (List.ofFn c) x).trace ∂gaussianSquareMatrixLaw n) -
      (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace ∂gaussianSquareMatrixLaw n) *
        (∫ x, (gaussianMatrixWord (List.ofFn c) x).trace ∂gaussianSquareMatrixLaw n)

theorem gaussian_two_word_raw_covariance_eq_cross_sum (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    gaussianTwoWordRawCovariance n k l b c =
      ∑ e : GaussianWordPairing (Sum.elim b c),
        if ∃ a, sumWalkBlock a.val ≠ sumWalkBlock (e a).val then
          (n : ℂ) ^ gaussianWordVertexExponent (Sum.elim b c)
            (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e else 0 := by
  rw [gaussianTwoWordRawCovariance, gaussian_two_word_all_pairing_integral,
    gaussian_matrix_word_all_pairing_integral, gaussian_matrix_word_all_pairing_integral,
    ← gaussian_two_word_separate_pairing_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : ∀ a, sumWalkBlock (e a).val = sumWalkBlock a.val
  · rw [if_pos h, if_neg (by
      rintro ⟨a, ha⟩
      exact ha (h a).symm), sub_self]
  · have hCross : ∃ a, sumWalkBlock a.val ≠ sumWalkBlock (e a).val := by
      obtain ⟨a, ha⟩ := not_forall.mp h
      exact ⟨a, fun hEq => ha hEq.symm⟩
    rw [if_neg h, if_pos hCross, sub_zero]

def gaussianTwoWordMixedContribution (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) : ℝ :=
  ∑ e : GaussianWordPairing (Sum.elim b c),
    if ∃ a, sumWalkBlock a.val ≠ sumWalkBlock (e a).val then
      (n : ℝ) ^ gaussianWordVertexExponent (Sum.elim b c)
        (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e /
          (n : ℝ) ^ (Fintype.card (GaussianDirectPositions (Sum.elim b c)) + 2)
    else 0

theorem gaussian_two_word_raw_covariance_normalized (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    gaussianTwoWordRawCovariance n k l b c /
      (n : ℂ) ^ (Fintype.card (GaussianDirectPositions (Sum.elim b c)) + 2) =
        (gaussianTwoWordMixedContribution n k l b c : ℂ) := by
  rw [gaussian_two_word_raw_covariance_eq_cross_sum, Finset.sum_div,
    gaussianTwoWordMixedContribution, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp only [zero_div, Complex.ofReal_zero, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast]

theorem gaussian_two_word_mixed_contribution_nonneg (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    0 ≤ gaussianTwoWordMixedContribution n k l b c := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> positivity

theorem gaussian_finite_word_pairing_card_le_factorial {α : Type*} [Fintype α] [DecidableEq α]
    (b : α → Bool) :
    Fintype.card (GaussianWordPairing b) ≤ (Fintype.card (GaussianDirectPositions b)).factorial := by
  by_cases h : Nonempty (GaussianWordPairing b)
  · obtain ⟨e₀⟩ := h
    rw [← Fintype.card_congr (matchingBijectionsEquiv e₀), Fintype.card_perm]
  · letI : IsEmpty (GaussianWordPairing b) := ⟨fun e => h ⟨e⟩⟩
    simp only [Fintype.card_of_isEmpty, Nat.zero_le]

theorem gaussian_two_word_mixed_contribution_bound {n : ℕ} (hn : 0 < n) (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    gaussianTwoWordMixedContribution n k l b c ≤
      ((Fintype.card (GaussianDirectPositions (Sum.elim b c))).factorial : ℝ) / n := by
  rw [gaussianTwoWordMixedContribution]
  calc
    _ ≤ ∑ _e : GaussianWordPairing (Sum.elim b c), 1 / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with hCross
      · exact dimension_power_ratio_le_inverse hn
          (Nat.lt_succ_of_le (gaussian_two_word_cross_exponent_bound k l (Sum.elim b c) e hCross))
      · positivity
    _ = (Fintype.card (GaussianWordPairing (Sum.elim b c)) : ℝ) / n := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast gaussian_finite_word_pairing_card_le_factorial (Sum.elim b c)

theorem gaussian_two_word_mixed_contribution_tendsto (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Tendsto (fun n : ℕ => gaussianTwoWordMixedContribution n k l b c) atTop (𝓝 0) := by
  have hLimit : Tendsto (fun n : ℕ =>
      ((Fintype.card (GaussianDirectPositions (Sum.elim b c))).factorial : ℝ) / n) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((Fintype.card (GaussianDirectPositions (Sum.elim b c))).factorial : ℝ)
    simpa only [mul_zero, mul_one_div] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun n => gaussian_two_word_mixed_contribution_nonneg n k l b c))
    ((eventually_gt_atTop 0).mono (fun _ hn => gaussian_two_word_mixed_contribution_bound hn k l b c))

end CircularLaw
