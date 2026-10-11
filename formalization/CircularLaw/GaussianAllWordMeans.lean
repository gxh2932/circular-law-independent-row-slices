import CircularLaw.GaussianNormalizedWordMeans

/-!
# Mean convergence for every finite normalized Gaussian word

Balanced nonempty words use the actual vertex-class count. Unbalanced
words have zero mean by the checked imbalance argument. The empty word
is the identity and has normalized trace one in positive dimension.
Thus every finite word has a finite mean limit, with no balance
assumption and with both real and imaginary components accounted for.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianNormalizedWordComplexMean (n : ℕ) (w : List Bool) : ℂ :=
  ∫ x, (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ w x).trace / n
    ∂gaussianSquareMatrixLaw n

theorem gaussian_matrix_word_balanced_integral_real (n k : ℕ)
    (b : Fin (k + 1) → Bool) (e₀ : GaussianWordPairing b) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace ∂gaussianSquareMatrixLaw n) =
      ((∫ x, (gaussianMatrixWord (List.ofFn b) x).trace.re
        ∂gaussianSquareMatrixLaw n : ℝ) : ℂ) := by
  rw [gaussian_matrix_word_vertex_integral n k b e₀,
    gaussian_matrix_word_vertex_real_integral n k b e₀]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_natCast]

theorem gaussian_normalized_word_complex_mean_eq (n k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    gaussianNormalizedWordComplexMean n (List.ofFn b) = (gaussianNormalizedWordMean n k b : ℂ) := by
  rw [gaussianNormalizedWordComplexMean]
  simp only [gaussian_scaled_matrix_word_trace_eq]
  rw [integral_div, integral_const_mul, gaussian_matrix_word_scale_balanced k b e₀,
    gaussian_matrix_word_balanced_integral_real n k b e₀]
  have hNorm : ‖(Real.sqrt (n : ℝ) : ℂ)⁻¹‖ ^
      (2 * Fintype.card (GaussianDirectPositions b)) =
      (1 / (n : ℝ)) ^ Fintype.card (GaussianDirectPositions b) := by
    rw [pow_mul, inverse_sqrt_dimension_norm_sq]
  rw [hNorm, gaussianNormalizedWordMean, integral_div]
  simp only [div_eq_mul_inv, one_mul, inv_pow, pow_succ]
  push_cast
  ring

theorem gaussian_normalized_word_complex_mean_tendsto (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n (List.ofFn b)) atTop
      (𝓝 (gaussianWordLeadingCount k b : ℂ)) := by
  simp only [gaussian_normalized_word_complex_mean_eq _ k b e₀]
  exact (Complex.continuous_ofReal.tendsto _).comp (gaussian_normalized_word_mean_tendsto k b e₀)

theorem gaussian_normalized_word_complex_mean_unbalanced (n : ℕ) (w : List Bool)
    (hw : w.count false ≠ w.count true) : gaussianNormalizedWordComplexMean n w = 0 := by
  rw [gaussianNormalizedWordComplexMean, integral_div,
    gaussian_scaled_matrix_word_count_mismatch_zero n _ w hw, zero_div]

theorem gaussian_normalized_word_complex_mean_nil {n : ℕ} (hn : 0 < n) :
    gaussianNormalizedWordComplexMean n [] = 1 := by
  simp only [gaussianNormalizedWordComplexMean, gaussianScaledMatrixWord,
    List.map_nil, List.prod_nil, Matrix.trace_one, Fintype.card_fin]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [hnC]

theorem gaussian_all_word_complex_mean_has_limit (w : List Bool) :
    ∃ m : ℕ, Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n w) atTop (𝓝 (m : ℂ)) := by
  cases w with
  | nil =>
    refine ⟨1, ?_⟩
    simp only [Nat.cast_one]
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono
      (fun _ hn => (gaussian_normalized_word_complex_mean_nil hn).symm))
  | cons b₀ w =>
    by_cases hw : (b₀ :: w).count false = (b₀ :: w).count true
    · let b : Fin (w.length + 1) → Bool := (b₀ :: w).get
      have hCard : Fintype.card (GaussianDirectPositions b) =
          Fintype.card (GaussianAdjointPositions b) := by
        rw [← list_ofFn_count_eq_fiber_card b false, ← list_ofFn_count_eq_fiber_card b true]
        simpa only [b, List.ofFn_get] using hw
      let e₀ : GaussianWordPairing b := Fintype.equivOfCardEq hCard
      refine ⟨gaussianWordLeadingCount w.length b, ?_⟩
      simpa only [b, List.ofFn_get] using gaussian_normalized_word_complex_mean_tendsto w.length b e₀
    · refine ⟨0, ?_⟩
      simp only [gaussian_normalized_word_complex_mean_unbalanced _ _ hw, Nat.cast_zero]
      exact tendsto_const_nhds

end CircularLaw
