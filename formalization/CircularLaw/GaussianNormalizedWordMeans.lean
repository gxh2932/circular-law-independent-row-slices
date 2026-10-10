import CircularLaw.GaussianWordMeanLimits
import CircularLaw.GaussianScaledMatrixWords

/-!
# Actual normalized Gaussian word means

Balancing the direct and adjoint position types gives the exact scalar
coefficient after normalization by the square root of the dimension.
Thus the normalized matrix trace divided by the dimension is exactly
the raw word normalization used in the vertex-count limit theorem.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

theorem gaussian_matrix_word_scale_balanced (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) (c : ℂ) :
    gaussianMatrixWordScale c (List.ofFn b) =
      ((‖c‖ ^ (2 * Fintype.card (GaussianDirectPositions b)) : ℝ) : ℂ) := by
  rw [gaussianMatrixWordScale, List.map_ofFn, List.prod_ofFn]
  change (∏ t, if b t then star c else c) = _
  rw [finite_bool_product_split]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← Fintype.card_congr e₀]
  exact complex_balanced_power_eq_norm_power c _

theorem gaussian_normalized_word_trace_eq {n : ℕ} (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) (x : GaussianSquareSample n) :
    (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn b) x).trace.re / n =
      (gaussianMatrixWord (List.ofFn b) x).trace.re /
        (n : ℝ) ^ (Fintype.card (GaussianDirectPositions b) + 1) := by
  rw [gaussian_scaled_matrix_word_trace_eq, gaussian_matrix_word_scale_balanced k b e₀]
  have hNorm : ‖(Real.sqrt (n : ℝ) : ℂ)⁻¹‖ ^
      (2 * Fintype.card (GaussianDirectPositions b)) =
      (1 / (n : ℝ)) ^ Fintype.card (GaussianDirectPositions b) := by
    rw [pow_mul, inverse_sqrt_dimension_norm_sq]
  rw [hNorm]
  simp only [Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    div_eq_mul_inv, one_mul, inv_pow, pow_succ]
  ring

theorem gaussian_normalized_word_mean_eq (n k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    (∫ x, (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn b) x).trace.re / n
      ∂gaussianSquareMatrixLaw n) = gaussianNormalizedWordMean n k b := by
  simp only [gaussian_normalized_word_trace_eq k b e₀, gaussianNormalizedWordMean]

theorem gaussian_normalized_word_trace_mean_tendsto (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    Tendsto (fun n : ℕ => ∫ x,
      (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn b) x).trace.re / n
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 (gaussianWordLeadingCount k b : ℝ)) := by
  simp only [gaussian_normalized_word_mean_eq _ k b e₀]
  exact gaussian_normalized_word_mean_tendsto k b e₀

end CircularLaw
