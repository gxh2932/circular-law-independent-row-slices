import CircularLaw.GaussianTwoWordCovariance
import CircularLaw.GaussianAllWordMeans

/-!
# Actual normalized Gaussian word covariances vanish

Square-root normalization supplies exactly the dimension power in the
connected-pairing formula. This identifies the covariance of actual
normalized traces with the nonnegative mixed sum, without assuming the
individual words or their union are balanced. Empty-word covariances
vanish exactly. Every fixed pair of word traces has covariance tending
to zero under the actual Gaussian matrix laws.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianNormalizedWordTrace {n : ℕ} (w : List Bool) (x : GaussianSquareSample n) : ℂ :=
  (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ w x).trace / n

def gaussianNormalizedWordCovariance (n : ℕ) (w v : List Bool) : ℂ :=
  (∫ x, gaussianNormalizedWordTrace w x * gaussianNormalizedWordTrace v x ∂gaussianSquareMatrixLaw n) -
    gaussianNormalizedWordComplexMean n w * gaussianNormalizedWordComplexMean n v

theorem gaussian_two_word_scale_product_balanced (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (e₀ : GaussianWordPairing (Sum.elim b c)) (d : ℂ) :
    gaussianMatrixWordScale d (List.ofFn b) * gaussianMatrixWordScale d (List.ofFn c) =
      ((‖d‖ ^ (2 * Fintype.card (GaussianDirectPositions (Sum.elim b c))) : ℝ) : ℂ) := by
  have hProd : gaussianMatrixWordScale d (List.ofFn b) * gaussianMatrixWordScale d (List.ofFn c) =
      ∏ a : Fin (k + 1) ⊕ Fin (l + 1), if Sum.elim b c a then star d else d := by
    rw [gaussianMatrixWordScale, gaussianMatrixWordScale, List.map_ofFn, List.map_ofFn,
      List.prod_ofFn, List.prod_ofFn]
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rfl
  rw [hProd, finite_bool_product_split]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← Fintype.card_congr e₀]
  exact complex_balanced_power_eq_norm_power d _

theorem gaussian_normalized_word_product_integrable (n : ℕ) (w v : List Bool) :
    Integrable (fun x => gaussianNormalizedWordTrace w x * gaussianNormalizedWordTrace v x)
      (gaussianSquareMatrixLaw n) := by
  have hEq : (fun x : GaussianSquareSample n =>
      gaussianNormalizedWordTrace w x * gaussianNormalizedWordTrace v x) =
      fun x => (gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ w *
        gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ v / (n : ℂ) ^ 2) *
          ((gaussianMatrixWord w x).trace * (gaussianMatrixWord v x).trace) := by
    funext x
    simp only [gaussianNormalizedWordTrace, gaussian_scaled_matrix_word_trace_eq, div_eq_mul_inv]
    ring
  rw [hEq]
  exact (gaussian_matrix_word_trace_product_integrable n w v).const_mul _

theorem gaussian_normalized_word_covariance_eq_scaled_raw (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    gaussianNormalizedWordCovariance n (List.ofFn b) (List.ofFn c) =
      (gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn b) *
        gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn c) / (n : ℂ) ^ 2) *
          gaussianTwoWordRawCovariance n k l b c := by
  have hEq : (fun x : GaussianSquareSample n =>
      gaussianNormalizedWordTrace (List.ofFn b) x * gaussianNormalizedWordTrace (List.ofFn c) x) =
      fun x => (gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn b) *
        gaussianMatrixWordScale (Real.sqrt (n : ℝ) : ℂ)⁻¹ (List.ofFn c) / (n : ℂ) ^ 2) *
          ((gaussianMatrixWord (List.ofFn b) x).trace * (gaussianMatrixWord (List.ofFn c) x).trace) := by
    funext x
    simp only [gaussianNormalizedWordTrace, gaussian_scaled_matrix_word_trace_eq, div_eq_mul_inv]
    ring
  rw [gaussianNormalizedWordCovariance, hEq, integral_const_mul,
    gaussianNormalizedWordComplexMean, gaussianNormalizedWordComplexMean]
  simp only [gaussian_scaled_matrix_word_trace_eq]
  simp only [integral_div, integral_const_mul]
  simp only [gaussianTwoWordRawCovariance, div_eq_mul_inv]
  ring

theorem gaussian_normalized_word_covariance_eq_mixed (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    gaussianNormalizedWordCovariance n (List.ofFn b) (List.ofFn c) =
      (gaussianTwoWordMixedContribution n k l b c : ℂ) := by
  rw [gaussian_normalized_word_covariance_eq_scaled_raw]
  by_cases h : Nonempty (GaussianWordPairing (Sum.elim b c))
  · obtain ⟨e₀⟩ := h
    rw [gaussian_two_word_scale_product_balanced k l b c e₀]
    have hNorm : ‖(Real.sqrt (n : ℝ) : ℂ)⁻¹‖ ^
        (2 * Fintype.card (GaussianDirectPositions (Sum.elim b c))) =
        (1 / (n : ℝ)) ^ Fintype.card (GaussianDirectPositions (Sum.elim b c)) := by
      rw [pow_mul, inverse_sqrt_dimension_norm_sq]
    rw [hNorm, ← gaussian_two_word_raw_covariance_normalized]
    simp only [div_eq_mul_inv, one_mul, inv_pow, pow_add]
    push_cast
    ring
  · letI : IsEmpty (GaussianWordPairing (Sum.elim b c)) := ⟨fun e => h ⟨e⟩⟩
    rw [gaussian_two_word_raw_covariance_eq_cross_sum, gaussianTwoWordMixedContribution]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, Complex.ofReal_zero]

theorem gaussian_normalized_word_covariance_norm_bound {n : ℕ} (hn : 0 < n) (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    ‖gaussianNormalizedWordCovariance n (List.ofFn b) (List.ofFn c)‖ ≤
      ((Fintype.card (GaussianDirectPositions (Sum.elim b c))).factorial : ℝ) / n := by
  rw [gaussian_normalized_word_covariance_eq_mixed, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussian_two_word_mixed_contribution_nonneg n k l b c)]
  exact gaussian_two_word_mixed_contribution_bound hn k l b c

theorem gaussian_normalized_word_covariance_nonempty_tendsto (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordCovariance n (List.ofFn b) (List.ofFn c)) atTop
      (𝓝 0) := by
  simp only [gaussian_normalized_word_covariance_eq_mixed]
  have h := (Complex.continuous_ofReal.tendsto _).comp (gaussian_two_word_mixed_contribution_tendsto k l b c)
  simpa only [Complex.ofReal_zero] using h

theorem gaussian_normalized_word_covariance_symm (n : ℕ) (w v : List Bool) :
    gaussianNormalizedWordCovariance n w v = gaussianNormalizedWordCovariance n v w := by
  simp only [gaussianNormalizedWordCovariance, mul_comm]

theorem gaussian_normalized_word_covariance_nil (n : ℕ) (w : List Bool) :
    gaussianNormalizedWordCovariance n [] w = 0 := by
  have hNil (x : GaussianSquareSample n) : gaussianNormalizedWordTrace [] x = (n : ℂ) / n := by
    simp only [gaussianNormalizedWordTrace, gaussianScaledMatrixWord, List.map_nil,
      List.prod_nil, Matrix.trace_one, Fintype.card_fin]
  rw [gaussianNormalizedWordCovariance]
  simp only [hNil, integral_const_mul]
  have hMeanNil : gaussianNormalizedWordComplexMean n [] = (n : ℂ) / n := by
    simp only [gaussianNormalizedWordComplexMean, gaussianScaledMatrixWord, List.map_nil,
      List.prod_nil, Matrix.trace_one, Fintype.card_fin, integral_const, probReal_univ,
      one_smul]
  rw [hMeanNil]
  change ((n : ℂ) / n) * gaussianNormalizedWordComplexMean n w -
    ((n : ℂ) / n) * gaussianNormalizedWordComplexMean n w = 0
  exact sub_self _

theorem gaussian_normalized_word_covariance_tendsto (w v : List Bool) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordCovariance n w v) atTop (𝓝 0) := by
  cases w with
  | nil => simp only [gaussian_normalized_word_covariance_nil]; exact tendsto_const_nhds
  | cons b₀ w =>
    cases v with
    | nil =>
      simp only [gaussian_normalized_word_covariance_symm _ (b₀ :: w) [],
        gaussian_normalized_word_covariance_nil]
      exact tendsto_const_nhds
    | cons c₀ v =>
      simpa only [List.ofFn_get] using gaussian_normalized_word_covariance_nonempty_tendsto
        w.length v.length (b₀ :: w).get (c₀ :: v).get

end CircularLaw
