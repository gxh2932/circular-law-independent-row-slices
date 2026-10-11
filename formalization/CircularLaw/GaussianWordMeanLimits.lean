import CircularLaw.GaussianWordPairingCounts
import CircularLaw.DimensionPowerLimit

/-!
# Mean limits for every balanced Gaussian matrix word

The actual trace keeps the direct and adjoint factors in their word
order. Its normalization is dimension to `direct factors + 1`.
The exact finite matching formula and the vertex-class bound show that
the mean converges to the number of maximal-exponent matchings. This is
the first-moment input for shifted Gram moments; concentration and the
shifted moment assembly are separate proof obligations.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

theorem gaussian_matrix_word_vertex_real_integral (n k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace.re ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing b,
        (n : ℝ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e := by
  change (∫ x, RCLike.re (gaussianMatrixWord (List.ofFn b) x).trace
    ∂gaussianSquareMatrixLaw n) = _
  rw [integral_re (gaussian_matrix_word_trace_integrable n (List.ofFn b)),
    gaussian_matrix_word_vertex_integral n k b e₀]
  change (∑ e : GaussianWordPairing b,
    (n : ℂ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e).re = _
  simp only [Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    Complex.ofReal_re]

def gaussianNormalizedWordMean (n k : ℕ) (b : Fin (k + 1) → Bool) : ℝ :=
  ∫ x, (gaussianMatrixWord (List.ofFn b) x).trace.re /
    (n : ℝ) ^ (Fintype.card (GaussianDirectPositions b) + 1) ∂gaussianSquareMatrixLaw n

def gaussianWordLeadingCount (k : ℕ) (b : Fin (k + 1) → Bool) : ℕ :=
  Fintype.card {e : GaussianWordPairing b //
    gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1}

theorem gaussian_normalized_word_trace_integrable (n k : ℕ) (b : Fin (k + 1) → Bool) :
    Integrable (fun x => (gaussianMatrixWord (List.ofFn b) x).trace.re /
      (n : ℝ) ^ (Fintype.card (GaussianDirectPositions b) + 1)) (gaussianSquareMatrixLaw n) :=
  (gaussian_matrix_word_trace_integrable n (List.ofFn b)).re.div_const _

theorem gaussian_normalized_word_mean_eq_vertex_sum (n k : ℕ)
    (b : Fin (k + 1) → Bool) (e₀ : GaussianWordPairing b) :
    gaussianNormalizedWordMean n k b = ∑ e : GaussianWordPairing b,
      (n : ℝ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e /
        (n : ℝ) ^ (Fintype.card (GaussianDirectPositions b) + 1) := by
  rw [gaussianNormalizedWordMean, integral_div,
    gaussian_matrix_word_vertex_real_integral n k b e₀, Finset.sum_div]

theorem gaussian_normalized_word_mean_nonneg (n k : ℕ)
    (b : Fin (k + 1) → Bool) (e₀ : GaussianWordPairing b) :
    0 ≤ gaussianNormalizedWordMean n k b := by
  rw [gaussian_normalized_word_mean_eq_vertex_sum n k b e₀]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem gaussian_word_pairing_card (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    Fintype.card (GaussianWordPairing b) = (Fintype.card (GaussianDirectPositions b)).factorial := by
  rw [← Fintype.card_congr (matchingBijectionsEquiv e₀), Fintype.card_perm]

theorem gaussian_normalized_word_mean_le_factorial {n : ℕ} (hn : 0 < n) (k : ℕ)
    (b : Fin (k + 1) → Bool) (e₀ : GaussianWordPairing b) :
    gaussianNormalizedWordMean n k b ≤ ((Fintype.card (GaussianDirectPositions b)).factorial : ℝ) := by
  rw [gaussian_normalized_word_mean_eq_vertex_sum n k b e₀]
  calc
    _ ≤ ∑ _e : GaussianWordPairing b, (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ =>
        dimension_power_ratio_le_one hn (gaussian_matrix_word_vertex_exponent_bound k b e))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      gaussian_word_pairing_card k b e₀]

theorem gaussian_word_leading_count_eq_indicator_sum (k : ℕ) (b : Fin (k + 1) → Bool) :
    (gaussianWordLeadingCount k b : ℝ) = ∑ e : GaussianWordPairing b,
      if gaussianWordVertexExponent b (finRotate (k + 1)) e =
        Fintype.card (GaussianDirectPositions b) + 1 then (1 : ℝ) else 0 := by
  rw [gaussianWordLeadingCount, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

theorem gaussian_word_leading_count_le_factorial (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    gaussianWordLeadingCount k b ≤ (Fintype.card (GaussianDirectPositions b)).factorial := by
  have h := Fintype.card_subtype_le (fun e : GaussianWordPairing b =>
    gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1)
  rw [gaussian_word_pairing_card k b e₀] at h
  exact h

theorem gaussian_normalized_word_mean_tendsto (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordMean n k b) atTop
      (𝓝 (gaussianWordLeadingCount k b : ℝ)) := by
  simp only [gaussian_normalized_word_mean_eq_vertex_sum _ k b e₀]
  rw [gaussian_word_leading_count_eq_indicator_sum]
  exact tendsto_finset_sum Finset.univ (fun e _ =>
    dimension_power_ratio_tendsto _ _ (gaussian_matrix_word_vertex_exponent_bound k b e))

end CircularLaw
