import CircularLaw.FiniteListIntegralLimits
import CircularLaw.MatrixScalarShiftWords
import CircularLaw.GaussianTracePolynomials

/-!
# Every shifted Gaussian singular-moment mean has a finite limit

The scalar-shift expansion retains every finite ordered word and its
coefficient. All normalized Gaussian word means have checked limits;
finite integration and limit passage assemble the actual shifted Gram
trace means. Taking the real part gives every even singular-moment mean
at every complex shift. Concentration of these random moments, hence
the general shifted weak law, remains a separate obligation.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianWordMeanCount (w : List Bool) : ℕ :=
  Classical.choose (gaussian_all_word_complex_mean_has_limit w)

theorem gaussian_word_mean_count_tendsto (w : List Bool) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n w) atTop
      (𝓝 (gaussianWordMeanCount w : ℂ)) :=
  Classical.choose_spec (gaussian_all_word_complex_mean_has_limit w)

theorem gaussian_word_mean_count_balanced (k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    gaussianWordMeanCount (List.ofFn b) = gaussianWordLeadingCount k b := by
  exact_mod_cast tendsto_nhds_unique (gaussian_word_mean_count_tendsto (List.ofFn b))
    (gaussian_normalized_word_complex_mean_tendsto k b e₀)

theorem gaussian_word_mean_count_unbalanced (w : List Bool)
    (hw : w.count false ≠ w.count true) : gaussianWordMeanCount w = 0 := by
  have h : Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n w) atTop (𝓝 (0 : ℂ)) := by
    simp only [gaussian_normalized_word_complex_mean_unbalanced _ w hw]
    exact tendsto_const_nhds
  exact_mod_cast tendsto_nhds_unique (gaussian_word_mean_count_tendsto w) h

theorem gaussian_word_mean_count_nil : gaussianWordMeanCount [] = 1 := by
  have h : Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n []) atTop (𝓝 (1 : ℂ)) :=
    tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono
      (fun _ hn => (gaussian_normalized_word_complex_mean_nil hn).symm))
  exact_mod_cast tendsto_nhds_unique (gaussian_word_mean_count_tendsto []) h

def gaussianShiftedTraceMean (n : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  ∫ x, ((normalizedShiftedGaussianMatrix z x *
    (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace / n
    ∂gaussianSquareMatrixLaw n

def gaussianShiftedMomentMeanLimit (z : ℂ) (k : ℕ) : ℂ :=
  ((scalarShiftWordExpansion z (gramMatrixWord k)).map
    (fun p => p.1 * (gaussianWordMeanCount p.2 : ℂ))).sum

theorem gaussian_shifted_moment_mean_limit_zero (z : ℂ) :
    gaussianShiftedMomentMeanLimit z 0 = 1 := by
  simp [gaussianShiftedMomentMeanLimit, gramMatrixWord, scalarShiftWordExpansion,
    gaussian_word_mean_count_nil]

theorem gaussian_shifted_gram_trace_word_expansion {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    ((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 *
          (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ p.2 x).trace)).sum := by
  rw [normalizedShiftedGaussianMatrix, matrix_shifted_gram_pow_word,
    matrix_scalar_shifted_word_expansion, Matrix.trace_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, Matrix.trace_smul, smul_eq_mul,
    gaussian_scaled_matrix_word_eq_adjoint_word]

theorem gaussian_shifted_normalized_trace_word_expansion {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    ((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace / n =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 *
          ((gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ p.2 x).trace / n))).sum := by
  rw [gaussian_shifted_gram_trace_word_expansion]
  simp only [div_eq_mul_inv]
  rw [← List.sum_map_mul_right]
  simp only [mul_assoc]

theorem gaussian_shifted_trace_mean_eq_word_sum (n : ℕ) (z : ℂ) (k : ℕ) :
    gaussianShiftedTraceMean n z k =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 * gaussianNormalizedWordComplexMean n p.2)).sum := by
  rw [gaussianShiftedTraceMean]
  simp only [gaussian_shifted_normalized_trace_word_expansion]
  rw [finite_list_sum_integral]
  · simp only [integral_const_mul, gaussianNormalizedWordComplexMean]
  · intro p _
    exact ((gaussian_scaled_matrix_word_trace_integrable n _ p.2).div_const (n : ℂ)).const_mul p.1

theorem gaussian_shifted_trace_mean_tendsto (z : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => gaussianShiftedTraceMean n z k) atTop
      (𝓝 (gaussianShiftedMomentMeanLimit z k)) := by
  simp only [gaussian_shifted_trace_mean_eq_word_sum, gaussianShiftedMomentMeanLimit]
  exact finite_list_sum_tendsto _ _ _ atTop (fun p _ =>
    tendsto_const_nhds.mul (gaussian_word_mean_count_tendsto p.2))

theorem gaussian_shifted_even_moment_mean_eq_trace_mean (n : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x)
      ∂gaussianSquareMatrixLaw n) = (gaussianShiftedTraceMean n z k).re := by
  simp only [gaussian_shifted_singular_even_moment_trace, gaussianShiftedTraceMean]
  rw [integral_div]
  change (∫ x, RCLike.re ((normalizedShiftedGaussianMatrix z x *
    (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace
    ∂gaussianSquareMatrixLaw n) / n = _
  rw [integral_re (gaussian_shifted_gram_trace_pow_integrable n z k), integral_div]
  simp only [← Complex.ofReal_natCast, Complex.div_ofReal_re]
  rfl

theorem gaussian_shifted_even_moment_mean_tendsto (z : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x,
      (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x) ∂gaussianSquareMatrixLaw n)
      atTop (𝓝 (gaussianShiftedMomentMeanLimit z k).re) := by
  simp only [gaussian_shifted_even_moment_mean_eq_trace_mean]
  exact (Complex.continuous_re.tendsto _).comp (gaussian_shifted_trace_mean_tendsto z k)

theorem gaussian_shifted_even_moment_mean_nonneg (n : ℕ) (z : ℂ) (k : ℕ) :
    0 ≤ ∫ x, (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x)
      ∂gaussianSquareMatrixLaw n := by
  apply integral_nonneg
  intro x
  apply integral_nonneg
  intro t
  positivity

theorem gaussian_shifted_moment_mean_limit_nonneg (z : ℂ) (k : ℕ) :
    0 ≤ (gaussianShiftedMomentMeanLimit z k).re := by
  exact ge_of_tendsto (gaussian_shifted_even_moment_mean_tendsto z k)
    (Filter.Eventually.of_forall (fun n => gaussian_shifted_even_moment_mean_nonneg n z k))

theorem gaussian_shifted_trace_mean_eq_real (n : ℕ) (z : ℂ) (k : ℕ) :
    gaussianShiftedTraceMean n z k = ((gaussianShiftedTraceMean n z k).re : ℂ) := by
  rw [← gaussian_shifted_even_moment_mean_eq_trace_mean n z k]
  simp only [gaussianShiftedTraceMean, gaussian_shifted_singular_even_moment_trace]
  have hPoint (x : GaussianSquareSample n) :
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace =
        (((normalizedShiftedGaussianMatrix z x *
          (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace.re : ℂ) :=
    hermitian_trace_pow_eq_ofReal_re _ (Matrix.isHermitian_mul_conjTranspose_self _) k
  have hFun : (fun x : GaussianSquareSample n =>
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace / (n : ℂ)) =
      fun x => Complex.ofReal (((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace.re / (n : ℝ)) := by
    funext x
    calc
      _ = (((normalizedShiftedGaussianMatrix z x *
          (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace.re : ℂ) / (n : ℂ) :=
        congrArg (fun t : ℂ => t / (n : ℂ)) (hPoint x)
      _ = _ := by simp only [← Complex.ofReal_natCast, Complex.ofReal_div]
  rw [hFun, integral_complex_ofReal]

theorem gaussian_shifted_moment_mean_limit_im_zero (z : ℂ) (k : ℕ) :
    (gaussianShiftedMomentMeanLimit z k).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (gaussian_shifted_trace_mean_tendsto z k)
  have hZero (n : ℕ) : (gaussianShiftedTraceMean n z k).im = 0 := by
    rw [gaussian_shifted_trace_mean_eq_real n z k, Complex.ofReal_im]
  change Tendsto (fun n : ℕ => (gaussianShiftedTraceMean n z k).im) atTop
    (𝓝 (gaussianShiftedMomentMeanLimit z k).im) at h
  have h' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (gaussianShiftedMomentMeanLimit z k).im) :=
    h.congr' (Filter.Eventually.of_forall hZero)
  exact tendsto_nhds_unique h' tendsto_const_nhds

end CircularLaw
