import CircularLaw.BernoulliAllWordMeanLimits
import CircularLaw.SquareSingularTraceMoments
import CircularLaw.MatrixGramShiftTrace

/-!
# All actual centered shifted Bernoulli singular-moment means

Every centered word trace is real. Its checked mean limit supplies the
finite scalar-shift expansion at every complex shift. Consequently
every actual even singular-moment mean has a finite nonnegative limit.
This is mean convergence under the actual sparse Bernoulli matrix law;
it does not assert concentration or identify the limit with the Gaussian
singular law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

theorem bernoulli_centered_word_trace_eq_real {n : ℕ} (p : ℝ≥0) (w : List Bool)
    (x : BernoulliSquareSample n) :
    (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) w).trace =
      ((matrixAdjointWord (bernoulliCenteredSquareMatrix p x) w).trace.re : ℂ) := by
  cases w with
  | nil => simp [matrixAdjointWord]
  | cons b w =>
    have h := bernoulli_centered_matrix_word_trace_expansion p w.length ((b :: w).get) x
    simp only [List.ofFn_get] at h
    rw [h, Complex.re_sum]
    simp only [Complex.ofReal_re, Complex.ofReal_sum]

theorem bernoulli_normalized_word_trace_eq_real {n : ℕ} (d : ℕ) (w : List Bool)
    (x : BernoulliSquareSample n) :
    (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace =
      ((matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace.re : ℂ) := by
  unfold normalizedCenteredBernoulliMatrix
  simp only [← Complex.ofReal_inv, matrix_adjoint_word_smul, matrix_word_scale_ofReal,
    Matrix.trace_smul, smul_eq_mul]
  rw [bernoulli_centered_word_trace_eq_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.ofReal_mul]

def bernoulliNormalizedWordComplexMean (n d : ℕ) (w : List Bool) : ℂ :=
  ∫ x, (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace / n
    ∂sparseBernoulliMatrixLaw n d

theorem bernoulli_normalized_word_complex_mean_eq_real (n d : ℕ) (w : List Bool) :
    bernoulliNormalizedWordComplexMean n d w = (bernoulliNormalizedWordMean n d w : ℂ) := by
  have hFun : (fun x : BernoulliSquareSample n =>
      (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace / (n : ℂ)) =
      fun x => Complex.ofReal
        ((matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace.re / (n : ℝ)) := by
    funext x
    rw [bernoulli_normalized_word_trace_eq_real]
    simp only [← Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_re]
  rw [bernoulliNormalizedWordComplexMean, hFun, integral_complex_ofReal]
  rfl

theorem bernoulli_all_word_complex_mean_tendsto (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => bernoulliNormalizedWordComplexMean n (d n) w) atTop
      (𝓝 (bernoulliWordMeanLimit w : ℂ)) := by
  simp only [bernoulli_normalized_word_complex_mean_eq_real]
  exact Complex.continuous_ofReal.tendsto _ |>.comp
    (bernoulli_all_word_mean_tendsto d hDegree hSparse w)

def bernoulliCenteredShiftedTraceMean (n d : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  ∫ x, (((normalizedCenteredBernoulliMatrix d x - z • 1) *
    (normalizedCenteredBernoulliMatrix d x - z • 1).conjTranspose) ^ k).trace / n
    ∂sparseBernoulliMatrixLaw n d

def bernoulliShiftedMomentMeanLimit (z : ℂ) (k : ℕ) : ℂ :=
  ((scalarShiftWordExpansion z (gramMatrixWord k)).map
    (fun q => q.1 * (bernoulliWordMeanLimit q.2 : ℂ))).sum

theorem bernoulli_shifted_trace_mean_eq_word_sum (n d : ℕ) (z : ℂ) (k : ℕ) :
    bernoulliCenteredShiftedTraceMean n d z k =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun q => q.1 * bernoulliNormalizedWordComplexMean n d q.2)).sum := by
  rw [bernoulliCenteredShiftedTraceMean, integral_div,
    bernoulli_centered_shifted_gram_trace_mean_expansion]
  simp only [div_eq_mul_inv]
  rw [← List.sum_map_mul_right]
  simp only [mul_assoc, bernoulliNormalizedWordComplexMean, integral_mul_const, div_eq_mul_inv]

theorem bernoulli_shifted_trace_mean_tendsto (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    Tendsto (fun n => bernoulliCenteredShiftedTraceMean n (d n) z k) atTop
      (𝓝 (bernoulliShiftedMomentMeanLimit z k)) := by
  simp only [bernoulli_shifted_trace_mean_eq_word_sum, bernoulliShiftedMomentMeanLimit]
  exact finite_list_sum_tendsto _ _ _ atTop (fun q _ =>
    tendsto_const_nhds.mul (bernoulli_all_word_complex_mean_tendsto d hDegree hSparse q.2))

theorem bernoulli_centered_shifted_even_moment_mean_eq_trace_mean (n d : ℕ)
    (z : ℂ) (k : ℕ) :
    (∫ x, (∫ t, (t : ℝ) ^ (2 * k)
      ∂squareSingularMeasure (normalizedCenteredBernoulliMatrix d x - z • 1))
        ∂sparseBernoulliMatrixLaw n d) = (bernoulliCenteredShiftedTraceMean n d z k).re := by
  simp only [square_singular_measure_even_moment, bernoulliCenteredShiftedTraceMean]
  rw [integral_div]
  change (∫ x, RCLike.re (((normalizedCenteredBernoulliMatrix d x - z • 1) *
      (normalizedCenteredBernoulliMatrix d x - z • 1).conjTranspose) ^ k).trace
    ∂sparseBernoulliMatrixLaw n d) / n = _
  rw [integral_re Integrable.of_finite, integral_div]
  simp only [← Complex.ofReal_natCast, Complex.div_ofReal_re]
  rfl

theorem bernoulli_centered_shifted_even_moment_mean_tendsto (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    Tendsto (fun n => ∫ x, (∫ t, (t : ℝ) ^ (2 * k)
      ∂squareSingularMeasure (normalizedCenteredBernoulliMatrix (d n) x - z • 1))
        ∂sparseBernoulliMatrixLaw n (d n)) atTop (𝓝 (bernoulliShiftedMomentMeanLimit z k).re) := by
  simp only [bernoulli_centered_shifted_even_moment_mean_eq_trace_mean]
  exact Complex.continuous_re.tendsto _ |>.comp
    (bernoulli_shifted_trace_mean_tendsto d hDegree hSparse z k)

theorem bernoulli_centered_shifted_even_moment_mean_nonneg (n d : ℕ) (z : ℂ) (k : ℕ) :
    0 ≤ ∫ x, (∫ t, (t : ℝ) ^ (2 * k)
      ∂squareSingularMeasure (normalizedCenteredBernoulliMatrix d x - z • 1))
        ∂sparseBernoulliMatrixLaw n d := by
  apply integral_nonneg
  intro x
  apply integral_nonneg
  intro t
  positivity

theorem bernoulli_shifted_moment_mean_limit_nonneg (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    0 ≤ (bernoulliShiftedMomentMeanLimit z k).re :=
  ge_of_tendsto (bernoulli_centered_shifted_even_moment_mean_tendsto d hDegree hSparse z k)
    (Eventually.of_forall (fun n => bernoulli_centered_shifted_even_moment_mean_nonneg n (d n) z k))

theorem bernoulli_shifted_moment_mean_limit_zero (z : ℂ) :
    bernoulliShiftedMomentMeanLimit z 0 = 1 := by
  simp [bernoulliShiftedMomentMeanLimit, gramMatrixWord, scalarShiftWordExpansion,
    bernoulliWordMeanLimit]

end CircularLaw
