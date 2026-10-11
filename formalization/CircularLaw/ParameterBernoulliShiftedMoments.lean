import CircularLaw.ParameterBernoulliWordConcentration

/-!
# Actual shifted singular moments for arbitrary Bernoulli parameters

Finite scalar-shift expansion assembles the real word traces. Their
Gaussian limits give every actual centered shifted even singular moment,
for any growing dimension and sparse real effective degree.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix NNReal Topology

namespace CircularLaw

theorem parameter_bernoulli_normalized_word_trace_eq_real {n : ℕ}
    (p : ℝ≥0) (w : List Bool) (x : BernoulliSquareSample n) :
    (matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) w).trace =
      ((matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) w).trace.re : ℂ) := by
  unfold parameterNormalizedCenteredBernoulliMatrix
  simp only [← Complex.ofReal_inv, matrix_adjoint_word_smul, matrix_word_scale_ofReal,
    Matrix.trace_smul, smul_eq_mul]
  rw [bernoulli_centered_word_trace_eq_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.ofReal_mul]

def parameterBernoulliCenteredShiftedSingularMoment {n : ℕ} (p : ℝ≥0) (z : ℂ) (k : ℕ)
    (x : BernoulliSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ (2 * k)
    ∂squareSingularMeasure (parameterNormalizedCenteredBernoulliMatrix p x - z • 1)

theorem parameter_bernoulli_centered_shifted_moment_word_sum {n : ℕ}
    (p : ℝ≥0) (z : ℂ) (k : ℕ) (x : BernoulliSquareSample n) :
    parameterBernoulliCenteredShiftedSingularMoment p z k x =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun a => a.1.re * parameterBernoulliWordTrace p a.2 x)).sum := by
  have hIm (w : List Bool) :
      (matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) w).trace.im = 0 := by
    rw [parameter_bernoulli_normalized_word_trace_eq_real]
    rfl
  have hList (L : List (ℂ × List Bool)) :
      ((L.map (fun a => a.1 *
        (matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) a.2).trace)).sum).re / n =
          (L.map (fun a => a.1.re * parameterBernoulliWordTrace p a.2 x)).sum := by
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, Complex.add_re, add_div, ih,
        Complex.mul_re, hIm, mul_zero, sub_zero, parameterBernoulliWordTrace]
      ring
  rw [parameterBernoulliCenteredShiftedSingularMoment, square_singular_measure_even_moment,
    matrix_shifted_gram_pow_word, matrix_scalar_shifted_word_expansion, Matrix.trace_list_sum]
  simp only [List.map_map]
  change ((List.map (fun a =>
    (a.1 • matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) a.2).trace)
      (scalarShiftWordExpansion z (gramMatrixWord k))).sum).re / n = _
  simp only [Matrix.trace_smul, smul_eq_mul]
  exact hList _

theorem gaussian_shifted_moment_limit_real_word_sum (z : ℂ) (k : ℕ) :
    (gaussianShiftedMomentMeanLimit z k).re =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun a => a.1.re * (gaussianWordMeanCount a.2 : ℝ))).sum := by
  rw [← bernoulli_shifted_moment_mean_limit_eq_gaussian, bernoulli_shifted_moment_limit_real_word_sum]
  simp only [bernoulli_word_mean_limit_eq_gaussian]

theorem parameter_bernoulli_weighted_words_converge (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (L : List (ℂ × List Bool)) :
    VaryingConvergesInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n x => (L.map (fun a => a.1.re * parameterBernoulliWordTrace (p n) a.2 x)).sum)
      (L.map (fun a => a.1.re * (gaussianWordMeanCount a.2 : ℝ))).sum := by
  induction L with
  | nil => simpa only [List.map_nil, List.sum_nil] using
      varying_probability_const (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n)) 0
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact varying_probability_add _
      (varying_probability_mul_deterministic _
        (parameter_bernoulli_word_converges_in_probability q p hp hQ hDegree hSparse a.2)
        tendsto_const_nhds) ih

theorem parameter_bernoulli_centered_shifted_moment_converges (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    VaryingConvergesInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n => parameterBernoulliCenteredShiftedSingularMoment (p n) z k)
      (gaussianShiftedMomentMeanLimit z k).re := by
  have hFun : (fun n => parameterBernoulliCenteredShiftedSingularMoment (n := q n) (p n) z k) =
      (fun n (x : BernoulliSquareSample (q n)) =>
        ((scalarShiftWordExpansion z (gramMatrixWord k)).map
          (fun a => a.1.re * parameterBernoulliWordTrace (p n) a.2 x)).sum) := by
    funext n x
    exact parameter_bernoulli_centered_shifted_moment_word_sum (p n) z k x
  rw [hFun, gaussian_shifted_moment_limit_real_word_sum]
  exact parameter_bernoulli_weighted_words_converge q p hp hQ hDegree hSparse
    (scalarShiftWordExpansion z (gramMatrixWord k))

end CircularLaw
