import CircularLaw.ParameterBernoulliWordCovariance

/-!
# Actual word concentration for arbitrary sparse Bernoulli parameters

The exact centered-square identity combines the checked mean limit and
vanishing covariance. Dimensions may vary independently of the sequence
index, and effective degrees are real.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem parameter_bernoulli_word_square_error_integral (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (w : List Bool) (a : ℝ) :
    (∫ x, (parameterBernoulliWordTrace p w x - a) ^ 2 ∂bernoulliSquareMatrixLaw n p hp) =
      parameterBernoulliWordCovariance n p hp w w +
        (parameterBernoulliWordMean n p hp w - a) ^ 2 := by
  rw [integral_centered_square_real _ _ Integrable.of_finite Integrable.of_finite]
  unfold parameterBernoulliWordCovariance parameterBernoulliWordMean
  simp only [pow_two]
  ring

theorem parameter_bernoulli_word_mean_square_tendsto (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => ∫ x,
      (parameterBernoulliWordTrace (p n) w x - (gaussianWordMeanCount w : ℝ)) ^ 2
        ∂bernoulliSquareMatrixLaw (q n) (p n) (hp n)) atTop (𝓝 0) := by
  simp only [parameter_bernoulli_word_square_error_integral]
  have hMean := ((parameter_bernoulli_all_word_mean_tendsto q p hp hQ hDegree hSparse w).sub_const
    (gaussianWordMeanCount w : ℝ)).pow 2
  have h := (parameter_bernoulli_all_word_covariance_tendsto_zero q p hp hQ hDegree w w).add hMean
  simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero] using h

theorem parameter_bernoulli_word_converges_in_probability (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (w : List Bool) :
    VaryingConvergesInProbability (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
      (fun n => parameterBernoulliWordTrace (p n) w) (gaussianWordMeanCount w : ℝ) :=
  varying_probability_of_mean_square (fun n => bernoulliSquareMatrixLaw (q n) (p n) (hp n))
    (fun n => parameterBernoulliWordTrace (p n) w) (gaussianWordMeanCount w : ℝ)
    (fun _ => Integrable.of_finite)
    (parameter_bernoulli_word_mean_square_tendsto q p hp hQ hDegree hSparse w)

end CircularLaw
