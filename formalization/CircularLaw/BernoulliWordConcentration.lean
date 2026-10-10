import CircularLaw.BernoulliNormalizedWordCovariance
import CircularLaw.GaussianMomentVariance
import CircularLaw.VaryingMeanSquareConvergence

/-!
# Actual Bernoulli word convergence in mean square and probability

The centered sparse Bernoulli trace covariance vanishes, and its mean
has the checked equality-pattern count as its limit. The exact square
error identity therefore gives mean-square convergence, hence actual
convergence in probability on the dimension-dependent sample spaces.
Gaussian identification of the count remains a separate obligation.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem bernoulli_word_square_error_integral (n d : ℕ) (w : List Bool) (a : ℝ) :
    (∫ x, (bernoulliNormalizedWordTrace d w x - a) ^ 2 ∂sparseBernoulliMatrixLaw n d) =
      bernoulliNormalizedWordCovariance n d w w +
        (bernoulliNormalizedWordMean n d w - a) ^ 2 := by
  rw [integral_centered_square_real _ _ Integrable.of_finite Integrable.of_finite]
  unfold bernoulliNormalizedWordCovariance
  have hMean : (∫ x, bernoulliNormalizedWordTrace d w x ∂sparseBernoulliMatrixLaw n d) =
      bernoulliNormalizedWordMean n d w := rfl
  rw [hMean]
  simp only [pow_two]
  ring

theorem bernoulli_word_mean_square_tendsto (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => ∫ x,
      (bernoulliNormalizedWordTrace (d n) w x - (bernoulliWordMeanLimit w : ℝ)) ^ 2
        ∂sparseBernoulliMatrixLaw n (d n)) atTop (𝓝 0) := by
  simp only [bernoulli_word_square_error_integral]
  have hMean := ((bernoulli_all_word_mean_tendsto d hDegree hSparse w).sub_const
    (bernoulliWordMeanLimit w : ℝ)).pow 2
  have h := (bernoulli_all_word_covariance_tendsto_zero d hDegree hSparse w w).add hMean
  simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero] using h

theorem bernoulli_word_converges_in_probability (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => bernoulliNormalizedWordTrace (d n) w) (bernoulliWordMeanLimit w : ℝ) :=
  varying_probability_of_mean_square (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun n => bernoulliNormalizedWordTrace (d n) w) (bernoulliWordMeanLimit w : ℝ)
    (fun _ => Integrable.of_finite) (bernoulli_word_mean_square_tendsto d hDegree hSparse w)

end CircularLaw
