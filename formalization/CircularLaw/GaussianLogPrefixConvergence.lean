import CircularLaw.GaussianLogTailReduction
import CircularLaw.EmpiricalFullLogPrefixConvergence
import CircularLaw.SquareLogPrefixComparison
import CircularLaw.VaryingProbabilitySqueeze

/-!
# Actual Gaussian logarithmic prefixes omitting any vanishing fraction

Every deterministic `ell <= n` with `(n-ell)/n -> 0` has the full
logarithmic limit. The literal square-matrix prefix uses denominator n
and the manuscript's negative sign. Its zero event is null in every
positive dimension. The exact manuscript floor is a special case.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace CircularLaw

theorem gaussian_prefix_log_mean_converges (z : ℂ) (ell : ℕ → ℕ)
    (hElln : ∀ n, ell n ≤ n)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => empiricalNonnegativePrefixMean (gaussianSingularArray z n x) (hElln n)
        (fun t => Real.log (t : ℝ)))
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z) :=
  empirical_prefix_log_convergence_of_full gaussianSquareMatrixLaw (gaussianSingularArray z)
    (gaussianShiftedSingularLimit z) ell hElln (gaussian_shifted_weak_convergence z)
    (gaussian_empirical_log_convergence z) (gaussian_shifted_limit_finite_logarithmic_integral z)
    hRemoved (gaussian_empirical_second_moment_bounded z)

theorem empirical_negative_log_prefix_eq_square {n ell : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hElln : ell ≤ n) :
    empiricalNonnegativePrefixMean (squareSingularValuesNNReal A) hElln
      (fun t => -Real.log (t : ℝ)) = squareNegativeLogPrefix A ell := by
  unfold empiricalNonnegativePrefixMean squareNegativeLogPrefix
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [squareNegativeLogAt, dif_pos (lt_of_lt_of_le j.isLt hElln)]
  rfl

theorem gaussian_square_negative_log_prefix_converges (z : ℂ) (ell : ℕ → ℕ)
    (hElln : ∀ n, ell n ≤ n)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x) (ell n))
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z)) := by
  have h := varying_probability_neg gaussianSquareMatrixLaw
    (gaussian_prefix_log_mean_converges z ell hElln hRemoved)
  have hFun : (fun (n : ℕ) (x : GaussianSquareSample n) =>
      -empiricalNonnegativePrefixMean (gaussianSingularArray z n x) (hElln n)
        (fun t => Real.log (t : ℝ))) =
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x) (ell n)) := by
    funext n x
    rw [← empirical_negative_log_prefix_eq_square _ (hElln n)]
    simp only [gaussianSingularArray, empiricalNonnegativePrefixMean,
      Finset.sum_neg_distrib, neg_div]
  rw [hFun] at h
  exact h

theorem gaussian_prefix_zero_event_null {n : ℕ} (hn : 0 < n) (z : ℂ) (ell : ℕ) :
    gaussianSquareMatrixLaw n {x | empiricalPrefixHasZero (gaussianSingularArray z n x) ell} = 0 := by
  apply measure_mono_null _ (gaussian_empirical_zero_event_null hn z)
  rintro x ⟨j, _, hj⟩
  exact ⟨j, hj⟩

theorem gaussian_prefix_zero_probability_tendsto (z : ℂ) (ell : ℕ → ℕ) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real
      {x | empiricalPrefixHasZero (gaussianSingularArray z n x) (ell n)}) atTop (𝓝 0) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [measureReal_def, gaussian_prefix_zero_event_null hn z, ENNReal.toReal_zero]

theorem gaussian_rounded_negative_log_prefix_converges (z : ℂ) (epsilon : ℕ → ℝ)
    (hNonneg : ∀ n, 0 ≤ epsilon n) (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x)
        (bernoulliSqueezePrefixLength n (epsilon n)))
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z)) :=
  gaussian_square_negative_log_prefix_converges z
    (fun n => bernoulliSqueezePrefixLength n (epsilon n))
    (fun n => bernoulli_squeeze_prefix_le (hNonneg n))
    (bernoulli_squeeze_prefix_removed_fraction_tendsto hNonneg hEpsilon)

theorem gaussian_zero_square_negative_log_prefix_converges (ell : ℕ → ℕ)
    (hElln : ∀ n, ell n ≤ n)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix 0 x) (ell n))
      (1 / 2 : ℝ) := by
  have h := gaussian_square_negative_log_prefix_converges 0 ell hElln hRemoved
  simpa only [gaussian_zero_shift_log_integral_value, neg_neg] using h

end CircularLaw
