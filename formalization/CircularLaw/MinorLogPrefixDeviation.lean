import CircularLaw.BernoulliPrincipalMinorSecondMoment
import CircularLaw.GaussianMinorUniformLogBounds
import CircularLaw.BernoulliLogSqueeze
import CircularLaw.EmpiricalPositivePrefixConvergence

/-!
# Signed logarithmic deviation of a retained principal-minor prefix

The actual prefix retains the ambient denominator. On explicit retained
small-value, clipped-mean and second-moment good events, its deviation is
bounded by the removed fraction, both clipped-mean errors, the positive
second-moment tail budget and limiting logarithmic clipping errors.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal BigOperators

namespace CircularLaw

theorem empirical_prefix_positive_clipped_mean_error {n ell : ℕ}
    (s : Fin n → ℝ≥0) (hElln : ell ≤ n) {T M : ℝ} (hT : 0 < T)
    (hMoment : empiricalNonnegativeMean s (fun t => (t : ℝ) ^ 2) ≤ M) :
    |empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog -
      empiricalNonnegativeMean s (clippedPositiveLog T)| ≤
        ((n - ell : ℕ) / (n : ℝ)) * T + 2 * M / T := by
  obtain ⟨hPrefixNonneg, hPrefixError⟩ := empirical_prefix_positive_log_error s hElln hT
  obtain ⟨hFullNonneg, hFullError⟩ := empirical_positive_log_excess_bounds s hT
  have hScale := mul_le_mul_of_nonneg_left hMoment (by positivity : (0 : ℝ) ≤ 1 / T)
  have hTriangle := abs_sub_le (empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog)
    (empiricalNonnegativeMean s hermitizationPositiveLog)
    (empiricalNonnegativeMean s (clippedPositiveLog T))
  have hAbsPrefix : |empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog -
      empiricalNonnegativeMean s hermitizationPositiveLog| =
      empiricalNonnegativeMean s hermitizationPositiveLog -
        empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog := by
    rw [abs_sub_comm, abs_of_nonneg hPrefixNonneg]
  rw [hAbsPrefix, abs_of_nonneg hFullNonneg] at hTriangle
  have hEq : 2 * ((1 / T) * M) = 2 * M / T := by ring
  linarith

theorem empirical_prefix_signed_log_error {n ell : ℕ}
    (s : Fin n → ℝ≥0) (hElln : ell ≤ n) (ν : Measure ℝ≥0)
    (hν : FiniteLogarithmicIntegral ν) {Tn Tp M : ℝ}
    (hTn : 0 ≤ Tn) (hTp : 0 < Tp)
    (hGood : ¬empiricalPrefixHasSmall s ell (Real.exp (-Tn)))
    (hMoment : empiricalNonnegativeMean s (fun t => (t : ℝ) ^ 2) ≤ M) :
    |empiricalNonnegativePrefixMean s hElln (fun t => -Real.log (t : ℝ)) -
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν))| ≤
      ((n - ell : ℕ) / (n : ℝ)) * (Tn + Tp) + 2 * M / Tp +
      |empiricalNonnegativeMean s (clippedNegativeLog Tn) - ∫ t, clippedNegativeLog Tn t ∂ν| +
      |empiricalNonnegativeMean s (clippedPositiveLog Tp) - ∫ t, clippedPositiveLog Tp t ∂ν| +
      |(∫ t, clippedNegativeLog Tn t ∂ν) - ∫ t, hermitizationNegativeLog t ∂ν| +
      |(∫ t, clippedPositiveLog Tp t ∂ν) - ∫ t, hermitizationPositiveLog t ∂ν| := by
  have hNeg := empirical_prefix_negative_error s hElln hTn hGood
    (∫ t, clippedNegativeLog Tn t ∂ν) (∫ t, hermitizationNegativeLog t ∂ν)
  have hPosCompare := empirical_prefix_positive_clipped_mean_error s hElln hTp hMoment
  have hPosTriangle := abs_sub_le (empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog)
    (empiricalNonnegativeMean s (clippedPositiveLog Tp)) (∫ t, hermitizationPositiveLog t ∂ν)
  have hPosIntegral := abs_sub_le (empiricalNonnegativeMean s (clippedPositiveLog Tp))
    (∫ t, clippedPositiveLog Tp t ∂ν) (∫ t, hermitizationPositiveLog t ∂ν)
  have hFun : (fun t : ℝ≥0 => -Real.log (t : ℝ)) =
      fun t => hermitizationNegativeLog t - hermitizationPositiveLog t := by
    funext t
    have h := hermitization_log_decomposition t
    linarith
  have hLimit : -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) =
      (∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, hermitizationPositiveLog t ∂ν := by
    rw [hermitization_log_integral_decomposition hν.2]
    ring
  rw [hFun, empirical_prefix_mean_sub, hLimit]
  have hTriangle := abs_sub_le
    (empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog - ∫ t, hermitizationNegativeLog t ∂ν)
    0 (empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog - ∫ t, hermitizationPositiveLog t ∂ν)
  simp only [sub_zero, zero_sub, abs_neg] at hTriangle
  have hEq : (empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog -
      empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog) -
      ((∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, hermitizationPositiveLog t ∂ν) =
      (empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog - ∫ t, hermitizationNegativeLog t ∂ν) -
      (empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog - ∫ t, hermitizationPositiveLog t ∂ν) := by ring
  rw [← hEq] at hTriangle
  nlinarith

theorem bernoulli_minor_negative_log_prefix_eq_empirical (d : ℕ → ℕ) (z : ℂ)
    {epsilon : ℝ} (hNonneg : 0 ≤ epsilon) (n : ℕ) (x : BernoulliSquareSample n) :
    bernoulliMinorLogPrefixAt d z epsilon hNonneg n x =
      ((bernoulliSqueezeMinorDimension n epsilon : ℝ) / n) *
        empiricalNonnegativePrefixMean (bernoulliMinorSingularArray d z epsilon hNonneg n x)
          (bernoulli_squeeze_lengths_le hNonneg).1 (fun t => -Real.log (t : ℝ)) := by
  let m := bernoulliSqueezeMinorDimension n epsilon
  have hLengths := bernoulli_squeeze_lengths_le (n := n) hNonneg
  have hSum : (∑ j : Fin (bernoulliSqueezePrefixLength n epsilon),
      -Real.log ((bernoulliMinorSingularArray d z epsilon hNonneg n x (Fin.castLE hLengths.1 j)) : ℝ)) =
      ∑ j ∈ Finset.range (bernoulliSqueezePrefixLength n epsilon),
        squareNegativeLogAt (squarePrincipalMinor (normalizedShiftedBernoulliMatrix (d n) z x)
          hLengths.2) j := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [squareNegativeLogAt, dif_pos (lt_of_lt_of_le j.isLt hLengths.1)]
    rfl
  unfold bernoulliMinorLogPrefixAt squareMinorNegativeLogPrefix empiricalNonnegativePrefixMean
  rw [hSum]
  by_cases hm : m = 0
  · have hEll : bernoulliSqueezePrefixLength n epsilon = 0 := by dsimp [m] at hm; omega
    simp only [hEll, Finset.range_zero, Finset.sum_empty, zero_div, mul_zero]
  · have hn : n ≠ 0 := by intro hn; subst n; have h := hLengths.2; dsimp [m] at hm; omega
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    change _ / (n : ℝ) = ((m : ℝ) / n) * (_ / m)
    field_simp

theorem bernoulli_minor_prefix_good_event_log_bound (d : ℕ → ℕ) (z : ℂ)
    {epsilon : ℝ} (hNonneg : 0 ≤ epsilon) (hHalf : epsilon ≤ 1 / 2)
    (n : ℕ) (x : BernoulliSquareSample n) {Tn Tp M delta : ℝ}
    (hTn : 0 ≤ Tn) (hTp : 0 < Tp) (hTpSupport : Real.log (128 + ‖z‖) ≤ Tp)
    (hGood : ¬empiricalPrefixHasSmall (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (bernoulliSqueezePrefixLength n epsilon) (Real.exp (-Tn)))
    (hMoment : empiricalNonnegativeMean (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (fun t => (t : ℝ) ^ 2) ≤ M)
    (hNegative : |empiricalNonnegativeMean (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (clippedNegativeLog Tn) - ∫ t, clippedNegativeLog Tn t ∂gaussianMinorSingularLimit (1 - epsilon) z| ≤ delta)
    (hPositive : |empiricalNonnegativeMean (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (clippedPositiveLog Tp) - ∫ t, clippedPositiveLog Tp t ∂gaussianMinorSingularLimit (1 - epsilon) z| ≤ delta) :
    |bernoulliMinorLogPrefixAt d z epsilon hNonneg n x -
      ((bernoulliSqueezeMinorDimension n epsilon : ℝ) / n) *
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (1 - epsilon) z))| ≤
      ((bernoulliSqueezeMinorDimension n epsilon - bernoulliSqueezePrefixLength n epsilon : ℕ) /
        (bernoulliSqueezeMinorDimension n epsilon : ℝ)) * (Tn + Tp) +
        2 * M / Tp + 2 * delta + 192 * Real.exp (-Tn / 2) := by
  have hTheta : 0 < 1 - epsilon := by linarith
  have hBound := empirical_prefix_signed_log_error
    (bernoulliMinorSingularArray d z epsilon hNonneg n x)
    (bernoulli_squeeze_lengths_le hNonneg).1 (gaussianMinorSingularLimit (1 - epsilon) z)
    (gaussian_minor_limit_finite_logarithmic_integral hTheta z) hTn hTp hGood hMoment
  have hNegClip := gaussian_minor_limit_uniform_negative_clipping (by linarith : 1 / 2 ≤ 1 - epsilon) z hTn
  have hPosClip := gaussian_minor_limit_uniform_positive_clipping hTheta (by linarith : 1 - epsilon ≤ 1) z hTpSupport
  rw [hPosClip, sub_self, abs_zero] at hBound
  rw [hPosClip] at hPositive
  have hTotal : |empiricalNonnegativePrefixMean
      (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (bernoulli_squeeze_lengths_le hNonneg).1 (fun t => -Real.log (t : ℝ)) -
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (1 - epsilon) z))| ≤
      ((bernoulliSqueezeMinorDimension n epsilon - bernoulliSqueezePrefixLength n epsilon : ℕ) /
        (bernoulliSqueezeMinorDimension n epsilon : ℝ)) * (Tn + Tp) +
        2 * M / Tp + 2 * delta + 192 * Real.exp (-Tn / 2) := by
    linarith
  have hRatioNonneg : 0 ≤ (bernoulliSqueezeMinorDimension n epsilon : ℝ) / n := by positivity
  have hRatioOne : (bernoulliSqueezeMinorDimension n epsilon : ℝ) / n ≤ 1 := by
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero, zero_le_one]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n)).mpr
        (by exact_mod_cast (bernoulli_squeeze_lengths_le (n := n) hNonneg).2)
  rw [bernoulli_minor_negative_log_prefix_eq_empirical, ← mul_sub, abs_mul, abs_of_nonneg hRatioNonneg]
  have hScale := mul_le_mul_of_nonneg_right hRatioOne
    (abs_nonneg (empiricalNonnegativePrefixMean
      (bernoulliMinorSingularArray d z epsilon hNonneg n x)
      (bernoulli_squeeze_lengths_le hNonneg).1 (fun t => -Real.log (t : ℝ)) -
      (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (1 - epsilon) z))))
  simp only [one_mul] at hScale
  exact hScale.trans hTotal

end CircularLaw
