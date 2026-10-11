import CircularLaw.GaussianMomentVariance
import CircularLaw.VaryingMeanSquareConvergence

/-!
# All actual zero-shift Gaussian even moments converge in probability

Their means tend to the exact leading-permutation count and their
variances vanish. The centered square expectation around that limiting
count is the variance plus the squared mean error, and hence tends to
zero. `GaussianZeroCatalanMoments.lean` later identifies these counts;
`GaussianShiftedWeakLimit.lean` supplies the general shifted weak law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_zero_shift_moment_square_error_integral (n k : ℕ) (a : ℝ) :
    (∫ x, (gaussianZeroShiftSingularMoment k x - a) ^ 2 ∂gaussianSquareMatrixLaw n) =
      gaussianTwoTraceMixedContribution n k + (gaussianZeroShiftSingularMomentMean n k - a) ^ 2 := by
  rw [integral_centered_square_real _ _ (gaussian_zero_shift_moment_integrable n k)
    (gaussian_zero_shift_moment_square_integrable n k), gaussian_zero_shift_moment_square_integral]
  change gaussianZeroShiftSingularMomentMean n k ^ 2 + gaussianTwoTraceMixedContribution n k -
    2 * a * gaussianZeroShiftSingularMomentMean n k + a ^ 2 = _
  ring

theorem gaussian_zero_shift_moment_mean_square_converges (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x,
      (gaussianZeroShiftSingularMoment k x - (gaussianLeadingMomentCount k : ℝ)) ^ 2
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 0) := by
  simp only [gaussian_zero_shift_moment_square_error_integral]
  have hMean := ((gaussian_zero_shift_moment_mean_tendsto k).sub_const
    (gaussianLeadingMomentCount k : ℝ)).pow 2
  have h := (gaussian_two_trace_mixed_contribution_tendsto k).add hMean
  simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero] using h

theorem gaussian_zero_shift_moment_converges_in_probability (k : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianZeroShiftSingularMoment k) (gaussianLeadingMomentCount k : ℝ) :=
  varying_probability_of_mean_square gaussianSquareMatrixLaw
    (fun _ => gaussianZeroShiftSingularMoment k) (gaussianLeadingMomentCount k : ℝ)
    (fun n => gaussian_zero_shift_moment_centered_square_integrable n k _)
    (gaussian_zero_shift_moment_mean_square_converges k)

theorem gaussian_zero_shift_moment_centered_deviation_bound {n : ℕ} (hn : 0 < n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussianSquareMatrixLaw n).real
      {x | ε < |gaussianZeroShiftSingularMoment k x - gaussianZeroShiftSingularMomentMean n k|} ≤
      ((2 * (k + 1)).factorial : ℝ) / ((n : ℝ) * ε ^ 2) := by
  have h := mean_square_deviation_bound (gaussianSquareMatrixLaw n)
    (gaussianZeroShiftSingularMoment k) (gaussianZeroShiftSingularMomentMean n k)
    (gaussian_zero_shift_moment_centered_square_integrable n k _) hε
  exact (h.trans (div_le_div_of_nonneg_right (gaussian_zero_shift_moment_variance_bound hn k)
    (sq_nonneg ε))).trans_eq (div_div _ _ _)

theorem gaussian_leading_fourth_moment_count : gaussianLeadingMomentCount 1 = 2 := by
  have hMean : ∀ᶠ n : ℕ in atTop, gaussianZeroShiftSingularMomentMean n 1 = 2 :=
    (eventually_gt_atTop 0).mono (fun _ hn => gaussian_singular_fourth_moment_integral hn)
  have hLimit : Tendsto (fun n : ℕ => gaussianZeroShiftSingularMomentMean n 1) atTop (𝓝 2) :=
    (tendsto_congr' hMean).mpr tendsto_const_nhds
  have h := tendsto_nhds_unique (gaussian_zero_shift_moment_mean_tendsto 1) hLimit
  exact_mod_cast h

theorem gaussian_zero_shift_fourth_moment_converges_in_probability :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => ∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure 0 x) 2 := by
  have h := gaussian_zero_shift_moment_converges_in_probability 1
  rw [gaussian_leading_fourth_moment_count] at h
  exact h

end CircularLaw
