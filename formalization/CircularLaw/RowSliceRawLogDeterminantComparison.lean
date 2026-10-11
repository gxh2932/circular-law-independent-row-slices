import CircularLaw.PrefixDeterminantErrorProbability

/-!
# Actual raw determinant comparison in the two manuscript regimes

The lower-band proof uses the proved fixed-shift intermediate theorem.
Both conclusions assemble row replacement, removal of regularization and
the actual logarithmic tails. The joint minimum failure limit is the
remaining explicit input; neither conclusion claims that imported estimate.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem lower_band_raw_log_det_comparison_of_minimum_failure :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ C : ℝ, Cstar ≤ C →
      ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ CL : ℝ, 0 ≤ CL →
        ∀ d : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) →
          SparseDegrees d → ∀ z : ℂ, z ≠ 0 →
            Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
              (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
                (lowerHermitizationCutoff n CL))) atTop (𝓝 0) →
            VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
              (fun n => independentSquareLogDeterminantDifference n (d n) z) 0 := by
  obtain ⟨Cstar, R, Cq, B, hCstar, hR, _hCq, _hB, hUniform⟩ :=
    fixed_shift_intermediate_singular_value_theorem
  refine ⟨Cstar, hCstar, ?_⟩
  intro C hC σ hσ0 hσ1 CL hCL d hBand hSparse z hz hMinBad
  have hCpos := hCstar.trans_le hC
  have hLower : LogLowerBound C d := hBand.mono (fun _ h => h.1)
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hCpos d hLower)
  have hτ : ∀ᶠ n : ℕ in atTop, 0 < lowerHermitizationCutoff n CL := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos hnR _
  have hRegularized := lower_cutoff_prefix_potential_comparison d hSparse hCpos hCL hLower z
  have hVolume := independent_prefix_volume_comparison_of_minimum_failure d (1 / 2)
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) (fun n => lowerHermitizationCutoff n CL)
    hτ hRegularized hMinBad
  have hSliceBottom := lower_row_slice_bottom_negative_log_converges hCpos hσ1.le hCL hR.le
    d hBand hSparse z hMinBad (hUniform C hC σ hσ0 hσ1 d hBand z).2
  exact independent_square_log_det_comparison_of_prefix_and_tails d hDegree hSparse
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) z
    (fun n => lowerHermitizationCutoff n CL) hτ hMinBad hVolume hSliceBottom
    (independent_bernoulli_bottom_negative_log_converges d hDegree hSparse z hz
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))

theorem superlog_raw_log_det_comparison_of_minimum_failure (d : ℕ → ℕ)
    (hSparse : SparseDegrees d) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ))
    (z : ℂ) (hz : z ≠ 0)
    (hMinBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
        (polynomialHermitizationCutoff n B))) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSquareLogDeterminantDifference n (d n) z) 0 := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound zero_lt_one d
      (log_lower_bound_of_superlog_degree d hε.le hLower))
  obtain ⟨ha, haOne⟩ := superlog_hermitization_exponent_range hε
  have hτ : ∀ᶠ n : ℕ in atTop, 0 < polynomialHermitizationCutoff n B := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos hnR _
  have hRegularized := superlog_cutoff_prefix_potential_comparison d hSparse hB hε hLower z
  have hVolume := independent_prefix_volume_comparison_of_minimum_failure d
    (superlogHermitizationExponent ε) (fun n => z * (Real.sqrt (d n : ℝ) : ℂ))
    (fun n => polynomialHermitizationCutoff n B) hτ hRegularized hMinBad
  exact independent_square_log_det_comparison_of_prefix_and_tails d hDegree hSparse ha haOne.le z
    (fun n => polynomialHermitizationCutoff n B) hτ hMinBad hVolume
    (superlog_row_slice_bottom_negative_log_converges d hSparse hB hε hLower z hMinBad)
    (independent_bernoulli_bottom_negative_log_converges d hDegree hSparse z hz ha haOne.le)

end CircularLaw
