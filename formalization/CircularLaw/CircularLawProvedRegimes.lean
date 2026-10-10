import CircularLaw.SliceMinimumDeterminantComparison
import CircularLaw.SliceMinimumLogTails
import CircularLaw.CompletedDegreeRegimes

/-!
# The two circular-law regimes and the main theorem

All minimum, replacement, logarithmic-tail, comparator, normalization and
assembly inputs are proved. Bernoulli logarithmic tails remove its ridge
and its full-log limit controls determinant zeros. The separate quantitative
joint minimum estimates remain distinct manuscript obligations.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem row_slice_log_limit_of_slice_minimum_prefix_and_tails (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (z : ℂ) (hz : z ≠ 0)
    (τ : ℕ → ℝ) (hτ : ∀ᶠ n : ℕ in atTop, 0 < τ n)
    (hRidge : Tendsto (fun n : ℕ => τ n / n) atTop (𝓝 0))
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (τ n)}) atTop (𝓝 0))
    (hRegularized : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) a
        (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n / n)) 0)
    (hSliceBottom : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) a z) 0) :
    VaryingConvergesInProbability (fun n => rowSliceMatrixLaw n (d n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z) := by
  have hVolume := independent_prefix_volume_comparison_of_slice_minimum
    d hDegree hSparse a z hz τ hτ hRidge hRegularized hMin
  have hZero := independent_square_det_zero_probability_of_slice_minimum
    d hDegree hSparse z hz τ hτ hMin
  have hRaw := independent_square_log_det_comparison_of_prefix_and_tails_and_zero_probability
    d hDegree hSparse ha haOne z hZero hVolume hSliceBottom
    (independent_bernoulli_bottom_negative_log_converges d hDegree hSparse z hz ha haOne)
  exact row_slice_log_determinant_converges_of_independent_comparison d hDegree hSparse z hz
    (independent_normalized_log_det_comparison_of_raw_and_zero_probability d hDegree hSparse z hZero hRaw)

theorem lower_band_log_determinant_converges :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ C : ℝ, Cstar ≤ C →
      ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ d : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) → SparseDegrees d →
          ∀ z : ℂ, z ≠ 0 → VaryingConvergesInProbability
            (fun n => rowSliceMatrixLaw n (d n))
            (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z)
            (circularLogPotential z) := by
  obtain ⟨p⟩ := lly_source_minimum_parameters_nonempty
  obtain ⟨Ci, R, Cq, B, hCi, hR, _hCq, _hB, hUniform⟩ :=
    fixed_shift_intermediate_singular_value_theorem
  refine ⟨max p.C Ci, hCi.trans_le (le_max_right _ _), ?_⟩
  intro C hC σ hσ0 hσ1 d hBand hSparse z hz
  have hCiC : Ci ≤ C := (le_max_right _ _).trans hC
  have hpC : p.C ≤ C := (le_max_left _ _).trans hC
  have hCpos : 0 < C := hCi.trans_le hCiC
  have hLower : LogLowerBound C d := hBand.mono (fun _ h => h.1)
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hCpos d hLower)
  have hpLower : LogLowerBound p.C d := by
    have hLog : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact Real.log_nonneg (by exact_mod_cast hn)
    filter_upwards [hLower, hLog] with n hLowerN hLogN
    exact (mul_le_mul_of_nonneg_right hpC hLogN).trans hLowerN
  let CL : ℝ := 2 * llySourceLoglogRatioConstant + 12
  have hCL : 0 ≤ CL := by
    dsimp only [CL]
    linarith only [lly_source_loglog_ratio_constant_ge_eight]
  have hMin := row_slice_lower_minimum_probability_tendsto_zero p d hSparse hpLower z
  have hSliceBottom := lower_row_slice_bottom_negative_log_converges_of_slice_minimum
    hCpos hσ1.le hCL hR.le d hBand hSparse z hMin
    (hUniform C hCiC σ hσ0 hσ1 d hBand z).2
  exact row_slice_log_limit_of_slice_minimum_prefix_and_tails d hDegree hSparse
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) z hz
    (fun n => lowerHermitizationCutoff n CL)
    ((eventually_lower_hermitization_cutoff_bounds hCL).mono (fun _ h => h.1))
    (lower_hermitization_ridge_tendsto_zero hCL) hMin
    (lower_cutoff_prefix_potential_comparison d hSparse hCpos hCL hLower z) hSliceBottom

theorem superlog_log_determinant_converges (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ))
    (z : ℂ) (hz : z ≠ 0) :
    VaryingConvergesInProbability (fun n => rowSliceMatrixLaw n (d n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z) := by
  obtain ⟨p⟩ := lly_source_minimum_parameters_nonempty
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound zero_lt_one d
      (log_lower_bound_of_superlog_degree d hε.le hLower))
  let B : ℝ := 2 * (8 * (1 + ε) / ε) + 12
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hMin := row_slice_superlog_minimum_probability_tendsto_zero p d hSparse hε hLower z
  obtain ⟨ha, haOne⟩ := superlog_hermitization_exponent_range hε
  exact row_slice_log_limit_of_slice_minimum_prefix_and_tails d hDegree hSparse ha haOne.le z hz
    (fun n => polynomialHermitizationCutoff n B)
    ((eventually_polynomial_hermitization_cutoff_bounds hB).mono (fun _ h => h.1))
    (polynomial_hermitization_ridge_tendsto_zero hB) hMin
    (superlog_cutoff_prefix_potential_comparison d hSparse hB hε hLower z)
    (superlog_row_slice_bottom_negative_log_converges_of_slice_minimum d hSparse hB hε hLower z hMin)

theorem lower_band_circular_law_uniform :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ C : ℝ, Cstar ≤ C →
      ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ d : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) → CircularConvergence d := by
  obtain ⟨Cstar, hCstar, hLog⟩ := lower_band_log_determinant_converges
  refine ⟨Cstar, hCstar, ?_⟩
  intro C hC σ hσ0 hσ1 d hBand
  have hCpos := hCstar.trans_le hC
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hCpos d (hBand.mono (fun _ h => h.1)))
  have hSparse := sparse_degrees_of_log_power_upper d (1 + σ) (hBand.mono (fun _ h => h.2))
  apply row_slice_variance_circular_convergence_of_log_limit d hDegree hSparse
  filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with z hz
  exact hLog C hC σ hσ0 hσ1 d hBand hSparse z hz

theorem superlog_circular_law (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) :
    CircularConvergence d := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound zero_lt_one d
      (log_lower_bound_of_superlog_degree d hε.le hLower))
  apply row_slice_variance_circular_convergence_of_log_limit d hDegree hSparse
  filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with z hz
  exact superlog_log_determinant_converges d hSparse hε hLower z hz

/-- The literal lower-band circular-law conclusion with one absolute constant
independent of sigma. The degree assumptions hold eventually. -/
def LowerBandCircularLawTheorem : Prop :=
  ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ d : ℕ → ℕ,
    (∀ᶠ n : ℕ in atTop, InLowerBand Cstar σ n (d n)) → CircularConvergence d

theorem lower_band_circular_law_theorem : LowerBandCircularLawTheorem := by
  obtain ⟨Cstar, hCstar, hUniform⟩ := lower_band_circular_law_uniform
  exact ⟨Cstar, hCstar, hUniform Cstar le_rfl⟩

/-- The literal superlogarithmic bridge with variance normalization. -/
def SuperlogarithmicCircularLawTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ d : ℕ → ℕ, SparseDegrees d →
    (∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) → CircularConvergence d

theorem superlogarithmic_circular_law_theorem : SuperlogarithmicCircularLawTheorem := by
  intro ε hε d hSparse hLower
  exact superlog_circular_law d hSparse hε hLower

theorem main_circular_law_theorem : MainTheorem := by
  obtain ⟨Cstar, hCstar, hLow⟩ := lower_band_circular_law_uniform
  apply main_theorem_of_circular_regimes hCstar
  · intro d hBand
    exact hLow Cstar le_rfl (1 / 2) (by norm_num) (by norm_num) d hBand
  · intro d hSparse hLower
    apply superlog_circular_law d hSparse (ε := 1 / 2) (by norm_num)
    simpa only [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] using hLower

end CircularLaw
