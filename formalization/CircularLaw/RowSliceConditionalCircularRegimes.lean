import CircularLaw.RowSliceCircularFromLogLimit
import CircularLaw.DegreeRates

/-!
# The two circular-law deductions with their minimum estimate explicit

Every replacement, logarithmic-tail, comparator, energy and normalization
input is discharged here. The lower-band constant is independent of
sigma. Only the actual joint minimum failure limits remain hypotheses;
these deductions are not proofs of the imported estimates or the named
unconditional manuscript conclusions.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem sparse_degrees_of_log_power_upper (d : ℕ → ℕ) (b : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) b) :
    SparseDegrees d := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
    (hUpper.mono (fun n hn => div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)))
    (log_power_div_self_tendsto_zero b)

theorem lower_band_circular_law_of_minimum_failure :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ C : ℝ, Cstar ≤ C →
      ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ d : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) →
        (∀ z : ℂ, z ≠ 0 → ∃ CL : ℝ, 0 ≤ CL ∧
          Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
            (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
              (lowerHermitizationCutoff n CL))) atTop (𝓝 0)) →
        CircularConvergence d := by
  obtain ⟨Cstar, hCstar, hRawUniform⟩ := lower_band_raw_log_det_comparison_of_minimum_failure
  refine ⟨Cstar, hCstar, ?_⟩
  intro C hC σ hσ0 hσ1 d hBand hMinimum
  have hCpos := hCstar.trans_le hC
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hCpos d (hBand.mono (fun _ h => h.1)))
  have hSparse := sparse_degrees_of_log_power_upper d (1 + σ) (hBand.mono (fun _ h => h.2))
  apply row_slice_variance_circular_convergence_of_log_limit d hDegree hSparse
  filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with z hz
  obtain ⟨CL, hCL, hMinBad⟩ := hMinimum z hz
  have hτ : ∀ᶠ n : ℕ in atTop, 0 < lowerHermitizationCutoff n CL := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos hnR _
  exact row_slice_log_determinant_converges_of_independent_comparison d hDegree hSparse z hz
    (independent_normalized_log_det_comparison_of_raw d hDegree hSparse z
      (fun n => lowerHermitizationCutoff n CL) hτ hMinBad
      (hRawUniform C hC σ hσ0 hσ1 CL hCL d hBand hSparse z hz hMinBad))

theorem superlog_circular_law_of_minimum_failure (d : ℕ → ℕ)
    (hSparse : SparseDegrees d) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ))
    (hMinimum : ∀ z : ℂ, z ≠ 0 → ∃ B : ℝ, 0 ≤ B ∧
      Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
        (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
          (polynomialHermitizationCutoff n B))) atTop (𝓝 0)) :
    CircularConvergence d := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound zero_lt_one d
      (log_lower_bound_of_superlog_degree d hε.le hLower))
  apply row_slice_variance_circular_convergence_of_log_limit d hDegree hSparse
  filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with z hz
  obtain ⟨B, hB, hMinBad⟩ := hMinimum z hz
  have hτ : ∀ᶠ n : ℕ in atTop, 0 < polynomialHermitizationCutoff n B := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos hnR _
  exact row_slice_log_determinant_converges_of_independent_comparison d hDegree hSparse z hz
    (independent_normalized_log_det_comparison_of_raw d hDegree hSparse z
      (fun n => polynomialHermitizationCutoff n B) hτ hMinBad
      (superlog_raw_log_det_comparison_of_minimum_failure d hSparse hB hε hLower z hz hMinBad))

end CircularLaw
