import CircularLaw.LLYSourceMinimumRegimes
import CircularLaw.SmallestSingularFailureTransfer

/-!
# Row-slice minimum failure tends to zero in both manuscript regimes

These are actual law probabilities for arbitrary sparse degree sequences
and every fixed complex shift. All row-slice minimum inputs are supplied;
the corresponding Bernoulli minimum limit remains separate.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem eventually_twice_degree_le_of_sparse (d : ℕ → ℕ) (hSparse : SparseDegrees d) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 2 * d n ≤ n := by
  have hHalf : ∀ᶠ n : ℕ in atTop, (d n : ℝ) / n < 1 / 2 :=
    hSparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 1, hHalf] with n hn hHalf
  have hnPos : 0 < n := by omega
  have h := (div_lt_iff₀ (by exact_mod_cast hnPos : (0 : ℝ) < n)).mp hHalf
  refine ⟨hnPos, ?_⟩
  exact_mod_cast (by nlinarith only [h] : (2 : ℝ) * d n ≤ n)

theorem row_slice_lower_minimum_probability_tendsto_zero (p : LLYSourceMinimumParameters)
    (d : ℕ → ℕ) (hSparse : SparseDegrees d) (hLower : LogLowerBound p.C d) (z : ℂ) :
    Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows)
        (lowerHermitizationCutoff n (2 * llySourceLoglogRatioConstant + 12))}) atTop (𝓝 0) := by
  have hC : 0 < p.C := by linarith only [p.degree]
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hC d hLower)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (inverse_sqrt_degree_error_tendsto_zero d hDegree (llySourceMinimumErrorConstant p))
  filter_upwards [eventually_lly_source_lower_cutoff_probability p, hLower,
    eventually_twice_degree_le_of_sparse d hSparse,
    eventually_fixed_shift_in_smallest_range d hDegree z] with n hProbability hLower hSize hShift
  simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real] using
    hProbability (d n) hLower hSize.2 (z * (Real.sqrt (d n : ℝ) : ℂ)) hShift

theorem row_slice_superlog_minimum_probability_tendsto_zero (p : LLYSourceMinimumParameters)
    (d : ℕ → ℕ) (hSparse : SparseDegrees d) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d n : ℝ)) (z : ℂ) :
    Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows)
        (polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12))}) atTop (𝓝 0) := by
  have hC : 0 < p.C := by linarith only [p.degree]
  have hLogLower : LogLowerBound p.C d := by
    filter_upwards [eventually_superlog_implies_any_log_degree p.C hε, hLower] with n hDegree hLower
    exact hDegree (d n) hLower
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hC d hLogLower)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (inverse_sqrt_degree_error_tendsto_zero d hDegree (llySourceMinimumErrorConstant p))
  filter_upwards [eventually_lly_source_superlog_probability p hε, hLower,
    eventually_twice_degree_le_of_sparse d hSparse,
    eventually_fixed_shift_in_smallest_range d hDegree z] with n hProbability hLower hSize hShift
  simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real] using
    hProbability (d n) hLower hSize.2 (z * (Real.sqrt (d n : ℝ) : ℂ)) hShift

end CircularLaw
