import CircularLaw.RowSliceRawLogDeterminantComparison
import CircularLaw.BernoulliCircularLaw
import CircularLaw.VarianceNormalizationTransfer

/-!
# Cancellation of the common determinant normalization

The actual degree-normalized shifted matrices are `1/sqrt(d)` times
the raw shifted matrices. Their logarithmic corrections cancel off the
joint minimum failure event. The checked Bernoulli limit then supplies
the actual row-slice normalized logarithmic limit. The imported minimum
failure estimate remains an explicit premise.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem square_log_norm_det_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {c : ℂ} (hc : c ≠ 0) (hDet : A.det ≠ 0) :
    Real.log ‖(c • A).det‖ = (n : ℝ) * Real.log ‖c‖ + Real.log ‖A.det‖ := by
  rw [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hc)) (norm_ne_zero_iff.mpr hDet),
    Real.log_pow]

theorem square_log_det_difference_smul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    Real.log ‖(c • A).det‖ - Real.log ‖(c • B).det‖ =
      Real.log ‖A.det‖ - Real.log ‖B.det‖ := by
  rw [square_log_norm_det_smul A hc hA, square_log_norm_det_smul B hc hB]
  ring

theorem degree_normalized_shift_eq_smul {n d : ℕ} (hd : 0 < d)
    (rows : RowSliceMatrix n d) (z : ℂ) :
    degreeNormalizedMatrix rows - z • 1 =
      (Real.sqrt (d : ℝ) : ℂ)⁻¹ • fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) rows := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hdR).ne'
  rw [degreeNormalizedMatrix, fullShiftedSliceMatrix, smul_sub, smul_smul]
  congr 1
  congr 1
  field_simp

theorem independent_normalized_log_det_difference_eq_raw {n d : ℕ} (hd : 0 < d)
    (z : ℂ) (samples : RowSliceMatrix n d × BernoulliSquareSample n)
    (hA : (fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) samples.1).det ≠ 0)
    (hB : (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1).det ≠ 0) :
    normalizedLogDeterminant (degreeNormalizedMatrix samples.1) z -
      normalizedLogDeterminant (degreeNormalizedBernoulliMatrix d samples.2) z =
      independentSquareLogDeterminantDifference n d z samples := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hdR).ne'
  have hBShift : degreeNormalizedBernoulliMatrix d samples.2 - z • 1 =
      (Real.sqrt (d : ℝ) : ℂ)⁻¹ •
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1) := by
    change normalizedShiftedBernoulliMatrix d z samples.2 = _
    rw [bernoulli_raw_shift_eq_sqrt_smul hd z samples.2,
      smul_smul, inv_mul_cancel₀ hRoot, one_smul]
  rw [normalizedLogDeterminant, normalizedLogDeterminant, degree_normalized_shift_eq_smul hd,
    hBShift, ← sub_div, square_log_det_difference_smul _ _ (inv_ne_zero hRoot) hA hB]
  rfl

theorem independent_normalized_log_det_comparison_of_raw (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (z : ℂ) (τ : ℕ → ℝ) (hτ : ∀ᶠ n in atTop, 0 < τ n)
    (hMinBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n))) atTop (𝓝 0))
    (hRaw : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSquareLogDeterminantDifference n (d n) z) 0) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => normalizedLogDeterminant (degreeNormalizedMatrix samples.1) z -
        normalizedLogDeterminant (degreeNormalizedBernoulliMatrix (d n) samples.2) z) 0 := by
  apply varying_probability_of_agreement_outside_bad_event
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n))
    hRaw hMinBad
  filter_upwards [hτ, eventually_valid_bernoulli_degrees hDegree hSparse] with n hτn hd
  intro samples hGood
  have hMin : (∀ j, τ n ≤ orderedSquareSingularValues
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) j) ∧
      (∀ j, τ n ≤ orderedSquareSingularValues
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) j) := not_not.mp hGood
  exact independent_normalized_log_det_difference_eq_raw hd.1 z samples
    (square_det_ne_zero_of_singular_lower_bound _ hτn hMin.1)
    (square_det_ne_zero_of_singular_lower_bound _ hτn hMin.2)

theorem row_slice_log_determinant_converges_of_independent_comparison (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    (hComparison : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => normalizedLogDeterminant (degreeNormalizedMatrix samples.1) z -
        normalizedLogDeterminant (degreeNormalizedBernoulliMatrix (d n) samples.2) z) 0) :
    VaryingConvergesInProbability (fun n => rowSliceMatrixLaw n (d n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z) := by
  have hBern := varying_bernoulli_probability_on_independent_coupling d hDegree hSparse
    (fun n x => normalizedLogDeterminant (degreeNormalizedBernoulliMatrix (d n) x) z)
    (circularLogPotential z) (bernoulli_log_determinant_converges_circular d z hDegree hSparse hz)
  have hCoupled := varying_probability_add (fun n => independentSquareComparisonLaw n (d n))
    hComparison hBern
  simp only [sub_add_cancel, zero_add] at hCoupled
  intro ε hε
  apply (hCoupled ε hε).congr'
  apply Eventually.of_forall
  intro n
  exact independent_square_slice_event_real n (d n)
    (fun rows => ε < |normalizedLogDeterminant (degreeNormalizedMatrix rows) z - circularLogPotential z|)

end CircularLaw
