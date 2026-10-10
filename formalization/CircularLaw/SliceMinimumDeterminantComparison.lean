import CircularLaw.SliceMinimumPrefixVolume

/-!
# Determinant comparison using vanishing zero probabilities

Log-volume interlacing requires nonzero determinants. The row-slice
minimum estimate supplies this for the slice model, while the checked
Bernoulli full-log limit supplies it for the comparator. No quantitative
Bernoulli minimum estimate is used in these deductions.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

def independentSquareDeterminantZero (n d : ℕ) (z : ℂ) :
    Set (RowSliceMatrix n d × BernoulliSquareSample n) :=
  {samples | (fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) samples.1).det = 0 ∨
    (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1).det = 0}

theorem independent_slice_raw_det_zero_probability_of_minimum (d : ℕ → ℕ)
    (z : ℂ) (τ : ℕ → ℝ) (hτ : ∀ᶠ n : ℕ in atTop, 0 < τ n)
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (τ n)}) atTop (𝓝 0)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      {samples | (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1).det = 0})
      atTop (𝓝 0) := by
  have hBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      {samples | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) (τ n)}) atTop (𝓝 0) := by
    apply hMin.congr'
    exact Eventually.of_forall (fun n => (independent_square_slice_event_real n (d n)
      (fun rows => squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (τ n))).symm)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hBad
  filter_upwards [hτ] with n hτn
  apply measureReal_mono (h₂ := by finiteness)
  intro samples hDet
  by_contra hGood
  exact square_det_ne_zero_of_singular_lower_bound _ hτn
    (square_singular_lower_bound_outside_failure _ (τ n) hGood) hDet

theorem independent_square_det_zero_probability_of_slice_minimum (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    (τ : ℕ → ℝ) (hτ : ∀ᶠ n : ℕ in atTop, 0 < τ n)
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (τ n)}) atTop (𝓝 0)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareDeterminantZero n (d n) z)) atTop (𝓝 0) := by
  have hSum := (independent_slice_raw_det_zero_probability_of_minimum d z τ hτ hMin).add
    (independent_bernoulli_raw_det_zero_probability_tendsto_zero d hDegree hSparse z hz)
  simp only [add_zero] at hSum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hSum
  exact Eventually.of_forall (fun n => measureReal_union_le _ _)

theorem independent_square_log_det_comparison_of_prefix_and_tails_and_zero_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (z : ℂ)
    (hZero : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareDeterminantZero n (d n) z)) atTop (𝓝 0))
    (hVolume : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixVolumeDifference n (d n) a (z * (Real.sqrt (d n : ℝ) : ℂ))) 0)
    (hSliceBottom : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) a z) 0)
    (hBernoulliBottom : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => empiricalBottomNegativeLog
        (squareSingularValuesNNReal (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1))
        (hermitizationDeletionCount n (d n) a)) 0) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSquareLogDeterminantDifference n (d n) z) 0 := by
  let μ := fun n => independentSquareComparisonLaw n (d n)
  let A := fun n (samples : RowSliceMatrix n (d n) × BernoulliSquareSample n) =>
    fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1
  let B := fun n (samples : RowSliceMatrix n (d n) × BernoulliSquareSample n) =>
    bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1
  let r := fun n => hermitizationDeletionCount n (d n) a
  let f := fun n => hermitizationPrefixEmbedding n (d n) a
  let bad := fun n => independentSquareDeterminantZero n (d n) z
  have hSliceTail := varying_probability_add μ
    (independent_slice_top_positive_log_converges d hDegree hSparse z ha haOne) hSliceBottom
  have hBernoulliTail := varying_probability_add μ
    (independent_bernoulli_top_positive_log_converges d hDegree hSparse z ha haOne) hBernoulliBottom
  simp only [add_zero] at hSliceTail hBernoulliTail
  have hGeometry : ∀ᶠ n in atTop, ∀ samples, samples ∉ bad n →
      |(Real.log ‖(A n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (A n samples) (f n))) / n| ≤
        squareTopPositiveLog (A n samples) (r n) + empiricalBottomNegativeLog (squareSingularValuesNNReal (A n samples)) (r n) ∧
      |(Real.log ‖(B n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (B n samples) (f n))) / n| ≤
        squareTopPositiveLog (B n samples) (r n) + empiricalBottomNegativeLog (squareSingularValuesNNReal (B n samples)) (r n) := by
    filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
    intro samples hGood
    have hDet : (A n samples).det ≠ 0 ∧ (B n samples).det ≠ 0 := not_or.mp hGood
    have hrn : r n ≤ n := hermitizationDeletionCount_le_dimension (by omega) ha.le
    have hA := row_restriction_normalized_det_error_bound (A n samples) (f n) (Nat.sub_le n (r n))
      hDet.1
    have hB := row_restriction_normalized_det_error_bound (B n samples) (f n) (Nat.sub_le n (r n))
      hDet.2
    dsimp only [r] at hrn
    simpa only [r, Nat.sub_sub_self hrn] using And.intro hA hB
  have hAError := varying_probability_of_good_random_bound μ
    (fun n samples => (Real.log ‖(A n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (A n samples) (f n))) / n)
    (fun n samples => squareTopPositiveLog (A n samples) (r n) +
      empiricalBottomNegativeLog (squareSingularValuesNNReal (A n samples)) (r n)) bad hZero hSliceTail
    (hGeometry.mono (fun _ h samples hGood => (h samples hGood).1))
  have hBError := varying_probability_of_good_random_bound μ
    (fun n samples => (Real.log ‖(B n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (B n samples) (f n))) / n)
    (fun n samples => squareTopPositiveLog (B n samples) (r n) +
      empiricalBottomNegativeLog (squareSingularValuesNNReal (B n samples)) (r n)) bad hZero hBernoulliTail
    (hGeometry.mono (fun _ h samples hGood => (h samples hGood).2))
  have hDiff := varying_probability_sub μ hAError hBError
  simp only [sub_self] at hDiff
  have hCombined := varying_probability_add μ hDiff hVolume
  simp only [add_zero] at hCombined
  convert hCombined using 1
  funext n samples
  dsimp [independentSquareLogDeterminantDifference, independentPrefixVolumeDifference, A, B, f]
  ring


theorem independent_normalized_log_det_comparison_of_raw_and_zero_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    (hZero : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareDeterminantZero n (d n) z)) atTop (𝓝 0))
    (hRaw : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSquareLogDeterminantDifference n (d n) z) 0) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => normalizedLogDeterminant (degreeNormalizedMatrix samples.1) z -
        normalizedLogDeterminant (degreeNormalizedBernoulliMatrix (d n) samples.2) z) 0 := by
  apply varying_probability_of_agreement_outside_bad_event
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => independentSquareDeterminantZero n (d n) z) hRaw hZero
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  intro samples hGood
  have hDet :
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1).det ≠ 0 ∧
      (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1).det ≠ 0 :=
    not_or.mp hGood
  exact independent_normalized_log_det_difference_eq_raw hd.1 z samples hDet.1 hDet.2

end CircularLaw
