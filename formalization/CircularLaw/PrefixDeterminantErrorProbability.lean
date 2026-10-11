import CircularLaw.PrefixDeterminantErrorGeometry
import CircularLaw.RowSliceBottomLogProbability
import CircularLaw.IndependentBernoulliLogTails

/-!
# Passing from actual prefix volumes to actual square determinants

Top and bottom tails bound each determinant-volume error on the joint
minimum event. Their checked limits and the volume comparison then give
the literal raw square log-determinant comparison. The minimum failure
limit remains an explicit mathematical premise.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem varying_probability_of_good_random_bound {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (f g : ∀ n, Ω n → ℝ) (bad : ∀ n, Set (Ω n))
    (hBad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (hG : VaryingConvergesInProbability μ g 0)
    (hBound : ∀ᶠ n in atTop, ∀ ω, ω ∉ bad n → |f n ω| ≤ g n ω) :
    VaryingConvergesInProbability μ f 0 := by
  intro ε hε
  have hUpper := hBad.add (hG ε hε)
  simp only [add_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hBound] with n hBn
  apply (measureReal_mono (μ := μ n) (s₂ := bad n ∪ {ω | ε < |g n ω - 0|})
    (h₂ := by finiteness) ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_cases hGood : ω ∈ bad n
  · exact Or.inl hGood
  · apply Or.inr
    simp only [Set.mem_setOf_eq, sub_zero] at hω ⊢
    exact hω.trans_le ((hBn ω hGood).trans (le_abs_self _))

theorem independent_slice_top_positive_log_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => squareTopPositiveLog
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1)
        (hermitizationDeletionCount n (d n) a)) 0 := by
  apply varying_probability_of_nonnegative_good_bound
    (fun n => independentSquareComparisonLaw n (d n)) _
    (fun n => (Real.log (1 + (2 + 2 * ‖z‖ ^ 2)) + (1 + a) * Real.log (d n : ℝ)) /
      Real.rpow (d n : ℝ) a) (fun _ => ∅)
    (fun _ _ => square_top_positive_log_nonneg _ _)
    (hermitization_positive_log_budget_tendsto_zero d hDegree ha (2 + 2 * ‖z‖ ^ 2))
    (by simpa only [measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd samples _
  exact square_top_positive_hermitization_energy_bound _ (lt_of_lt_of_le hd.1 hd.2) hd.1 hd.2 ha haOne
    (by positivity : (0 : ℝ) ≤ 2 + 2 * ‖z‖ ^ 2) (row_slice_shifted_energy_degree_bound samples.1 z)

def independentSquareLogDeterminantDifference (n d : ℕ) (z : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) : ℝ :=
  (Real.log ‖(fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) samples.1).det‖ -
    Real.log ‖(bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1).det‖) / n

theorem independent_square_log_det_comparison_of_prefix_and_tails (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (z : ℂ) (τ : ℕ → ℝ)
    (hτ : ∀ᶠ n in atTop, 0 < τ n)
    (hMinBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n))) atTop (𝓝 0))
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
  let bad := fun n => independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n)
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
    filter_upwards [hτ, eventually_valid_bernoulli_degrees hDegree hSparse] with n hτn hd
    intro samples hGood
    have hMin : (∀ j, τ n ≤ orderedSquareSingularValues (A n samples) j) ∧
        (∀ j, τ n ≤ orderedSquareSingularValues (B n samples) j) := not_not.mp hGood
    have hrn : r n ≤ n := hermitizationDeletionCount_le_dimension (by omega) ha.le
    have hA := row_restriction_normalized_det_error_bound (A n samples) (f n) (Nat.sub_le n (r n))
      (square_det_ne_zero_of_singular_lower_bound _ hτn hMin.1)
    have hB := row_restriction_normalized_det_error_bound (B n samples) (f n) (Nat.sub_le n (r n))
      (square_det_ne_zero_of_singular_lower_bound _ hτn hMin.2)
    dsimp only [r] at hrn
    simpa only [r, Nat.sub_sub_self hrn] using And.intro hA hB
  have hAError := varying_probability_of_good_random_bound μ
    (fun n samples => (Real.log ‖(A n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (A n samples) (f n))) / n)
    (fun n samples => squareTopPositiveLog (A n samples) (r n) +
      empiricalBottomNegativeLog (squareSingularValuesNNReal (A n samples)) (r n)) bad hMinBad hSliceTail
    (hGeometry.mono (fun _ h samples hGood => (h samples hGood).1))
  have hBError := varying_probability_of_good_random_bound μ
    (fun n samples => (Real.log ‖(B n samples).det‖ - matrixRowLogVolume (matrixRowRestriction (B n samples) (f n))) / n)
    (fun n samples => squareTopPositiveLog (B n samples) (r n) +
      empiricalBottomNegativeLog (squareSingularValuesNNReal (B n samples)) (r n)) bad hMinBad hBernoulliTail
    (hGeometry.mono (fun _ h samples hGood => (h samples hGood).2))
  have hDiff := varying_probability_sub μ hAError hBError
  simp only [sub_self] at hDiff
  have hCombined := varying_probability_add μ hDiff hVolume
  simp only [add_zero] at hCombined
  convert hCombined using 1
  funext n samples
  dsimp [independentSquareLogDeterminantDifference, independentPrefixVolumeDifference, A, B, f]
  ring

end CircularLaw
