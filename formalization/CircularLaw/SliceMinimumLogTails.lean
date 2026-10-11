import CircularLaw.SliceMinimumPrefixVolume
import CircularLaw.RowSliceMinimumRegimeLimits

/-!
# Actual slice minimum inputs for ridge scales and bottom log tails

Both ridge scales tend to zero. The actual row-slice minimum event,
together with the proved intermediate event in the lower band, controls
the bottom tails; the comparator minimum is not a premise here.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem eventually_lower_hermitization_cutoff_bounds {CL : ℝ} (hCL : 0 ≤ CL) :
    ∀ᶠ n : ℕ in atTop, 0 < lowerHermitizationCutoff n CL ∧ lowerHermitizationCutoff n CL ≤ 1 := by
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop 1, hLog] with n hn hLogN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hnR) _
  · unfold lowerHermitizationCutoff
    simpa only [Real.rpow_eq_pow] using Real.rpow_le_one_of_one_le_of_nonpos hnR
      (neg_nonpos.mpr (mul_nonneg hCL (Real.log_nonneg hLogN)))

theorem eventually_polynomial_hermitization_cutoff_bounds {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, 0 < polynomialHermitizationCutoff n B ∧ polynomialHermitizationCutoff n B ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hnR) _
  · unfold polynomialHermitizationCutoff
    simpa only [Real.rpow_eq_pow] using Real.rpow_le_one_of_one_le_of_nonpos hnR (neg_nonpos.mpr hB)

theorem lower_hermitization_ridge_tendsto_zero {CL : ℝ} (hCL : 0 ≤ CL) :
    Tendsto (fun n : ℕ => lowerHermitizationCutoff n CL / n) atTop (𝓝 0) :=
  ridge_scale_tendsto_zero_of_bounded_cutoff _
    ((eventually_lower_hermitization_cutoff_bounds hCL).mono (fun _ h => ⟨h.1.le, h.2⟩))

theorem polynomial_hermitization_ridge_tendsto_zero {B : ℝ} (hB : 0 ≤ B) :
    Tendsto (fun n : ℕ => polynomialHermitizationCutoff n B / n) atTop (𝓝 0) :=
  ridge_scale_tendsto_zero_of_bounded_cutoff _
    ((eventually_polynomial_hermitization_cutoff_bounds hB).mono (fun _ h => ⟨h.1.le, h.2⟩))

theorem independent_slice_minimum_failure_tendsto_zero (d : ℕ → ℕ) (ζ : ℕ → ℂ) (τ : ℕ → ℝ)
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) rows) (τ n)}) atTop (𝓝 0)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      {samples | squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) samples.1) (τ n)})
      atTop (𝓝 0) := by
  apply hMin.congr'
  exact Eventually.of_forall (fun n => (independent_square_slice_event_real n (d n)
    (fun rows => squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) rows) (τ n))).symm)

theorem lower_row_slice_bottom_negative_log_converges_of_slice_minimum {C σ CL R : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (hCL : 0 ≤ CL) (hR : 0 ≤ R) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) (hSparse : SparseDegrees d) (z : ℂ)
    (hMinBad : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows)
        (lowerHermitizationCutoff n CL)}) atTop (𝓝 0))
    (hIntermediate : Tendsto (fixedShiftIntermediateProbability R d z) atTop (𝓝 1)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) (1 / 2) z) 0 := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hC d (hBand.mono (fun _ h => h.1)))
  have hMinCoupled := independent_slice_minimum_failure_tendsto_zero d
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) (fun n => lowerHermitizationCutoff n CL) hMinBad
  let bad : ∀ n, Set (RowSliceMatrix n (d n) × BernoulliSquareSample n) := fun n =>
    {samples | squareSmallestSingularFailure
    (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1)
    (lowerHermitizationCutoff n CL)} ∪
      {samples | ¬IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R samples.1}
  have hI := row_slice_intermediate_failure_tendsto_zero d hDegree hSparse z R hIntermediate
  have hSum := hMinCoupled.add hI
  simp only [add_zero] at hSum
  have hBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real (bad n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    apply Eventually.of_forall
    intro n
    have h := measureReal_union_le (μ := independentSquareComparisonLaw n (d n))
      {samples | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) (lowerHermitizationCutoff n CL)}
      {samples | ¬IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R samples.1}
    rw [independent_square_slice_event_real n (d n)
      (fun rows => ¬IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R rows)] at h
    exact h
  apply varying_probability_of_nonnegative_good_bound
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => independentSliceBottomNegativeLog n (d n) (1 / 2) z)
    (fun n => lowerRowBottomLogBudget n (d n) CL R) bad
    (fun n => independent_slice_bottom_negative_log_nonneg n (d n) (1 / 2) z)
    (lower_row_bottom_log_budget_tendsto_zero hC hσ hCL hR d hBand hSparse) hBad
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro samples hGood
  have hMin : ∀ j, lowerHermitizationCutoff n CL ≤ orderedSquareSingularValues
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) j := by
    apply square_singular_lower_bound_outside_failure
    exact fun hBad => hGood (Set.mem_union_left _ hBad)
  have hInt : IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R samples.1 := by
    have h := fun hBad => hGood (Set.mem_union_right _ hBad)
    exact not_not.mp h
  exact row_slice_lower_bottom_bound_on_good_events hn samples.1 _ hR hMin hInt

theorem superlog_row_slice_bottom_negative_log_converges_of_slice_minimum (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) (z : ℂ)
    (hMinBad : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows)
        (polynomialHermitizationCutoff n B)}) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) (superlogHermitizationExponent ε) z) 0 := by
  apply varying_probability_of_nonnegative_good_bound
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => independentSliceBottomNegativeLog n (d n) (superlogHermitizationExponent ε) z)
    (fun n => superlogRowBottomLogBudget n (d n) B ε)
    (fun n => {samples | squareSmallestSingularFailure
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) (polynomialHermitizationCutoff n B)})
    (fun n => independent_slice_bottom_negative_log_nonneg n (d n) (superlogHermitizationExponent ε) z)
    (superlog_row_bottom_log_budget_tendsto_zero d hSparse hB hε hLower)
    (independent_slice_minimum_failure_tendsto_zero d (fun n => z * (Real.sqrt (d n : ℝ) : ℂ))
      (fun n => polynomialHermitizationCutoff n B) hMinBad)
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro samples hGood
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < polynomialHermitizationCutoff n B := Real.rpow_pos_of_pos hnR _
  have hMin := square_singular_lower_bound_outside_failure
    (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1)
    (polynomialHermitizationCutoff n B) hGood
  exact square_bottom_negative_log_bound_of_minimum _ _ hτ hMin

end CircularLaw
