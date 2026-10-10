import CircularLaw.RowSliceBottomLogBudgets
import CircularLaw.IndependentSquareMinimumFailure

/-!
# Actual row-slice bottom tails on the independent square coupling

The two scalar budgets give convergence in probability after accounting
for the literal minimum failure event. The lower regime also uses the
proved intermediate event. The imported minimum probabilities remain
explicit, and no minimum estimate is asserted by these deductions.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem independent_square_slice_event_real (n d : ℕ) (event : RowSliceMatrix n d → Prop) :
    (independentSquareComparisonLaw n d).real {samples | event samples.1} =
      (rowSliceMatrixLaw n d).real {rows | event rows} := by
  haveI : IsFiniteMeasure (rowSliceMatrixLaw n d) := by unfold rowSliceMatrixLaw; infer_instance
  exact finite_law_event_real measurable_fst (independent_square_slice_marginal n d) event

theorem row_slice_intermediate_failure_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (R : ℝ)
    (hSuccess : Tendsto (fixedShiftIntermediateProbability R d z) atTop (𝓝 1)) :
    Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | ¬IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R rows}) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hSuccess
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  haveI := rowSliceMatrixLaw_probability hd.2
  have hCompl := probReal_compl_eq_one_sub (μ := rowSliceMatrixLaw n (d n))
    ((Set.toFinite {rows | IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R rows}).measurableSet)
  simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real, fixedShiftIntermediateProbability,
    Set.compl_setOf] using hCompl.symm

theorem varying_probability_of_nonnegative_good_bound {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : ∀ n, Ω n → ℝ) (budget : ℕ → ℝ) (bad : ∀ n, Set (Ω n))
    (hNonneg : ∀ n ω, 0 ≤ f n ω) (hBudget : Tendsto budget atTop (𝓝 0))
    (hBad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (hBound : ∀ᶠ n in atTop, ∀ ω, ω ∉ bad n → f n ω ≤ budget n) :
    VaryingConvergesInProbability μ f 0 := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBad
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hBound, hBudget.eventually (gt_mem_nhds hε)] with n hBn hSmall
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hω
  by_contra hGood
  have h := hBn ω hGood
  simp only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg (hNonneg n ω)] at hω
  linarith

def independentSliceBottomNegativeLog (n d : ℕ) (a : ℝ) (z : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) : ℝ :=
  empiricalBottomNegativeLog
    (squareSingularValuesNNReal (fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) samples.1))
    (hermitizationDeletionCount n d a)

theorem independent_slice_bottom_negative_log_nonneg (n d : ℕ) (a : ℝ) (z : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) :
    0 ≤ independentSliceBottomNegativeLog n d a z samples := by
  unfold independentSliceBottomNegativeLog empiricalBottomNegativeLog
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (Nat.cast_nonneg n)

theorem lower_row_slice_bottom_negative_log_converges {C σ CL R : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (hCL : 0 ≤ CL) (hR : 0 ≤ R) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) (hSparse : SparseDegrees d) (z : ℂ)
    (hMinBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
        (lowerHermitizationCutoff n CL))) atTop (𝓝 0))
    (hIntermediate : Tendsto (fixedShiftIntermediateProbability R d z) atTop (𝓝 1)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) (1 / 2) z) 0 := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hC d (hBand.mono (fun _ h => h.1)))
  let bad := fun n => independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
    (lowerHermitizationCutoff n CL) ∪
      {samples | ¬IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R samples.1}
  have hI := row_slice_intermediate_failure_tendsto_zero d hDegree hSparse z R hIntermediate
  have hSum := hMinBad.add hI
  simp only [add_zero] at hSum
  have hBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real (bad n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    apply Eventually.of_forall
    intro n
    have h := measureReal_union_le (μ := independentSquareComparisonLaw n (d n))
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ)) (lowerHermitizationCutoff n CL))
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
  have hMin : (∀ j, lowerHermitizationCutoff n CL ≤ orderedSquareSingularValues
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) j) ∧
      (∀ j, lowerHermitizationCutoff n CL ≤ orderedSquareSingularValues
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) j) := by
    have h := fun hBad => hGood (Set.mem_union_left _ hBad)
    exact not_not.mp h
  have hInt : IntermediateSingularValueEvent (z * (Real.sqrt (d n : ℝ) : ℂ)) R samples.1 := by
    have h := fun hBad => hGood (Set.mem_union_right _ hBad)
    exact not_not.mp h
  exact row_slice_lower_bottom_bound_on_good_events hn samples.1 _ hR hMin.1 hInt

theorem superlog_row_slice_bottom_negative_log_converges (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) (z : ℂ)
    (hMinBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
        (polynomialHermitizationCutoff n B))) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentSliceBottomNegativeLog n (d n) (superlogHermitizationExponent ε) z) 0 := by
  apply varying_probability_of_nonnegative_good_bound
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => independentSliceBottomNegativeLog n (d n) (superlogHermitizationExponent ε) z)
    (fun n => superlogRowBottomLogBudget n (d n) B ε)
    (fun n => independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
      (polynomialHermitizationCutoff n B))
    (fun n => independent_slice_bottom_negative_log_nonneg n (d n) (superlogHermitizationExponent ε) z)
    (superlog_row_bottom_log_budget_tendsto_zero d hSparse hB hε hLower) hMinBad
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro samples hGood
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < polynomialHermitizationCutoff n B := Real.rpow_pos_of_pos hnR _
  have hMin : (∀ j, polynomialHermitizationCutoff n B ≤ orderedSquareSingularValues
      (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) samples.1) j) ∧
      (∀ j, polynomialHermitizationCutoff n B ≤ orderedSquareSingularValues
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) j) := not_not.mp hGood
  exact square_bottom_negative_log_bound_of_minimum _ _ hτ hMin.1

end CircularLaw
