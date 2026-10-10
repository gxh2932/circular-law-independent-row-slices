import CircularLaw.LLYSourceGradualBudgets
import CircularLaw.LLYFirstWitnessBudgets
import CircularLaw.LLYFirstRadiusBudgets
import CircularLaw.LLYFirstSteepProbability

/-!
# First-class kernel and adjoint probabilities at the source parameters

The rank-one class is empty. At all other literal ceiling ranks the
source floor budget, square-root stride, scale count and expansion
parameters supply the proved finite probability estimates.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_lly_first_source_leave_one_out_kernel_probability {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyFirstSteepLeaveOneOutKernelFailure ζ rows i (llySourceStride n d)
            (llySourceScale n d a) (llySourceFirstRank n d a)) ≤ (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 100,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 1),
    eventually_lly_first_witness_failure_polynomial A] with n hn hDegrees hWitness
  intro d hLower hdn i ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hStride := lly_source_stride_ge_two (by omega : 2 ≤ n) hd hC hLower
  by_cases hOne : llySourceFirstRank n d a = 1
  · rw [hOne, lly_first_steep_rank_one_kernel_probability hd (by omega : 0 < llySourceStride n d)]
    positivity
  · have hFloor := lly_source_first_nonunit_rank_floor_budget (by omega : 2 ≤ n) hd hC hLower ha haOne hOne
    have hk := lly_source_first_rank_pos (by omega : 2 ≤ n) hd ha
    have hkn := lly_source_first_rank_le_dimension (by omega : 2 ≤ n) hd ha.le haOne (by linarith) hLower
    have hScale := (lly_source_scale_ranks (by omega : 2 ≤ n) hd hC hLower ha).1.resolve_left hOne
    have hLog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
    have hDegreeCost := (mul_le_mul_of_nonneg_right
      (max_le hEntropyCost hFailureCost) hLog).trans hLower
    have hProbability := hWitness d (llySourceStride n d) (llySourceScale n d a) (llySourceFirstRank n d a)
      hd hdn hStride hk hkn hFloor hScale hDegreeCost
      (lly_source_stride_sqrt_log_budget (by omega : 2 ≤ n) hd)
      (Finset.univ.erase i) (one_row_deleted_retained_card hn i)
    apply (uniformProbability_mono ?_).trans hProbability
    intro rows hFail hGood
    obtain ⟨x, hUnit, hFirst, hKernel⟩ := hFail
    apply lly_first_steep_retained_kernel_exclusion (by omega : 0 < n) hd
      (by omega : 0 < llySourceStride n d) hk hkn (Finset.univ.erase i) rows hGood ζ hShift x hUnit hFirst
    ext j
    rw [retained_shifted_slice_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1

theorem eventually_lly_first_source_radius_adjoint_probability {C A a : ℝ}
    (hC : 1920000 ≤ C) (hA : A ≤ 11)
    (hColumnCost : (1 / (2 * sliceTailRate)) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyFirstSteepAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a)
            (llySourceFirstRank n d a)
            ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)) ≤
              2 * (n : ℝ) ^ (-A) := by
  have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 2, hLog,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 16)]
      with n hn hLog hDegrees
  intro d hLower hdn ζ hShift
  have hdLarge : 16 ≤ d := hDegrees d hLower
  have hd : 0 < d := by omega
  have hk := lly_source_first_rank_pos hn hd ha
  have hkn := lly_source_first_rank_le_dimension hn hd ha.le haOne (by linarith) hLower
  have hStride := lly_source_stride_ge_two hn hd hC hLower
  by_cases hOne : llySourceFirstRank n d a = 1
  · rw [hOne, lly_first_steep_adjoint_rank_one_failure_probability hd (by omega : 0 < llySourceStride n d)]
    positivity
  · have hEps := lly_source_epsilon_pos hn hd
    have hSize := lly_source_first_nonunit_rank_expansion_budget hn hd ha haOne hOne
    have hEpsSquare := lly_source_epsilon_square_degree hn hd
    have hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ (2 * llySourceEpsilon n d) ^ 2 * d := by
      nlinarith [hEpsSquare]
    have hError : (2 * llySourceEpsilon n d) * llySourceStride n d ≤ 1 / 8 := by
      have h := lly_source_stride_epsilon_budget hn hd
      nlinarith
    have hProbability := lly_first_steep_adjoint_failure_probability_of_gradual_radius
      (by omega : 0 < n) hd hdn (by omega : 0 < llySourceStride n d) hk hkn
      (by positivity : 0 ≤ 2 * llySourceEpsilon n d) hSize hBudget hError
      (lly_source_stride_quarter_degree_budget hn hdLarge hLog)
      (lly_source_almost_radius_pos (by omega : 0 < n) hd a).le
      (lly_source_almost_radius_gradual n d a) ζ hShift
    have hScales := lly_first_scale_count hStride
      ((lly_source_scale_ranks hn hd hC hLower ha).1.resolve_left hOne) hkn
    have hScalesR : ((llySourceScale n d a + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hScales
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hExponent : -(2 * llySourceEpsilon n d) ^ 2 * d / 16 = -12 * Real.log (n : ℝ) := by
      nlinarith [hEpsSquare]
    have hFirst : ((llySourceScale n d a + 1 : ℕ) : ℝ) *
        Real.exp (-(2 * llySourceEpsilon n d) ^ 2 * d / 16) ≤ (n : ℝ) ^ (-A) := by
      rw [hExponent]
      calc
        _ ≤ (n : ℝ) * Real.exp (-12 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hScalesR (Real.exp_nonneg _)
        _ = Real.exp (-11 * Real.log (n : ℝ)) := by
          calc
            _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-12 * Real.log (n : ℝ)) := by
              rw [Real.exp_log hnR]
            _ = _ := by rw [← Real.exp_add]; congr 1; ring
        _ = (n : ℝ) ^ (-11 : ℝ) := by
          rw [Real.rpow_def_of_pos hnR]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n) (by linarith)
    have hColumnDegree := (mul_le_mul_of_nonneg_right hColumnCost
      (by linarith : 0 ≤ Real.log (n : ℝ))).trans hLower
    have hColumn : (n : ℝ) * Real.exp (-2 * sliceTailRate * d) ≤ (n : ℝ) ^ (-A) := by
      have h := dimension_exp_degree_le_rpow (by omega : 0 < n)
        (one_div_pos.mpr (mul_pos (by norm_num) sliceTailRate_pos)) hColumnDegree
      convert h using 1
      congr 2
      field_simp
    apply hProbability.trans
    simpa only [two_mul] using add_le_add hFirst hColumn

end CircularLaw
