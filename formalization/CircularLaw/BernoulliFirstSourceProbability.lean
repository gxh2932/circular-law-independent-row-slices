import CircularLaw.BernoulliFirstSteepProbability
import CircularLaw.LLYSourceGradualBudgets
import CircularLaw.LLYFirstWitnessBudgets
import CircularLaw.LLYFirstRadiusBudgets

/-!
# Bernoulli first-steep probabilities at the literal source parameters

The ceiling rank is either one, making the first class empty, or fits
the checked floor witness budget. The actual Bernoulli upper-degree and
witness bounds both have arbitrary polynomial decay above C log n.
-/

noncomputable section
open Classical MeasureTheory Filter

namespace CircularLaw

theorem bernoulli_row_degree_upper_failure_polynomial {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (A : ℝ)
    (hDegree : (1 / bernoulliDegreeUpperRate) * (A + 1) * Real.log (n : ℝ) ≤ d) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample} ≤ (n : ℝ) ^ (-A) := by
  apply (sparse_bernoulli_row_degree_upper_failure hn hdn).trans
  have h := dimension_exp_degree_le_rpow hn
    (one_div_pos.mpr bernoulli_degree_upper_rate_pos) hDegree
  convert h using 1
  congr 2
  field_simp

theorem bernoulli_lly_first_steep_retained_failure_polynomial {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (hScales : r + 1 ≤ n) (A : ℝ)
    (hWitnessDegree : (2 / uniqueWitnessRate) * (A + 1) * Real.log (n : ℝ) ≤ d)
    (hUpperDegree : (1 / bernoulliDegreeUpperRate) * (A + 1) * Real.log (n : ℝ) ≤ d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) {τ : ℝ}
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYFirstSteepRetainedFailure I ζ sample d ℓ r k τ} ≤ 2 * (n : ℝ) ^ (-A) := by
  apply (bernoulli_lly_first_steep_retained_failure_probability hn hd hdn hℓ hk hkn I hI
    hSmall hBudget ζ hSpectral hThreshold).trans
  have hUpper := dimension_exp_degree_le_rpow (by omega : 0 < n)
    (one_div_pos.mpr bernoulli_degree_upper_rate_pos) hUpperDegree
  have hUpper' : (n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) ≤ (n : ℝ) ^ (-A) := by
    convert hUpper using 1
    congr 2
    field_simp
  have hScalesR : ((r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hScales
  have hWitness : ((r + 1 : ℕ) : ℝ) * Real.exp (-(uniqueWitnessRate / 2) * d) ≤ (n : ℝ) ^ (-A) := by
    have h := dimension_exp_degree_le_rpow (by omega : 0 < n)
      (div_pos (by norm_num) uniqueWitnessRate_pos) hWitnessDegree
    have hExponent : -(uniqueWitnessRate / 2) * (d : ℝ) = -(d : ℝ) / (2 / uniqueWitnessRate) := by
      field_simp
    calc
      _ ≤ (n : ℝ) * Real.exp (-(uniqueWitnessRate / 2) * d) :=
        mul_le_mul_of_nonneg_right hScalesR (Real.exp_pos _).le
      _ ≤ _ := by simpa only [hExponent] using h
  simpa only [two_mul] using add_le_add hUpper' hWitness

theorem bernoulli_lly_first_steep_rank_one_retained_failure_probability {n d ℓ r : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (I : Finset (Fin n)) (ζ : ℂ) (τ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYFirstSteepRetainedFailure I ζ sample d ℓ r 1 τ} = 0 := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYFirstSteepRetainedFailure I ζ sample d ℓ r 1 τ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro sample hFail
    obtain ⟨x, _, hFirst, _⟩ := hFail
    rw [lly_first_steep_rank_one_empty hd hℓ] at hFirst
    exact hFirst
  rw [hEvent, measureReal_empty]

theorem eventually_bernoulli_lly_first_source_retained_failure_probability {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ I : Finset (Fin n), (99 / 100 : ℝ) * n ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) →
          (sparseBernoulliMatrixLaw n d).real {sample |
            BernoulliLLYFirstSteepRetainedFailure I ζ sample d (llySourceStride n d)
              (llySourceScale n d a) (llySourceFirstRank n d a)
              ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)} ≤
                2 * (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 100,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 1),
    eventually_lly_first_stride_entropy_budget] with n hn hDegrees hEntropy
  intro d hLower hdn I hI ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hStride := lly_source_stride_ge_two (by omega : 2 ≤ n) hd hC hLower
  by_cases hOne : llySourceFirstRank n d a = 1
  · rw [hOne, bernoulli_lly_first_steep_rank_one_retained_failure_probability hd
      (by omega : 0 < llySourceStride n d)]
    positivity
  · have hFloor := lly_source_first_nonunit_rank_floor_budget (by omega : 2 ≤ n) hd hC hLower ha haOne hOne
    have hk := lly_source_first_rank_pos (by omega : 2 ≤ n) hd ha
    have hkn := lly_source_first_rank_le_dimension (by omega : 2 ≤ n) hd ha.le haOne (by linarith) hLower
    have hRank := (lly_source_scale_ranks (by omega : 2 ≤ n) hd hC hLower ha).1.resolve_left hOne
    have hScales := lly_first_scale_count hStride hRank hkn
    have hLog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
    have hEntropyDegree := (mul_le_mul_of_nonneg_right hEntropyCost hLog).trans hLower
    have hWitnessDegree := (mul_le_mul_of_nonneg_right hFailureCost hLog).trans hLower
    have hUpperDegree := (mul_le_mul_of_nonneg_right hUpperCost hLog).trans hLower
    have hBudget := hEntropy d (llySourceStride n d) hd hEntropyDegree
      (lly_source_stride_sqrt_log_budget (by omega : 2 ≤ n) hd)
    have hThreshold := lly_gradual_radius_first_threshold (by omega : 0 < n) hd hOne
      (lly_source_almost_radius_pos (by omega : 0 < n) hd a).le (lly_source_almost_radius_gradual n d a)
    exact bernoulli_lly_first_steep_retained_failure_polynomial (by omega : 3 ≤ n) hd hdn
      (by omega : 0 < llySourceStride n d) hk hkn I hI (lly_first_rank_witness_budget hd hFloor)
      hBudget hScales A hWitnessDegree hUpperDegree ζ hShift hThreshold

theorem eventually_bernoulli_lly_first_source_leave_one_out_kernel_probability {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) →
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d (llySourceStride n d)
            (llySourceScale n d a) (llySourceFirstRank n d a)} ≤ 2 * (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 100,
    eventually_bernoulli_lly_first_source_retained_failure_probability hC hEntropyCost hFailureCost
      hUpperCost ha haOne] with n hn hProbability
  intro d hLower hdn i ζ hShift
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (hProbability d hLower hdn (Finset.univ.erase i) (one_row_deleted_retained_card hn i) ζ hShift)
  intro sample hFail
  obtain ⟨x, hUnit, hFirst, hKernel⟩ := hFail
  have hZero : (retainedShiftedBernoulliMatrix (Finset.univ.erase i) ζ sample).toEuclideanLin x = 0 := by
    ext j
    rw [retained_shifted_bernoulli_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1
  refine ⟨x, hUnit, hFirst, ?_⟩
  rw [hZero, norm_zero]
  calc
    0 ≤ (llySourceAlmostRadius n d a / Real.sqrt n) ^ 2 := sq_nonneg _
    _ = _ := by ring

end CircularLaw
