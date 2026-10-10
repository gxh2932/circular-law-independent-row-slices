import CircularLaw.BernoulliLaterSourcePolynomial
import CircularLaw.LLYSourceMinimumProbability

/-!
# Quantitative minimum-singular-value probability for the actual Bernoulli law

All steep adjoint and omitted-row kernel probabilities are proved at the
literal source ranks and radius. The already checked fresh-row and gradual
reductions then give the inverse-square-root degree rate in the complete
manuscript degree and spectral windows.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem eventually_bernoulli_source_minimum_probability {C a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hFirstEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFirstFailureCost : (2 / uniqueWitnessRate) * 2 ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * 2 ≤ C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) (ha₂Small : a₂ ≤ 1 / 1000)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4) (hα : 0 < α) (hαSmall : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        (sparseBernoulliMatrixLaw n d).real {sample |
          squareSmallestSingularFailure (fullShiftedBernoulliMatrix ζ sample)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ / Real.sqrt n)} ≤
              (6 + (bernoulliScalarSmallBallConstant / Real.sqrt α + 6) / α) / Real.sqrt d := by
  have hCPos : 0 < C := by linarith
  have hNormCost : (1 : ℝ) + 4 ≤ 9 * C := by linarith
  have hDimension : ∀ᶠ n : ℕ in atTop, 4 * Real.log 4 ≤ rowLoadRate * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
      atTop atTop).eventually_ge_atTop (4 * Real.log 4 / rowLoadRate)] with n hn
    have h := (div_le_iff₀ rowLoadRate_pos).mp hn
    nlinarith only [h]
  filter_upwards [eventually_ge_atTop 100, hDimension,
    eventually_lly_source_rank_validity hC ha₁ ha₁One ha₂ ha₃ (by linarith only [ha₃Small] : a₃ ≤ 1 / 2),
    eventually_lly_source_third_rank_density ha₃ hαSmall,
    eventually_degree_property_uniform hCPos eventually_row_load_degree_entropy,
    eventually_degree_property_uniform hCPos eventually_lly_spectral_window_gradual_budget,
    eventually_bernoulli_lly_source_steep_kernel_probability_le_later (A := 1) hC hFirstEntropyCost
      (by simpa only [one_add_one_eq_two] using hFirstFailureCost)
      (by simpa only [one_add_one_eq_two] using hUpperCost) ha₁ ha₁One,
    eventually_bernoulli_later_source_kernel_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hαSmall,
    eventually_bernoulli_lly_source_steep_adjoint_probability_le_later (A := 1) hC hFirstEntropyCost
      (by simpa only [one_add_one_eq_two] using hFirstFailureCost)
      (by simpa only [one_add_one_eq_two] using hUpperCost) ha₁ ha₁One,
    eventually_bernoulli_later_source_adjoint_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hαSmall,
    eventually_lly_row_load_exponential_polynomial]
      with n hn hDimension hRanks hDensity hEntropy0 hShiftBudget hFirstKernel hLaterKernel
        hFirstAdjoint hLaterAdjoint hLoadExp
  intro d hLower hDegree ζ hShift
  have hdn : d ≤ n := by omega
  obtain ⟨hd, _, hk₁, hk₁n, hk₂, hk₃, hRanks, hHalf⟩ := hRanks d hLower hdn
  have hk₂n : llySourceSecondRank n d a₂ ≤ n := by omega
  have hk₃n : llySourceThirdRank n a₃ ≤ n := by omega
  have hFit := (lly_source_scale_ranks (by omega : 2 ≤ n) hd hC hLower ha₁).2
  have hPrefix := lly_source_first_strict_prefix_floor_budget (by omega : 2 ≤ n) hd hC hLower ha₁.le ha₁One
  have hScale₂ := lly_source_second_gradual_scale_budget (n := n) hd ha₂.le ha₂Small
  have hScale₃ := lly_source_third_gradual_scale_budget (n := n) ha₃.le
    (by linarith only [ha₃Small] : a₃ ≤ 1 / 1000)
  have hShiftGradual := (hShiftBudget d hLower).2 ζ hShift
  have hShiftD : ‖ζ‖ ≤ (d : ℝ) := hShiftGradual.trans
    (by nlinarith only [Nat.cast_nonneg (α := ℝ) d])
  have hRank₃ := lly_source_third_rank_upper (n := n) ha₃.le
  have hRank₂ : (llySourceSecondRank n d a₂ : ℝ) ≤ a₃ * n :=
    (by exact_mod_cast hRanks : (llySourceSecondRank n d a₂ : ℝ) ≤ llySourceThirdRank n a₃).trans hRank₃
  have hKernel (i : Fin n) : (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d (llySourceStride n d)
        (llySourceScale n d a₁) (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)} ≤ 4 * (n : ℝ) ^ (-1 : ℝ) := by
    apply (hFirstKernel d hLower hdn _ _ i ζ hShiftD α (llySourceAlmostRadius n d a₁)).trans
    have h := hLaterKernel d hLower hDegree i ζ hShift
    linarith
  have hAdjoint : (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepAlmostAdjointFailure ζ sample d (llySourceStride n d)
        (llySourceScale n d a₁) (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
        ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
          Real.sqrt n)} ≤ 4 * (n : ℝ) ^ (-1 : ℝ) := by
    apply (hFirstAdjoint d hLower hdn _ _ ζ hShiftD α (llySourceAlmostRadius n d a₁)).trans
    have h := hLaterAdjoint d hLower hDegree ζ hShift
    linarith
  have hBound := bernoulli_smallest_probability_of_lly_steep_bounds hn hd hDegree hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hRanks hFit hHalf hPrefix hScale₂ hScale₃ hα
    (by linarith only [hαSmall, ha₃Small] : α ≤ 1)
    (lly_source_almost_radius_pos (by omega : 0 < n) hd a₁) hDensity
    (lly_source_almost_radius_gradual n d a₁) ha₃
    (by linarith only [ha₃Small] : a₃ ≤ 1) hRank₂ hRank₃
    (hEntropy0 d hLower) hEntropy hDimension ζ hShiftGradual hKernel hAdjoint
  have hBernoulliDegree : (200 : ℝ) * (1 + 1) * Real.log (n : ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_right (by linarith only [hC] : (400 : ℝ) ≤ C)
      (Real.log_natCast_nonneg n)
    nlinarith only [h, hLower]
  have hDegreeExp := dimension_exp_degree_le_rpow (by omega : 0 < n)
    (by norm_num : (0 : ℝ) < 200) hBernoulliDegree
  have hDegreeRoot : Real.sqrt d ≤ (n : ℝ) := by
    apply (Real.sqrt_le_sqrt (by exact_mod_cast hdn : (d : ℝ) ≤ n)).trans
    apply (Real.sqrt_le_iff).mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact ⟨by linarith only [hnR], by nlinarith only [hnR]⟩
  have hPolynomial : (n : ℝ) ^ (-1 : ℝ) ≤ 1 / Real.sqrt d := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hd : (0 : ℝ) < d)) hDegreeRoot
  apply hBound.trans
  calc
    _ ≤ 6 * (n : ℝ) ^ (-1 : ℝ) +
        (bernoulliScalarSmallBallConstant / Real.sqrt (α * d) + 6 * (n : ℝ) ^ (-1 : ℝ)) / α := by
      apply add_le_add
      · nlinarith only [hDegreeExp, hLoadExp]
      · apply div_le_div_of_nonneg_right _ hα.le
        nlinarith only [hDegreeExp, hLoadExp]
    _ ≤ 6 / Real.sqrt d +
        (bernoulliScalarSmallBallConstant / Real.sqrt (α * d) + 6 / Real.sqrt d) / α := by
      have hSix : 6 * (n : ℝ) ^ (-1 : ℝ) ≤ 6 / Real.sqrt d := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left hPolynomial (by norm_num : (0 : ℝ) ≤ 6)
      exact add_le_add hSix (div_le_div_of_nonneg_right (add_le_add le_rfl hSix) hα.le)
    _ = _ := by rw [Real.sqrt_mul hα.le]; ring

end CircularLaw
