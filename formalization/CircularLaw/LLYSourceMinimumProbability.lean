import CircularLaw.LLYAlmostKernelReduction
import CircularLaw.LLYFirstSourceProbability
import CircularLaw.LLYThirdSourceKernelProbability

/-!
# Actual row-slice minimum probability at the proved source radius

All three steep classes and both gradual branches are supplied. The
source ceiling, floors, scale and spectral window are literal. Only the
conversion of the explicit source radius to the manuscript exponent and
the Bernoulli counterpart remain outside this row-slice probability
estimate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_lly_third_source_radius_adjoint_probability_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyThirdAlmostUnitAdjointFailure ζ rows (llySourceStride n d)
            (llySourceScale n d a₁) (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ / Real.sqrt n)) ≤
              (n : ℝ) ^ (-A) := by
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_third_source_radius_probability hC hAOne (by linarith : A + 1 + 3 ≤ 9 * C)
      ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα,
    eventually_dimension_log_degree_exponential_polynomial hAOne,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 2)]
      with n hn hProbability hExponents hDegrees
  intro d hLower hDegree ζ hShift
  have hd := hDegrees d hLower
  have hExp64 := hExponents d hd
  have hLog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega) : (1 : ℝ) ≤ d)
  have hProduct := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hLog
  have hExp : Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) ≤ (n : ℝ) ^ (-(A + 1)) :=
    (Real.exp_le_exp.mpr (by nlinarith : -(n : ℝ) * Real.log (d : ℝ) / 32 ≤
      -(n : ℝ) * Real.log (d : ℝ) / 64)).trans hExp64
  apply (hProbability d hLower hDegree ζ hShift).trans
  exact (by nlinarith only [hExp] : (n : ℝ) ^ (-(A + 1)) +
    Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) ≤ 2 * (n : ℝ) ^ (-(A + 1))).trans
      (two_shifted_polynomial_rates_le hn A)

theorem eventually_lly_row_load_exponential_polynomial :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(rowLoadRate / 4) * n) ≤ (n : ℝ) ^ (-1 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1)
      (div_pos rowLoadRate_pos (by norm_num : (0 : ℝ) < 4)) 0 1 (by norm_num)]
      with n hn hBudget
  simp only [zero_add, one_mul, Real.rpow_eq_pow, Real.rpow_one] at hBudget
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  apply Real.exp_le_exp.mpr
  linarith

theorem eventually_lly_source_row_slice_minimum_probability {C a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hFirstEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFirstFailureCost : (2 / uniqueWitnessRate) * 2 ≤ C)
    (hColumnCost : (1 / (2 * sliceTailRate)) * 2 ≤ C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) (ha₂Small : a₂ ≤ 1 / 1000)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4) (hα : 0 < α) (hαSmall : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ / Real.sqrt n)) ≤
              (5 + (sliceSmallBallDegreeConstant α + 4) / α) / Real.sqrt d := by
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
    eventually_lly_first_source_leave_one_out_kernel_probability (A := 1) hC hFirstEntropyCost
      (by simpa only [one_add_one_eq_two] using hFirstFailureCost) ha₁ ha₁One,
    eventually_lly_second_source_retained_kernel_probability_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂,
    eventually_lly_third_source_radius_retained_kernel_probability_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hαSmall,
    eventually_lly_first_source_radius_adjoint_probability (A := 1) hC (by norm_num : (1 : ℝ) ≤ 11)
      (by simpa only [one_add_one_eq_two] using hColumnCost) ha₁ ha₁One,
    eventually_lly_second_almost_source_radius_probability_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂,
    eventually_lly_third_source_radius_adjoint_probability_polynomial hC (by norm_num : (0 : ℝ) ≤ 1)
      hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hαSmall,
    eventually_lly_row_load_exponential_polynomial]
      with n hn hDimension hRanks hDensity hEntropy0 hShiftBudget hFirstKernel hSecondKernel hThirdKernel
        hFirstAdjoint hSecondAdjoint hThirdAdjoint hLoadExp
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
  have hRows : ∀ i : Fin n, (n : ℝ) / 2 ≤ (Finset.univ.erase i).card := by
    intro i
    have h := one_row_deleted_retained_card hn i
    linarith only [h, Nat.cast_nonneg (α := ℝ) n]
  have hBound := row_slice_smallest_probability_of_lly_almost_class_bounds hn hd hDegree hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hRanks hFit hHalf hPrefix hScale₂ hScale₃ hα
    (by linarith only [hαSmall, ha₃Small] : α ≤ 1)
    (lly_source_almost_radius_pos (by omega : 0 < n) hd a₁) hDensity
    (lly_source_almost_radius_gradual n d a₁) ha₃
    (by linarith only [ha₃Small] : a₃ ≤ 1) hRank₂ hRank₃
    (hEntropy0 d hLower) hEntropy hDimension ζ hShiftGradual
    (fun i => hFirstKernel d hLower hdn i ζ hShiftD)
    (fun i => hSecondKernel d hLower hDegree (Finset.univ.erase i) (hRows i) ζ hShift)
    (fun i => hThirdKernel d hLower hDegree (Finset.univ.erase i) (hRows i) ζ hShift)
    (hFirstAdjoint d hLower hdn ζ hShiftD)
    (hSecondAdjoint d hLower hDegree ζ hShift)
    (hThirdAdjoint d hLower hDegree ζ hShift)
  have hColumnDegree : (72 : ℝ) * (1 + 1) * Real.log (n : ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_right (by linarith only [hC] : (144 : ℝ) ≤ C)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))
    nlinarith only [h, hLower]
  have hColumnExp := dimension_exp_degree_le_rpow (by omega : 0 < n)
    (by norm_num : (0 : ℝ) < 72) hColumnDegree
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
    _ ≤ 5 * (n : ℝ) ^ (-1 : ℝ) +
        (sliceSmallBallDegreeConstant α / Real.sqrt d + 4 * (n : ℝ) ^ (-1 : ℝ)) / α := by
      apply add_le_add
      · nlinarith only [hColumnExp]
      · apply div_le_div_of_nonneg_right _ hα.le
        nlinarith only [hLoadExp]
    _ ≤ 5 / Real.sqrt d + (sliceSmallBallDegreeConstant α / Real.sqrt d + 4 / Real.sqrt d) / α := by
      have hFive : 5 * (n : ℝ) ^ (-1 : ℝ) ≤ 5 / Real.sqrt d := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left hPolynomial (by norm_num : (0 : ℝ) ≤ 5)
      have hFour : 4 * (n : ℝ) ^ (-1 : ℝ) ≤ 4 / Real.sqrt d := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left hPolynomial (by norm_num : (0 : ℝ) ≤ 4)
      exact add_le_add hFive (div_le_div_of_nonneg_right (add_le_add le_rfl hFour) hα.le)
    _ = _ := by ring

end CircularLaw
