import CircularLaw.LLYSourceRadiusExponent
import CircularLaw.HermitizationCutoffBudgets

/-!
# The checked radius supplies both manuscript regularization scales

The literal floor stride gives a logarithmic-exponent threshold under
the basic logarithmic degree cutoff, and one fixed power threshold
above every superlogarithmic cutoff.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def llySourceLoglogRatioConstant : ℝ :=
  8 + (Real.log 6 + 2 + 2 * Real.log 1920000) / Real.log 2

theorem lly_source_loglog_ratio_constant_ge_eight : 8 ≤ llySourceLoglogRatioConstant := by
  have hLog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hLogC : 0 ≤ Real.log 1920000 := Real.log_nonneg (by norm_num)
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hFraction : 0 ≤ (Real.log 6 + 2 + 2 * Real.log 1920000) / Real.log 2 := by positivity
  unfold llySourceLoglogRatioConstant
  linarith only [hFraction]

theorem lly_source_stride_ratio_loglog {n d : ℕ} (hn : 2 ≤ n) (hd : 6 ≤ d)
    {C : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d)
    (hLL : 1 ≤ Real.log (Real.log (n : ℝ))) :
    Real.log (6 * (d : ℝ)) ≤ (llySourceLoglogRatioConstant * Real.log (Real.log (n : ℝ))) *
      Real.log (llySourceStride n d : ℝ) := by
  have hdPos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hStride := lly_source_stride_ge_two hn hdPos hC hDegree
  have hLogStride : Real.log 2 ≤ Real.log (llySourceStride n d : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hStride)
  have hLog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hLog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hLogC : 0 ≤ Real.log 1920000 := Real.log_nonneg (by norm_num)
  have hK := lly_source_loglog_ratio_constant_ge_eight
  have hBudget := lly_source_stride_log_degree_budget hn hdPos hC hDegree
  have hKProduct : llySourceLoglogRatioConstant * Real.log 2 =
      8 * Real.log 2 + (Real.log 6 + 2 + 2 * Real.log 1920000) := by
    unfold llySourceLoglogRatioConstant
    field_simp
  have hBase : Real.log (6 * (d : ℝ)) ≤ 2 * Real.log (d : ℝ) := by
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdR.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by exact_mod_cast hd : (6 : ℝ) ≤ d)
    linarith only [h]
  by_cases hSmall : Real.log (d : ℝ) ≤ 2 * Real.log (Real.log (n : ℝ)) + 2 * Real.log 1920000
  · have hExpand : Real.log (6 * (d : ℝ)) ≤
        (Real.log 6 + 2 + 2 * Real.log 1920000) * Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdR.ne']
      have h6 := mul_le_mul_of_nonneg_left hLL hLog6
      have hCScaled := mul_le_mul_of_nonneg_left hLL hLogC
      nlinarith only [hSmall, h6, hCScaled]
    have hCoeff : Real.log 6 + 2 + 2 * Real.log 1920000 ≤
        llySourceLoglogRatioConstant * Real.log 2 := by
      rw [hKProduct]
      linarith only [hLog2]
    have hScaled := mul_le_mul_of_nonneg_right hCoeff (by linarith only [hLL] :
      0 ≤ Real.log (Real.log (n : ℝ)))
    apply hExpand.trans
    calc
      _ ≤ (llySourceLoglogRatioConstant * Real.log 2) * Real.log (Real.log (n : ℝ)) := hScaled
      _ = (llySourceLoglogRatioConstant * Real.log (Real.log (n : ℝ))) * Real.log 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLogStride (by positivity)
  · have hLarge : Real.log (d : ℝ) ≤ 4 * Real.log (llySourceStride n d : ℝ) := by
      nlinarith only [hBudget, le_of_not_ge hSmall]
    have hEight : Real.log (6 * (d : ℝ)) ≤ 8 * Real.log (llySourceStride n d : ℝ) := by
      linarith only [hBase, hLarge]
    have hKLL : 8 ≤ llySourceLoglogRatioConstant * Real.log (Real.log (n : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hLL (by linarith only [hK] : 0 ≤ llySourceLoglogRatioConstant)
      nlinarith only [h, hK]
    exact hEight.trans (mul_le_mul_of_nonneg_right hKLL (hLog2.le.trans hLogStride))

theorem lly_source_stride_ratio_superlog {n d : ℕ} (hn : 2 ≤ n) (hd : 6 ≤ d)
    {C ε : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d) (hε : 0 < ε)
    (hLowerLog : (1 + ε) * Real.log (Real.log (n : ℝ)) ≤ Real.log (d : ℝ))
    (hOffset : Real.log 1920000 ≤ (ε / 2) * Real.log (Real.log (n : ℝ))) :
    Real.log (6 * (d : ℝ)) ≤ (8 * (1 + ε) / ε) * Real.log (llySourceStride n d : ℝ) := by
  have hdPos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hBudget := lly_source_stride_log_degree_budget hn hdPos hC hDegree
  have hBudgetScaled := mul_le_mul_of_nonneg_left hBudget (by linarith only [hε] : 0 ≤ 1 + ε)
  have hOffsetScaled := mul_le_mul_of_nonneg_left hOffset (by linarith only [hε] : 0 ≤ 1 + ε)
  have hLowerScaled := mul_le_mul_of_nonneg_left hLowerLog (by linarith only [hε] : 0 ≤ 1 + ε / 2)
  have hBase : Real.log (6 * (d : ℝ)) ≤ 2 * Real.log (d : ℝ) := by
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdR.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by exact_mod_cast hd : (6 : ℝ) ≤ d)
    linarith only [h]
  apply hBase.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hε).mpr
  nlinarith only [hBudgetScaled, hOffsetScaled, hLowerScaled]

theorem eventually_lly_source_lower_cutoff_radius {C a : ℝ} (hC : 1920000 ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      lowerHermitizationCutoff n (2 * llySourceLoglogRatioConstant + 12) ≤
        (llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n := by
  have hLL : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 20, hLL,
    eventually_degree_property_uniform (by linarith only [hC] : 0 < C) (eventually_ge_atTop 6)]
      with n hn hLL hDegrees
  intro d hLower hdn
  have hdLarge := hDegrees d hLower
  have hd : 0 < d := by omega
  have hK := lly_source_loglog_ratio_constant_ge_eight
  have hRadius := lly_source_minimum_threshold_of_stride_ratio hn hd hdn hC hLower ha haOne
    (by positivity : 0 ≤ llySourceLoglogRatioConstant * Real.log (Real.log (n : ℝ)))
    (lly_source_stride_ratio_loglog (by omega : 2 ≤ n) hdLarge hC hLower hLL)
  apply le_trans _ hRadius
  unfold lowerHermitizationCutoff
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
  nlinarith only [hLL]

theorem eventually_lly_source_superlog_cutoff_radius {C a ε : ℝ} (hC : 1920000 ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) →
        polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12) ≤
          (llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n := by
  have hLL : ∀ᶠ n : ℕ in atTop, 2 * Real.log 1920000 / ε ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 20, hLL,
    eventually_degree_property_uniform (by linarith only [hC] : 0 < C) (eventually_ge_atTop 6)]
      with n hn hLL hDegrees
  intro d hDegree hdn hLower
  have hdLarge := hDegrees d hDegree
  have hd : 0 < d := by omega
  have hLogN : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 2 ≤ n by omega) : (1 : ℝ) < n)
  have hLowerLog := Real.le_log_of_rpow_le hLogN hLower
  have hOffset : Real.log 1920000 ≤ (ε / 2) * Real.log (Real.log (n : ℝ)) := by
    have h := (div_le_iff₀ hε).mp hLL
    nlinarith only [h]
  exact lly_source_minimum_threshold_of_stride_ratio hn hd hdn hC hDegree ha haOne
    (by positivity : 0 ≤ 8 * (1 + ε) / ε)
    (lly_source_stride_ratio_superlog (by omega : 2 ≤ n) hdLarge hC hDegree hε hLowerLog hOffset)

end CircularLaw
