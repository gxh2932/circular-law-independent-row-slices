import CircularLaw.LLYSecondNetEntropy
import CircularLaw.RareLLYSourceFirstCoefficients
import CircularLaw.LLYSourceScale
import CircularLaw.LogarithmicNetCost

/-!
# Entropy absorption at the literal second-class source parameters

The final sparse support has density a2/d^(3/4). Its entropy and grid
cost are smaller than the first-rank decay once the degree grows.
First-prefix support choices use the actual logarithmic degree lower
bound. The ceiling, floor and first-rank-one case are retained.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def llySourceSecondDensity (d : ℕ) (a : ℝ) : ℝ := a / (d : ℝ) ^ (3 / 4 : ℝ)

theorem lly_source_epsilon_mul_sqrt_degree {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    llySourceEpsilon n d * Real.sqrt d = Real.sqrt (48 * Real.log (n : ℝ)) := by
  have hRoot : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [llySourceEpsilon, Real.sqrt_div (mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))),
      div_mul_cancel₀ _ hRoot]

theorem lly_source_epsilon_degree_lower {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    Real.sqrt (48 * Real.log 2) ≤ llySourceEpsilon n d * Real.sqrt d := by
  rw [lly_source_epsilon_mul_sqrt_degree hn hd]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn)) (by norm_num)

theorem lly_source_second_density_entropy {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    smallSetEntropy (llySourceSecondDensity d a) =
      llySourceSecondDensity d a * (1 - Real.log a + (3 / 4 : ℝ) * Real.log (d : ℝ)) := by
  unfold smallSetEntropy llySourceSecondDensity
  rw [Real.log_div ha.ne' (by positivity : (d : ℝ) ^ (3 / 4 : ℝ) ≠ 0),
    Real.log_rpow (by exact_mod_cast hd : (0 : ℝ) < d)]
  ring

theorem lly_source_second_tail_entropy_bound {n d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    3 * ((llySourceSecondRank n d a - 1 : ℕ) : ℝ) * Real.log (d : ℝ) +
      (n : ℝ) * smallSetEntropy (llySourceSecondDensity d a) ≤
        (n : ℝ) * llySourceSecondDensity d a *
          (1 + |Real.log a| + (15 / 4 : ℝ) * Real.log (d : ℝ)) := by
  have hPrev : ((llySourceSecondRank n d a - 1 : ℕ) : ℝ) ≤
      llySourceSecondDensity d a * n := by
    have h := (by exact_mod_cast Nat.sub_le (llySourceSecondRank n d a) 1 :
      ((llySourceSecondRank n d a - 1 : ℕ) : ℝ) ≤ llySourceSecondRank n d a).trans
        (lly_source_second_rank_upper (n := n) (d := d) ha.le)
    convert h using 1
    unfold llySourceSecondDensity
    ring
  have hSupportCost := mul_le_mul_of_nonneg_right hPrev (Real.log_natCast_nonneg d)
  have hLogAbs := neg_le_abs (Real.log a)
  have hDensity : 0 ≤ (n : ℝ) * llySourceSecondDensity d a := by
    unfold llySourceSecondDensity
    positivity
  have hEntropy := mul_le_mul_of_nonneg_left hLogAbs hDensity
  rw [lly_source_second_density_entropy hd ha]
  nlinarith only [hSupportCost, hEntropy]

theorem lly_source_second_tail_entropy_absorbed {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hBudget : 1 + |Real.log a₂| + (15 / 4 : ℝ) * Real.log (d : ℝ) ≤
      (a₁ * Real.sqrt (48 * Real.log 2) / (128 * a₂)) * (d : ℝ) ^ (1 / 4 : ℝ)) :
    3 * ((llySourceSecondRank n d a₂ - 1 : ℕ) : ℝ) * Real.log (d : ℝ) +
      (n : ℝ) * smallSetEntropy (llySourceSecondDensity d a₂) ≤
        (llySourceFirstRank n d a₁ : ℝ) * d / 128 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower : Real.sqrt d * (d : ℝ) ^ (1 / 4 : ℝ) = (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hdR]
    norm_num
  rw [show (a₁ * Real.sqrt (48 * Real.log 2) / (128 * a₂)) * (d : ℝ) ^ (1 / 4 : ℝ) =
    (a₁ * Real.sqrt (48 * Real.log 2) * (d : ℝ) ^ (1 / 4 : ℝ)) / (128 * a₂) by ring] at hBudget
  have hScaledBudget := (le_div_iff₀ (by positivity : (0 : ℝ) < 128 * a₂)).mp hBudget
  have hEpsilon := mul_le_mul_of_nonneg_left (lly_source_epsilon_degree_lower hn hd)
    (by positivity : 0 ≤ a₁ * (d : ℝ) ^ (1 / 4 : ℝ))
  have hEpsilonEq : a₁ * (d : ℝ) ^ (1 / 4 : ℝ) *
      (llySourceEpsilon n d * Real.sqrt d) =
        a₁ * llySourceEpsilon n d * (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [show a₁ * (d : ℝ) ^ (1 / 4 : ℝ) * (llySourceEpsilon n d * Real.sqrt d) =
      a₁ * llySourceEpsilon n d * (Real.sqrt d * (d : ℝ) ^ (1 / 4 : ℝ)) by ring, hPower]
  rw [hEpsilonEq] at hEpsilon
  have hRatio : llySourceSecondDensity d a₂ *
      (1 + |Real.log a₂| + (15 / 4 : ℝ) * Real.log (d : ℝ)) ≤ a₁ * llySourceEpsilon n d / 128 := by
    unfold llySourceSecondDensity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hdR _)).mpr
    nlinarith only [hScaledBudget, hEpsilon]
  have hN := mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg (α := ℝ) n)
  have hFirst := lly_source_first_rank_degree_lower (n := n) hd a₁
  apply (lly_source_second_tail_entropy_bound hd ha₂).trans
  nlinarith only [hN, hFirst]

theorem lly_source_log_successor_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n + 1 : ℕ) ≤ 2 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ))
    (by push_cast; nlinarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2)
  rwa [Real.log_pow, Nat.cast_ofNat] at hLog

theorem lly_source_scale_power_lower {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) :
    (llySourceStride n d) ^ llySourceScale n d a ≤ llySourceFirstRank n d a := by
  have hFirst := lly_source_first_rank_pos hn hd ha
  by_cases hOne : llySourceFirstRank n d a = 1
  · simp only [llySourceScale, hOne, Nat.sub_self, Nat.log_zero_right, pow_zero, le_refl]
  · exact (Nat.pow_log_le_self (llySourceStride n d)
      (by omega : llySourceFirstRank n d a - 1 ≠ 0)).trans (Nat.sub_le _ _)

theorem lly_source_second_prefix_density {n d : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    ((llySourceSecondRank n d a - 1 : ℕ) : ℝ) ≤ llySourceSecondDensity d a * n := by
  have h := (by exact_mod_cast Nat.sub_le (llySourceSecondRank n d a) 1 :
    ((llySourceSecondRank n d a - 1 : ℕ) : ℝ) ≤ llySourceSecondRank n d a).trans
      (lly_source_second_rank_upper (n := n) (d := d) ha)
  convert h using 1
  unfold llySourceSecondDensity
  ring

theorem eventually_lly_second_source_entropy_budget {C a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d →
      0 < d ∧ Real.log 484 ≤ Real.log (d : ℝ) ∧ llyThirdNetError d ≤ 1 / 100 ∧
        0 < llySourceSecondDensity d a₂ ∧ llySourceSecondDensity d a₂ ≤ 1 ∧
          5 * (llySourceFirstRank n d a₁ : ℝ) * Real.log (n + 1 : ℕ) +
            (40 * (llySourceFirstRank n d a₁ : ℝ) +
              3 * (llySourceSecondRank n d a₂ - 1 : ℕ) + 5) * Real.log (d : ℝ) +
                (n : ℝ) * smallSetEntropy (llySourceSecondDensity d a₂) ≤
                  (llySourceFirstRank n d a₁ : ℝ) * d / 32 := by
  have hCPos : 0 < C := by linarith
  have hCoefficient : 0 < a₁ * Real.sqrt (48 * Real.log 2) / (128 * a₂) := by
    apply div_pos (mul_pos ha₁ (Real.sqrt_pos.mpr ?_)) (by positivity)
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hLog : ∀ᶠ d : ℕ in atTop, Real.log 484 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  have hDegrees : ∀ᶠ d : ℕ in atTop, 0 < d ∧ Real.log 484 ≤ Real.log (d : ℝ) ∧
      max 100 a₂ ≤ (d : ℝ) ^ (3 / 4 : ℝ) ∧
        45 * Real.log (d : ℝ) ≤ (d : ℝ) / 512 ∧
          1 + |Real.log a₂| + (15 / 4 : ℝ) * Real.log (d : ℝ) ≤
            (a₁ * Real.sqrt (48 * Real.log 2) / (128 * a₂)) * (d : ℝ) ^ (1 / 4 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hLog,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) (max 100 a₂),
      eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (0 : ℝ) < 1 / 512) 0 45 (by norm_num),
      eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 4)
        hCoefficient (1 + |Real.log a₂|) (15 / 4) (by norm_num)]
        with d hd hLog hPower hGrid hTail
    have hGrid' : 45 * Real.log (d : ℝ) ≤ (d : ℝ) / 512 := by
      change 0 + 45 * Real.log (d : ℝ) ≤ (1 / 512) * (d : ℝ) ^ (1 : ℝ) at hGrid
      rw [zero_add, Real.rpow_one] at hGrid
      linarith
    exact ⟨by omega, hLog, hPower, hGrid', hTail⟩
  filter_upwards [eventually_ge_atTop 2, eventually_degree_property_uniform hCPos hDegrees]
    with n hn hDegrees
  intro d hLower
  obtain ⟨hd, hLog, hPower, hGrid, hTail⟩ := hDegrees d hLower
  have hPowPos : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hδ : llyThirdNetError d ≤ 1 / 100 := by
    unfold llyThirdNetError
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) ((le_max_left _ _).trans hPower)
  have hDensityPos : 0 < llySourceSecondDensity d a₂ := div_pos ha₂ hPowPos
  have hDensityOne : llySourceSecondDensity d a₂ ≤ 1 :=
    (div_le_one hPowPos).mpr ((le_max_right _ _).trans hPower)
  refine ⟨hd, hLog, hδ, hDensityPos, hDensityOne, ?_⟩
  have hFirst := lly_source_first_rank_pos hn hd ha₁
  have hFirstOne : (1 : ℝ) ≤ llySourceFirstRank n d a₁ := by exact_mod_cast hFirst
  have hLogN := Real.log_natCast_nonneg n
  have hCScaled := mul_le_mul_of_nonneg_right (by linarith : (5120 : ℝ) ≤ C) hLogN
  have hSuccessor := lly_source_log_successor_le hn
  have hSupportRoot : 5 * Real.log (n + 1 : ℕ) ≤ (d : ℝ) / 512 := by nlinarith
  have hSupportCost := mul_le_mul_of_nonneg_left hSupportRoot
    (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁))
  have hGridCost := mul_le_mul_of_nonneg_left hGrid
    (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁))
  have hFifth := mul_le_mul_of_nonneg_right hFirstOne (Real.log_natCast_nonneg d)
  have hThin := lly_source_second_tail_entropy_absorbed hn hd ha₁ ha₂ hTail
  nlinarith only [hSupportCost, hGridCost, hFifth, hThin,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁)) (Nat.cast_nonneg (α := ℝ) d)]

theorem eventually_lly_second_source_net_count_absorbed {C a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d →
      ((llySecondNonconstantNet n d (llySourceStride n d) (llySourceScale n d a₁)
        (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂) (llyThirdNetResolution d)).card : ℝ) *
          (meanCorrectedScalarNet (llyThirdNetResolution d) d 0 (llyThirdNetError d)).card ≤
            Real.exp ((llySourceFirstRank n d a₁ : ℝ) * d / 32) := by
  filter_upwards [eventually_ge_atTop 2, eventually_lly_second_source_entropy_budget hC ha₁ ha₂]
    with n hn hBudgets
  intro d hLower
  obtain ⟨hd, hLog, hδ, ha, haOne, hBudget⟩ := hBudgets d hLower
  exact lly_second_net_card_product_absorbed hd hLog (lly_source_stride_ge_two hn hd hC hLower)
    (lly_source_scale_power_lower hn hd ha₁) hδ ha haOne
      (lly_source_second_prefix_density ha₂.le) hBudget

end CircularLaw
