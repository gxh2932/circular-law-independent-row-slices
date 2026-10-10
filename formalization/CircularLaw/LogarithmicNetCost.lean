import CircularLaw.ProfileExceptionCost

/-!
# Preserving the logarithmic row cost

The K1 decay is a small multiple of `n*log(d)`. Its row factor must
retain `log(d)^2`, giving `2*n*log(log(d))` in the exponent.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem fixedNetSplitCost_loglog_bound {n d K : ℕ} (hn : 0 < n)
    (hLog : 1 ≤ Real.log d) (hK : (n : ℝ) / 2 ≤ K) (hKn : K ≤ n) (R : ℝ) :
    fixedNetSplitCost n d K R ≤
      Real.exp (2 * (d : ℝ) ^ 2 +
        (n : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log (Real.log d))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hKR : (0 : ℝ) < K := by linarith
  have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
  have hRatio : (n : ℝ) / K ≤ 2 := (div_le_iff₀ hKR).mpr (by linarith)
  have hC : 0 ≤ rowSmallBallConstant := by linarith [rowSmallBallConstant_ge_one]
  have hA : 0 ≤ 8 * Real.exp 1 * rowSmallBallConstant * R ^ 2 := by positivity
  have hRow : 2 * fixedNetRowFactor n d K R ≤ fixedNetDegreeFactor R * Real.log d ^ 2 := by
    calc
      _ = (8 * Real.exp 1 * rowSmallBallConstant * R ^ 2) * ((n : ℝ) / K) *
          Real.log d ^ 2 := by unfold fixedNetRowFactor; ring
      _ ≤ ((8 * Real.exp 1 * rowSmallBallConstant * R ^ 2) * 2) * Real.log d ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRatio hA) (sq_nonneg _)
      _ ≤ _ := by unfold fixedNetDegreeFactor; nlinarith [sq_nonneg (Real.log d)]
  have hFactorPos : 0 < fixedNetDegreeFactor R := lt_of_lt_of_le zero_lt_one (fixedNetDegreeFactor_ge_one R)
  have hLogFactor : 0 ≤ Real.log (fixedNetDegreeFactor R) :=
    Real.log_nonneg (fixedNetDegreeFactor_ge_one R)
  have hLogLog : 0 ≤ Real.log (Real.log d) := Real.log_nonneg hLog
  have hLogPos : 0 < Real.log d := by linarith
  have hLogCap : 0 ≤ Real.log (fixedNetDegreeFactor R) + 2 * Real.log (Real.log d) := by linarith
  have hExpLog : Real.exp (2 * Real.log (Real.log d)) = Real.log d ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hLogPos] using Real.exp_nat_mul (Real.log (Real.log d)) 2
  have hPower : (fixedNetDegreeFactor R * Real.log d ^ 2) ^ K =
      Real.exp ((K : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log (Real.log d))) := by
    rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log hFactorPos, hExpLog]
  have hConditioning : 2 * (K : ℝ) * (d : ℝ) ^ 2 / n ≤ 2 * (d : ℝ) ^ 2 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hKnR (sq_nonneg (d : ℝ))]
  unfold fixedNetSplitCost
  calc
    _ ≤ Real.exp (2 * (d : ℝ) ^ 2) * (fixedNetDegreeFactor R * Real.log d ^ 2) ^ K :=
      mul_le_mul (Real.exp_le_exp.mpr hConditioning)
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (fixedNetRowFactor_nonneg n d K R)) hRow K)
        (pow_nonneg (mul_nonneg (by norm_num) (fixedNetRowFactor_nonneg n d K R)) K)
        (Real.exp_nonneg _)
    _ ≤ Real.exp (2 * (d : ℝ) ^ 2) *
        Real.exp ((n : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log (Real.log d))) := by
      rw [hPower]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hKnR hLogCap)) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem eventually_loglog_degree_budget {r : ℝ} (hr : 0 < r) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B + 2 * Real.log (Real.log d) ≤ r * Real.log d := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hRatio : Tendsto (fun d : ℕ => Real.log (Real.log d) / Real.log d) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hLog
  filter_upwards [hLog.eventually_ge_atTop 1, hLog.eventually_ge_atTop (2 * B / r),
    hRatio.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))]
    with d hLogOne hLarge hSmall
  change 1 ≤ Real.log d at hLogOne
  change 2 * B / r ≤ Real.log d at hLarge
  have hConst := (div_le_iff₀ hr).mp hLarge
  have hLogPos : 0 < Real.log d := by linarith
  have hRatioSmall := (div_lt_iff₀ hLogPos).mp hSmall
  linarith

theorem eventually_log_power_degree_budget {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (B b : ℝ) (hb : 0 < b) :
    ∀ᶠ d : ℕ in atTop, B + b * Real.log d ≤ r * Real.rpow (d : ℝ) κ := by
  have hRatio : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) κ) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_real_power_lower hκ (2 * B / r),
    hRatio.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / (2 * b)))]
    with d hd hLarge hSmall
  have hPower : 0 < Real.rpow (d : ℝ) κ := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hConst := (div_le_iff₀ hr).mp hLarge
  have hScaled := (div_lt_iff₀ hPower).mp hSmall
  have hScaled' := mul_le_mul_of_nonneg_left hScaled.le hb.le
  field_simp at hScaled'
  nlinarith only [hConst, hScaled', hr, hb]

end CircularLaw
