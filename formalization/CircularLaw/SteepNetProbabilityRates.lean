import CircularLaw.SourceSteepNetLemma

/-!
# Absorbing the actual steep-net counts

The T1 entropy costs `log(d)/d^(1/6)` of its small-ball exponent. The T2
floor ratio has logarithm at least `log(d)/6`; a fixed small positive a3
then leaves an exponential rate in `n*log(d)`. Witness failure remains a
separate summand throughout.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem steep_net_T1_entropy_absorbed {n d : ℕ} {r : ℝ}
    (hd : 0 < d) (hr : 0 < r)
    (hDegree : 14 * Real.log (d : ℝ) ≤ r * Real.rpow (d : ℝ) (1 / 6)) :
    7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ) ≤
      (r / 2) * (d : ℝ) * firstSteepScale n d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hDen : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdR _
  have hSecond := (le_div_iff₀ hDen).mp
    (Nat.floor_le (div_nonneg (Nat.cast_nonneg n) hDen.le) :
      (secondSteepScale n d : ℝ) ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3))
  have hFirst := (div_le_iff₀ hRoot).mp (firstSteepScale_density_lower (n := n) hd)
  have hPower : Real.rpow (d : ℝ) (1 / 6) * Real.sqrt d = Real.rpow (d : ℝ) (2 / 3) := by
    simp only [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
    rw [← Real.rpow_add hdR, show (1 / 6 : ℝ) + 1 / 2 = 2 / 3 by norm_num]
  apply (mul_le_mul_iff_left₀ hRoot).mp
  calc
    _ = (14 * Real.log (d : ℝ)) * ((secondSteepScale n d : ℝ) * Real.sqrt d / 2) := by ring
    _ ≤ (r * Real.rpow (d : ℝ) (1 / 6)) * ((secondSteepScale n d : ℝ) * Real.sqrt d / 2) :=
      mul_le_mul_of_nonneg_right hDegree (by positivity)
    _ = (r / 2) * (secondSteepScale n d : ℝ) * (Real.rpow (d : ℝ) (1 / 6) * Real.sqrt d) := by ring
    _ = (r / 2) * ((secondSteepScale n d : ℝ) * Real.rpow (d : ℝ) (2 / 3)) := by rw [hPower]; ring
    _ ≤ (r / 2) * n := mul_le_mul_of_nonneg_left hSecond (by positivity)
    _ ≤ (r / 2) * ((d : ℝ) * firstSteepScale n d * Real.sqrt d) :=
      mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = _ := by ring

theorem eventually_steep_net_T1_entropy {r : ℝ} (hr : 0 < r) :
    ∀ᶠ d : ℕ in atTop, 14 * Real.log (d : ℝ) ≤ r * Real.rpow (d : ℝ) (1 / 6) := by
  have hLimit : Tendsto (fun d : ℕ => Real.log (d : ℝ) / Real.rpow (d : ℝ) (1 / 6))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hSmall := hLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 14))
  filter_upwards [hSmall, eventually_ge_atTop 1] with d hSmall hd
  have hPower : 0 < Real.rpow (d : ℝ) (1 / 6) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd : (0 : ℝ) < d) _
  have hScaled := (div_lt_iff₀ hPower).mp hSmall
  linarith

theorem steep_net_T1_probability_absorbed {n d : ℕ} {r : ℝ}
    (hd : 0 < d) (hr : 0 < r)
    (hDegree : 14 * Real.log (d : ℝ) ≤ r * Real.rpow (d : ℝ) (1 / 6))
    (hCount : ((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card ≤
      Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ))) :
    ((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card *
        Real.exp (-r * (d : ℝ) * firstSteepScale n d) ≤
      Real.exp (-(r / 2) * n / Real.sqrt d) := by
  have hCost := steep_net_T1_entropy_absorbed (n := n) hd hr hDegree
  calc
    _ ≤ Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ)) *
        Real.exp (-r * (d : ℝ) * firstSteepScale n d) :=
      mul_le_mul_of_nonneg_right hCount (Real.exp_pos _).le
    _ = Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ) +
        (-r * (d : ℝ) * firstSteepScale n d)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(r / 2) * (d : ℝ) * firstSteepScale n d) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ = -(r / 2) * ((d : ℝ) * firstSteepScale n d) := by ring
        _ ≤ -(r / 2) * ((n : ℝ) / Real.sqrt d) :=
          mul_le_mul_of_nonpos_left (firstSteepScale_density_lower (n := n) hd) (by linarith)
        _ = _ := by ring

theorem secondSteepScale_ratio_lower {n d : ℕ} (hd : 0 < d) (hDimension : 2 * d ≤ n) :
    Real.rpow (d : ℝ) (1 / 3) / 2 ≤ (d : ℝ) * secondSteepScale n d / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hPower : Real.rpow (d : ℝ) (2 / 3) * Real.rpow (d : ℝ) (1 / 3) = (d : ℝ) := by
    rw [positive_degree_power_mul hd, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num]
    simp only [Real.rpow_eq_pow, Real.rpow_one]
  apply (le_div_iff₀ hnR).mpr
  calc
    _ ≤ (2 * (secondSteepScale n d : ℝ) * Real.rpow (d : ℝ) (2 / 3)) *
        (Real.rpow (d : ℝ) (1 / 3) / 2) := by
      have h := mul_le_mul_of_nonneg_right (secondSteepScale_density_lower hd hDimension)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by norm_num) :
          0 ≤ Real.rpow (d : ℝ) (1 / 3) / 2)
      convert h using 1
      ring
    _ = (secondSteepScale n d : ℝ) * (Real.rpow (d : ℝ) (2 / 3) * Real.rpow (d : ℝ) (1 / 3)) := by ring
    _ = _ := by rw [hPower]; ring

theorem secondSteepScale_log_ratio_lower {n d : ℕ}
    (hd : 0 < d) (hDimension : 2 * d ≤ n) (hLog : 6 * Real.log 2 ≤ Real.log (d : ℝ)) :
    Real.log (d : ℝ) / 6 ≤ Real.log ((d : ℝ) * secondSteepScale n d / n) := by
  have hPowerPos : 0 < Real.rpow (d : ℝ) (1 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have h := Real.log_le_log (div_pos hPowerPos (by norm_num)) (secondSteepScale_ratio_lower hd hDimension)
  rw [Real.log_div hPowerPos.ne' (by norm_num : (2 : ℝ) ≠ 0), positive_degree_power_log hd] at h
  linarith

theorem steep_net_T2_rate_lower {n d : ℕ} {r : ℝ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (hr : 0 < r)
    (hLog : 0 ≤ Real.log (d : ℝ)) (hLogLarge : 6 * Real.log 2 ≤ Real.log (d : ℝ)) :
    (r / 2400) * n * Real.log (d : ℝ) ≤
      r * (d : ℝ) * equalBlockScale n d * Real.log ((d : ℝ) * secondSteepScale n d / n) := by
  have hDensity := equalBlockScale_density_lower hd hn
  have hRatio := secondSteepScale_log_ratio_lower hd (by omega : 2 * d ≤ n) hLogLarge
  have hProduct := mul_le_mul hDensity hRatio (by linarith : 0 ≤ Real.log (d : ℝ) / 6)
    (by positivity : (0 : ℝ) ≤ (d : ℝ) * equalBlockScale n d)
  have hScaled := mul_le_mul_of_nonneg_left hProduct hr.le
  convert hScaled using 1 <;> ring

theorem steep_net_T2_probability_absorbed {n d : ℕ} {a₃ r : ℝ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (ha : 0 ≤ a₃) (hr : 0 < r)
    (haSmall : 7 * a₃ ≤ r / 4800)
    (hLog : 0 ≤ Real.log (d : ℝ)) (hLogLarge : 6 * Real.log 2 ≤ Real.log (d : ℝ))
    (hCount : ((sourceT2Net n d a₃).card : ℝ) *
        (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card ≤
      Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ))) :
    ((sourceT2Net n d a₃).card : ℝ) * (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card *
        Real.exp (-r * (d : ℝ) * equalBlockScale n d * Real.log ((d : ℝ) * secondSteepScale n d / n)) ≤
      Real.exp (-(r / 4800) * n * Real.log (d : ℝ)) := by
  have hThird : (thirdSteepScale n a₃ : ℝ) ≤ a₃ * n :=
    Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have hCost : 7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ) ≤
      (r / 4800) * n * Real.log (d : ℝ) := by
    have hFirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hThird (by norm_num : (0 : ℝ) ≤ 7)) hLog
    have hSecond := mul_le_mul_of_nonneg_right haSmall
      (mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hLog)
    nlinarith
  have hRate := steep_net_T2_rate_lower hd hn hr hLog hLogLarge
  calc
    _ ≤ Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ)) *
        Real.exp (-r * (d : ℝ) * equalBlockScale n d * Real.log ((d : ℝ) * secondSteepScale n d / n)) :=
      mul_le_mul_of_nonneg_right hCount (Real.exp_pos _).le
    _ = Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ) +
        (-r * (d : ℝ) * equalBlockScale n d * Real.log ((d : ℝ) * secondSteepScale n d / n))) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem two_exponential_rates_absorbed {r₁ r₂ q : ℝ}
    (hq : 0 ≤ q) (hLarge : 2 * Real.log 2 ≤ min r₁ r₂ * q) :
    Real.exp (-r₁ * q) + Real.exp (-r₂ * q) ≤ Real.exp (-(min r₁ r₂ / 2) * q) := by
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left r₁ r₂) hq
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right r₁ r₂) hq
  calc
    _ ≤ Real.exp (-min r₁ r₂ * q) + Real.exp (-min r₁ r₂ * q) :=
      add_le_add (Real.exp_le_exp.mpr (by linarith)) (Real.exp_le_exp.mpr (by linarith))
    _ = Real.exp (Real.log 2) * Real.exp (-min r₁ r₂ * q) := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring
    _ = Real.exp (Real.log 2 + (-min r₁ r₂ * q)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end CircularLaw
