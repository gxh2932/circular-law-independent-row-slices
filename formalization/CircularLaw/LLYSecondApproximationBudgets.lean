import CircularLaw.LLYSecondSourceEntropy
import CircularLaw.LLYSecondSteepNormalization
import CircularLaw.LLYThirdApproximationBudgets
import CircularLaw.LogLogPowerBudgets

/-!
# Source approximation budgets for the actual second-class net

The centered mesh error is compared with sqrt(n1*d), retaining the
source epsilon. The spectral window contributes log(log(d)), which is
bounded uniformly by log(log(n)). Unit-vector residuals use the same
radius already checked for the third class.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem real_quarter_power_square {x : ℝ} (hx : 0 < x) :
    (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
  rw [pow_two, ← Real.rpow_add hx, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by ring,
    ← Real.sqrt_eq_rpow]

theorem lly_second_scaled_mesh_error_budget {n d m : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hFirst : a * llySourceEpsilon n d * n ≤ (m : ℝ) * d)
    (hCoefficient : L ≤ (Real.sqrt (a * Real.sqrt 48) / 60) *
      (Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) :
    Real.sqrt n * (L / (d : ℝ) ^ (1 / 4 : ℝ)) ≤ Real.sqrt ((m : ℝ) * d) / 60 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hSquare := pow_le_pow_left₀ hL hCoefficient 2
  rw [mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ a * Real.sqrt 48),
    real_quarter_power_square hLog] at hSquare
  have hLogRoot : Real.sqrt 48 * Real.sqrt (Real.log (n : ℝ)) =
      Real.sqrt (48 * Real.log (n : ℝ)) := (Real.sqrt_mul (by norm_num) _).symm
  have hCoefficientSquare : 3600 * L ^ 2 ≤ a * Real.sqrt (48 * Real.log (n : ℝ)) := by
    rw [div_mul_eq_mul_div] at hSquare
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 60 ^ 2)).mp hSquare
    rw [mul_assoc, hLogRoot] at h
    nlinarith only [h]
  have hFirstScaled := mul_le_mul_of_nonneg_right hFirst (Real.sqrt_nonneg d)
  have hFirstScaled' : a * (n : ℝ) * Real.sqrt (48 * Real.log (n : ℝ)) ≤
      (m : ℝ) * d * Real.sqrt d := by
    calc
      _ = (a * llySourceEpsilon n d * n) * Real.sqrt d := by
        rw [show (a * llySourceEpsilon n d * n) * Real.sqrt d =
          a * (n : ℝ) * (llySourceEpsilon n d * Real.sqrt d) by ring,
            lly_source_epsilon_mul_sqrt_degree hn hd]
      _ ≤ _ := hFirstScaled
  have hCoefficientN := mul_le_mul_of_nonneg_left hCoefficientSquare (Nat.cast_nonneg (α := ℝ) n)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), real_quarter_power_square hdR,
    div_pow, Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ) * d)]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hdR)).mpr
  nlinarith only [hCoefficientN, hFirstScaled']

theorem eventually_lly_second_source_grid_adjoint_error_small {C C₀ a₁ : ℝ}
    (hC : 0 < C) (hC₀ : 0 ≤ C₀) (ha₁ : 0 < a₁) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      0 < d ∧ llyThirdNetError d ≤ 1 / 100 ∧
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          ((C₀ * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * llyThirdNetError d) +
            (C₀ * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
              (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤
                Real.sqrt ((llySourceFirstRank n d a₁ : ℝ) * d) / 60 := by
  have hCoefficient : 0 < Real.sqrt (a₁ * Real.sqrt 48) / 60 := by
    apply div_pos (Real.sqrt_pos.mpr ?_) (by norm_num)
    exact mul_pos ha₁ (Real.sqrt_pos.mpr (by norm_num))
  have hLogDegree : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 2,
    eventually_loglog_power_dimension_budget (by norm_num : (0 : ℝ) < 1 / 4)
      hCoefficient (3 * C₀ + 1) 3 (by norm_num),
    eventually_degree_property_uniform hC (eventually_ge_atTop 1),
    eventually_degree_property_uniform hC hLogDegree,
    eventually_degree_property_uniform hC
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) 100)]
        with n hn hBudget hDegrees hLogs hPowers
  intro d hLower hdn
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hLogD := hLogs d hLower
  have hδ : llyThirdNetError d ≤ 1 / 100 := by
    unfold llyThirdNetError
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (hPowers d hLower)
  refine ⟨hd, hδ, ?_⟩
  intro ζ hShift
  have hLogLog : Real.log (Real.log (d : ℝ)) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log (by linarith : 0 < Real.log (d : ℝ))
      (Real.log_le_log (by exact_mod_cast hd : (0 : ℝ) < d) (by exact_mod_cast hdn))
  have hLogLogNonneg := Real.log_nonneg hLogD
  apply (lly_third_grid_adjoint_error_bound hd hC₀ ζ hShift).trans
  exact lly_second_scaled_mesh_error_budget hn hd ha₁ (by linarith :
    0 ≤ 3 * C₀ + 3 * Real.log (Real.log (d : ℝ)) + 1)
      (lly_source_first_rank_degree_lower (n := n) hd a₁) (by linarith)

theorem lly_second_norm_constant_ge_sqrt {n d r : ℕ} (hd : 0 < d) :
    Real.sqrt n ≤ llySecondSteepNormConstant n d r := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPower : 1 ≤ (6 * (d : ℝ)) ^ (r + 1) := one_le_pow₀ (by linarith)
  simpa only [llySecondSteepNormConstant, mul_one] using
    mul_le_mul_of_nonneg_left hPower (Real.sqrt_nonneg n)

theorem lly_second_norm_constant_le_third {n d r : ℕ} (hd : 0 < d) :
    llySecondSteepNormConstant n d r ≤ llyThirdSteepNormConstant n d r := by
  have hPower : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  simpa only [llySecondSteepNormConstant, llyThirdSteepNormConstant, mul_one] using
    mul_le_mul_of_nonneg_left hPower
      (by positivity : 0 ≤ Real.sqrt n * (6 * (d : ℝ)) ^ (r + 1))

theorem lly_second_radius_unit_image_budget {n d r m : ℕ}
    (hn : 3600 ≤ n) (hd : 0 < d) (hm : 0 < m) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδOne : δ ≤ 1)
    (hRadius : llySecondSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n) :
    llySecondSteepNormConstant n d r * ((ρ / Real.sqrt n) * ρ / Real.sqrt n) ≤
      Real.sqrt ((m : ℝ) * d) / 60 := by
  have hnR : (3600 : ℝ) ≤ n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < n)
  have hB := lly_second_norm_constant_ge_sqrt (n := n) (r := r) hd
  have hρδ : ρ ≤ δ := by
    have h := (mul_le_mul_of_nonneg_right hB hρ).trans hRadius
    apply (mul_le_mul_iff_right₀ hRoot).mp
    simpa only [mul_comm] using h
  have hρOne : ρ ≤ 1 := hρδ.trans hδOne
  have hBρ : llySecondSteepNormConstant n d r * ρ ≤ Real.sqrt n :=
    hRadius.trans (by nlinarith [Real.sqrt_nonneg n])
  have hNumerator : llySecondSteepNormConstant n d r * ρ ^ 2 ≤ Real.sqrt n := by
    have hScaled := mul_le_mul_of_nonneg_right hBρ hρ
    have hρScaled := mul_le_mul_of_nonneg_left hρOne hRoot.le
    nlinarith only [hScaled, hρScaled]
  have hIdentity : (ρ / Real.sqrt n) * ρ / Real.sqrt n = ρ ^ 2 / n := by
    rw [div_mul_eq_mul_div, div_div, Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ n)]
    ring
  rw [hIdentity, ← mul_div_assoc]
  have hRootLarge : (60 : ℝ) ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (by norm_num) hRoot.le).mp
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ n)]
    norm_num
    exact hn
  have hNRoot : Real.sqrt n / (n : ℝ) = 1 / Real.sqrt n := by
    apply (div_eq_div_iff (by linarith : (n : ℝ) ≠ 0) hRoot.ne').mpr
    rw [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ n), one_mul]
  have hProductOne : (1 : ℝ) ≤ (m : ℝ) * d := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  calc
    _ ≤ Real.sqrt n / (n : ℝ) := div_le_div_of_nonneg_right hNumerator (by linarith)
    _ = 1 / Real.sqrt n := hNRoot
    _ ≤ 1 / 60 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hRootLarge
    _ ≤ _ := div_le_div_of_nonneg_right (by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hProductOne) (by norm_num)

end CircularLaw
