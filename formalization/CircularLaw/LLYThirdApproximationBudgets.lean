import CircularLaw.LLYThirdGridBudgets
import CircularLaw.LLYThirdSteepNormalization
import CircularLaw.LogarithmicNetCost

/-!
# Discharging the third-class approximation budget in the spectral window

At the `d^(-3/4)` mesh, the centered-adjoint error is at most a fixed
constant plus `log(log(d))`, divided by `d^(1/4)`, times `sqrt(n)`.
This tends to zero. The normalized unit-vector residual at `rho^2/n`
is also controlled by the same actual third-class radius.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_third_norm_constant_ge_sqrt {n d r : ℕ} (hd : 0 < d) :
    Real.sqrt n ≤ llyThirdSteepNormConstant n d r := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPower : 1 ≤ (6 * (d : ℝ)) ^ (r + 1) := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 6 * d)
  have hDegree : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hdR (by norm_num)
  have hBoth : 1 ≤ (6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hBoth (Real.sqrt_nonneg n)
  simpa only [mul_one, llyThirdSteepNormConstant, mul_assoc] using h

theorem lly_third_grid_adjoint_error_bound {n d : ℕ} (hd : 0 < d) {C₀ L : ℝ}
    (hC₀ : 0 ≤ C₀) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Real.sqrt d * L) :
    ((C₀ * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * llyThirdNetError d) +
      (C₀ * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤
      Real.sqrt n * ((3 * C₀ + 3 * L + 1) / (d : ℝ) ^ (1 / 4 : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRootOne : (1 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hdR.le]
    simpa only [one_pow] using hdOne
  have hError : 0 ≤ llyThirdNetError d := by unfold llyThirdNetError; positivity
  let T := C₀ * Real.sqrt d + ‖ζ‖
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hFine : Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d) ≤ llyThirdNetError d / d := by
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right (llyThirdNetResolution_error hd) hdR.le
  have hRatio : (T + d) / d ≤ T + 1 := by
    apply (div_le_iff₀ hdR).mpr
    have h := mul_le_mul_of_nonneg_left hdOne hT
    nlinarith
  have hScalar : (T + d) * (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d)) ≤
      (T + 1) * llyThirdNetError d := by
    calc
      _ ≤ (T + d) * (llyThirdNetError d / d) := mul_le_mul_of_nonneg_left hFine (by positivity)
      _ = ((T + d) / d) * llyThirdNetError d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hRatio hError
  have hScalarRoot := mul_le_mul_of_nonneg_left hScalar (Real.sqrt_nonneg n)
  have hTUpper : T ≤ Real.sqrt d * (C₀ + L) := by dsimp only [T]; nlinarith [hShift]
  have hCoeff : 3 * T + 1 ≤ Real.sqrt d * (3 * C₀ + 3 * L + 1) := by nlinarith
  have hPower : Real.sqrt d * (d : ℝ) ^ (1 / 4 : ℝ) = (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hdR]
    norm_num
  have hCancel : llyThirdNetError d * Real.sqrt d = 1 / (d : ℝ) ^ (1 / 4 : ℝ) := by
    unfold llyThirdNetError
    rw [one_div_mul_eq_div]
    apply (div_eq_div_iff (by positivity : (d : ℝ) ^ (3 / 4 : ℝ) ≠ 0)
      (by positivity : (d : ℝ) ^ (1 / 4 : ℝ) ≠ 0)).mpr
    simpa only [one_mul] using hPower
  calc
    _ ≤ Real.sqrt n * llyThirdNetError d * (3 * T + 1) := by
      change T * (2 * Real.sqrt n * llyThirdNetError d) +
        (C₀ * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d)) ≤ _
      dsimp only [T] at hScalarRoot
      nlinarith
    _ ≤ Real.sqrt n * llyThirdNetError d * (Real.sqrt d * (3 * C₀ + 3 * L + 1)) :=
      mul_le_mul_of_nonneg_left hCoeff (mul_nonneg (Real.sqrt_nonneg _) hError)
    _ = _ := by rw [show Real.sqrt n * llyThirdNetError d * (Real.sqrt d * (3 * C₀ + 3 * L + 1)) =
      Real.sqrt n * (llyThirdNetError d * Real.sqrt d) * (3 * C₀ + 3 * L + 1) by ring, hCancel]; ring

theorem eventually_lly_third_grid_adjoint_error_small {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧ llyThirdNetError d ≤ 1 / 100 ∧
      ∀ n : ℕ, ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        ((C₀ * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * llyThirdNetError d) +
          (C₀ * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
            (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤ Real.sqrt n / 12 := by
  have hLog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 1, hLog,
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) 100,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 12) (3 * C₀ + 1) 3 (by norm_num)]
      with d hd hLog hPower hBudget
  have hdPos : 0 < d := by omega
  have hError : llyThirdNetError d ≤ 1 / 100 := by
    unfold llyThirdNetError
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hPower
  refine ⟨hdPos, hError, ?_⟩
  intro n ζ hShift
  have hLogLogUpper : Real.log (Real.log (d : ℝ)) ≤ Real.log (d : ℝ) :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (d : ℝ))).trans (by linarith)
  have hSmall : 3 * C₀ + 3 * Real.log (Real.log (d : ℝ)) + 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) / 12 := by
    change 3 * C₀ + 1 + 3 * Real.log (d : ℝ) ≤
      (1 / 12) * (d : ℝ) ^ (1 / 4 : ℝ) at hBudget
    linarith
  apply (lly_third_grid_adjoint_error_bound hdPos hC₀ ζ hShift).trans
  have hRatio : (3 * C₀ + 3 * Real.log (Real.log (d : ℝ)) + 1) / (d : ℝ) ^ (1 / 4 : ℝ) ≤ 1 / 12 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hdPos : (0 : ℝ) < d) _)).mpr
    linarith
  convert mul_le_mul_of_nonneg_left hRatio (Real.sqrt_nonneg n) using 1
  ring

theorem lly_third_radius_unit_image_budget {n d r : ℕ} (hn : 12 ≤ n) (hd : 0 < d)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδOne : δ ≤ 1)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n) :
    llyThirdSteepNormConstant n d r * ((ρ / Real.sqrt n) * ρ / Real.sqrt n) ≤ Real.sqrt n / 12 := by
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < n)
  have hB := lly_third_norm_constant_ge_sqrt (n := n) (r := r) hd
  have hρδ : ρ ≤ δ := by
    have h := (mul_le_mul_of_nonneg_right hB hρ).trans hRadius
    apply (mul_le_mul_iff_right₀ hRoot).mp
    simpa only [mul_comm] using h
  have hProduct : δ * ρ ≤ 1 := by nlinarith
  have hScaled := mul_le_mul_of_nonneg_right hRadius hρ
  have hScaledProduct := mul_le_mul_of_nonneg_right hProduct hRoot.le
  have hNumerator : llyThirdSteepNormConstant n d r * ρ ^ 2 ≤ Real.sqrt n := by nlinarith
  have hIdentity : (ρ / Real.sqrt n) * ρ / Real.sqrt n = ρ ^ 2 / n := by
    rw [div_mul_eq_mul_div, div_div,
      show Real.sqrt n * Real.sqrt n = (n : ℝ) by
        simpa only [pow_two] using Real.sq_sqrt (by linarith : (0 : ℝ) ≤ n)]
    ring
  rw [hIdentity, ← mul_div_assoc]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
  have hScaleN := mul_le_mul_of_nonneg_left hnR hRoot.le
  nlinarith

theorem eventually_lly_third_unit_net_approximation_budget {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧ llyThirdNetError d ≤ 1 / 100 ∧
      ∀ n r : ℕ, 12 ≤ n → ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d r * ρ ≤ llyThirdNetError d * Real.sqrt n →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          llyThirdSteepNormConstant n d r * ((ρ / Real.sqrt n) * ρ / Real.sqrt n) +
            ((C₀ * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * llyThirdNetError d) +
              (C₀ * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
                (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤ Real.sqrt n / 3 := by
  filter_upwards [eventually_lly_third_grid_adjoint_error_small hC₀] with d hData
  refine ⟨hData.1, hData.2.1, ?_⟩
  intro n r hn ρ hρ hRadius ζ hShift
  have hError := hData.2.2 n ζ hShift
  have hUnit := lly_third_radius_unit_image_budget hn hData.1 hρ
    (by linarith [hData.2.1] : llyThirdNetError d ≤ 1) hRadius
  linarith [Real.sqrt_nonneg n]

end CircularLaw
