import CircularLaw.GaussianRowSpanExtension
import CircularLaw.Hypergeometric
import CircularLaw.TerminalClusterParameters
import CircularLaw.LogarithmicNetCost

/-!
# Uniform source parameters for the fresh-row Gaussian estimate

Both literal codimensions satisfy the full Gaussian interval. The actual
exceptional-coordinate fraction is at most one quarter, the degree is at
most half the dimension, and the slice occupancy error is at most d^-3.
The Gaussian radius transfers to the exact d^(1/96) scale.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem kernelCodimension_gaussian_interval {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    {σ : ℝ} (hσ : σ ≤ 1) (hLog : 2 ≤ Real.log (n : ℝ))
    (hUpper : (d : ℝ) ≤ Real.rpow (Real.log (n : ℝ)) (1 + σ)) :
    (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L ∧
      (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 := by
  have hBounds := kernelCodimension_bounds hd hn hL
  have hLogOne : (1 : ℝ) ≤ Real.log n := by linarith
  have hSquare : (d : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    apply hUpper.trans
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hLogOne (by linarith : (1 + σ : ℝ) ≤ 2)
  have hCube : (d : ℝ) ^ 3 ≤ (Real.log (n : ℝ)) ^ 6 := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hSquare 3 using 1
    ring
  have hSeven : 2 * (d : ℝ) ^ 3 ≤ (Real.log (n : ℝ)) ^ 7 := by
    calc
      _ ≤ Real.log n * (Real.log (n : ℝ)) ^ 6 :=
        mul_le_mul hLog hCube (by positivity) (by linarith)
      _ = _ := by ring
  have hPower : (Real.log (n : ℝ)) ^ 7 ≤ (Real.log (n : ℝ)) ^ 288 :=
    pow_le_pow_right₀ hLogOne (by decide)
  have hSmall : 2 * (d : ℝ) ^ 3 ≤ (Real.log (n : ℝ)) ^ 288 := hSeven.trans hPower
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact ⟨(div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) hSmall).trans hBounds.1,
    hBounds.2⟩

theorem eventually_slice_occupancy_error_cube :
    ∀ᶠ d : ℕ in atTop, Real.exp (-sliceTailRate * d) ≤ 1 / (d : ℝ) ^ 3 := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1)
      sliceTailRate_pos 0 3 (by norm_num)] with d hd hBudget
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [Real.rpow_eq_pow, Real.rpow_one, zero_add] at hBudget
  have hExp : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 3
  calc
    _ ≤ Real.exp (-(3 * Real.log d)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, hExp, one_div]

theorem eventually_fresh_row_gaussian_parameters {C σ : ℝ} (hC : 0 < C) (hσ : σ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      0 < n ∧ 0 < d ∧ 2 * d ≤ n ∧ 4 * d ^ 3 ≤ n ∧
      Real.exp (-sliceTailRate * d) ≤ 1 / (d : ℝ) ^ 3 ∧
      ∀ L : ℕ, IsKernelCodimension n d L →
        0 < L ∧ L ≤ n ∧ (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L ∧
          (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 ∧ structuralClusterFraction n L ≤ 1 / 4 := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1, hLog.eventually_ge_atTop 2,
    eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_slice_occupancy_error_cube,
    eventually_degree_property_uniform hC
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 192) 4)]
    with n hn hLog hConditions hTail hPower
  intro d hBand
  change 2 ≤ Real.log (n : ℝ) at hLog
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have h := hCon.degree_large; omega
  have hCubePow : d ^ 3 ≤ d ^ 4 := Nat.pow_le_pow_right hd (by decide)
  have hOnePow : d ≤ d ^ 4 := by simpa only [pow_one] using Nat.pow_le_pow_right hd (by decide : 1 ≤ 4)
  have hCubic : 4 * d ^ 3 ≤ n := (Nat.mul_le_mul_left 4 hCubePow).trans hCon.dimension_fourth
  have hHalf : 2 * d ≤ n := by have h := hCon.dimension_fourth; omega
  refine ⟨hn, hd, hHalf, hCubic, hTail d hBand.1, ?_⟩
  intro L hL
  have hBounds := kernelCodimension_quotient_bounds hd hCubic hL
  have hRange := kernelCodimension_gaussian_interval hd hCubic hL hσ hLog hBand.2
  have hPow := hPower d hBand.1
  have hInv : Real.rpow (d : ℝ) (-(1 / 192)) ≤ 1 / 4 := by
    simp only [Real.rpow_eq_pow] at hPow ⊢
    rw [Real.rpow_neg (Nat.cast_nonneg d), inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hPow
  exact ⟨hBounds.2.2, hBounds.2.1.trans (Nat.div_le_self _ _), hRange.1, hRange.2,
    (structuralClusterFraction_degree_bounds hd hCubic hL).2.trans hInv⟩

theorem gaussianSourceRadius_degree_comparison {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) {Cg R : ℝ}
    (hCg : 0 ≤ Cg) (hR : 2 * Cg ≤ R) :
    Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)) ≤ Real.exp (-Cg * structuralGrowth n L) := by
  have hGrowth := mul_le_mul_of_nonneg_left (structuralGrowth_degree_bounds hd hn hL).2 hCg
  have hScale := mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg (Nat.cast_nonneg d) (1 / 96))
  apply Real.exp_le_exp.mpr
  simp only [Real.rpow_eq_pow] at hGrowth hScale ⊢
  nlinarith only [hGrowth, hScale]

end CircularLaw
