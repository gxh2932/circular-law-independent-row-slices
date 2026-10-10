import CircularLaw.CubeConvolution

/-!
# Cube concentration of finite independent sums

Characteristic functions identify the actual sum law after removing any
chosen summand. The checked Esseen estimate bounds enlarged cubes when
all remaining laws have half-mass concentration at the preceding scale.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Convolution

namespace CircularLaw

theorem productSumLaw_remove {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (q : ι) :
    productSumLaw μ = μ q ∗ productSumLaw (fun i : {i : ι // i ≠ q} => μ i.val) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_productSumLaw, charFun_conv, charFun_productSumLaw]
  exact Fintype.prod_eq_mul_prod_subtype_ne _ q

theorem card_remove_one {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι) :
    Fintype.card {i : ι // i ≠ q} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl (fun i : ι => i = q), Fintype.card_subtype_eq]

theorem cubeConcentration_sum_le_summand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (q : ι) (r : ℝ) :
    cubeConcentration (productSumLaw μ) r ≤ cubeConcentration (μ q) r := by
  rw [productSumLaw_remove μ q, Measure.conv_comm]
  exact convolution_cubeConcentration_le _ _ r

theorem half_deficit_product_sum_small_ball {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (hm : 1 ≤ Fintype.card ι)
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hHalf : ∀ i, planarConcentration (μ i) r₀ ≤ 1 / 2) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      (2 * (24 * Real.exp 1 / Real.pi)) * (r / r₀) / Real.sqrt (Fintype.card ι : ℝ) := by
  have hmPos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  have hrPos : 0 < r := hr₀.trans_le hr
  have hLower : (Fintype.card ι : ℝ) / 2 ≤ sumConcentrationDeficit μ r₀ := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (1 / 2 : ℝ) ≤ 1 - planarConcentration (μ i) r₀ by linarith [hHalf i])
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] using h
  have hD : 0 < sumConcentrationDeficit μ r₀ := lt_of_lt_of_le (by positivity) hLower
  have hRoot : Real.sqrt (Fintype.card ι : ℝ) / 2 ≤ Real.sqrt (sumConcentrationDeficit μ r₀) := by
    have hQuarter : (Fintype.card ι : ℝ) / 4 ≤ sumConcentrationDeficit μ r₀ := by linarith
    have h := Real.sqrt_le_sqrt hQuarter
    simpa only [Real.sqrt_div hmPos.le, show Real.sqrt (4 : ℝ) = 2 by norm_num] using h
  have h := (product_sum_esseen_small_ball μ hr₀ hr hD z).trans
    (div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < Real.sqrt (Fintype.card ι : ℝ) / 2) hRoot)
  convert h using 1
  ring

theorem median_cube_sum_bound {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (hm : 1 ≤ Fintype.card ι)
    {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 2 ≤ N)
    (hHalf : ∀ i, cubeConcentration (μ i) (((N - 1 : ℕ) : ℝ) * r) ≤ 1 / 2) :
    cubeConcentration (productSumLaw μ) (((N : ℝ) + 1) * r) ≤
      (12 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt (Fintype.card ι : ℝ) := by
  have hPred : 1 ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hBase : 0 < ((N - 1 : ℕ) : ℝ) * r := by positivity
  have hRatio : (Real.sqrt 2 * (((N : ℝ) + 1) * r)) / (((N - 1 : ℕ) : ℝ) * r) ≤ 6 := by
    apply (div_le_iff₀ hBase).mpr
    have hCast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]
      norm_num
    have hNReal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hsqrt : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    rw [hCast]
    have h := mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ ((N : ℝ) + 1) * r)
    nlinarith
  apply cubeConcentration_le_of_bounds
  intro z
  have hRadius : ((N - 1 : ℕ) : ℝ) * r ≤ Real.sqrt 2 * (((N : ℝ) + 1) * r) := by
    have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have hNReal : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast (show N - 1 ≤ N + 1 by omega)
    have h := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ ((N : ℝ) + 1) * r)
    nlinarith
  have h := (measureReal_mono (planarCube_subset_closedBall z (by positivity))).trans
    (half_deficit_product_sum_small_ball μ hm hBase hRadius
      (fun i => (planarConcentration_le_cubeConcentration (μ i) _).trans (hHalf i)) z)
  exact h.trans (by
    have hScaled := mul_le_mul_of_nonneg_left hRatio
      (by positivity : 0 ≤ 2 * (24 * Real.exp 1 / Real.pi))
    have hDiv := div_le_div_of_nonneg_right hScaled (Real.sqrt_nonneg (Fintype.card ι : ℝ))
    convert hDiv using 1
    ring)

end CircularLaw
