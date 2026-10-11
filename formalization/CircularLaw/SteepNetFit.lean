import CircularLaw.SourceSteepNetLemma
import CircularLaw.SteepNetSmallBall

/-!
# Finite and uniform fit of the source steep nets

The literal ceiling and floor ranks satisfy the ordered equal-block
conditions. The actual matrix approximation radius fits both checked
small-ball radii once the degree is large. The dimension threshold is
uniform over all degrees in the lower band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem secondSteepScale_upper (n d : ℕ) :
    (secondSteepScale n d : ℝ) ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3) :=
  Nat.floor_le (div_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg d) _))

theorem source_kernel_dimension_four_hundred {n d : ℕ} (h : SourceKernelConditions n d) :
    400 * d ≤ n ∧ (200 : ℝ) ≤ Real.sqrt d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hSquare := Nat.pow_le_pow_right hd (by decide : 2 ≤ 4)
  have hDimension := h.dimension_fourth
  have hDegree := h.degree_large
  constructor
  · nlinarith
  · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    exact_mod_cast hDegree

theorem source_first_second_rank_fit {n d : ℕ} (h : SourceKernelConditions n d) :
    firstSteepScale n d ≤ secondSteepScale n d ∧
      secondSteepScale n d + firstSteepScale n d ≤ n ∧ 4 * secondSteepScale n d ≤ n := by
  have hDimension := source_kernel_dimension_twice_degree h
  have hd := hDimension.2.1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot := (source_kernel_dimension_four_hundred h).2
  have hFirst := firstSteepScale_small hd h.dimension_root hRoot
  have hFirstFour : 4 * firstSteepScale n d ≤ n :=
    (Nat.mul_le_mul_right (firstSteepScale n d) (by nlinarith : 4 ≤ 100 * d)).trans hFirst
  have hDen : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hRootLower : Real.sqrt d ≤ Real.rpow (d : ℝ) (2 / 3) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using
      Real.rpow_le_rpow_of_exponent_le hdR (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
  have hDenUpper : Real.rpow (d : ℝ) (2 / 3) ≤ (d : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hdR (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hSecondProd := (le_div_iff₀ hDen).mp (secondSteepScale_upper n d)
  have hSecondFourR : (4 : ℝ) * secondSteepScale n d ≤ n := by
    have hScaled := mul_le_mul_of_nonneg_left (hRoot.trans hRootLower)
      (Nat.cast_nonneg (secondSteepScale n d) : (0 : ℝ) ≤ secondSteepScale n d)
    nlinarith
  have hSecondFour : 4 * secondSteepScale n d ≤ n := by exact_mod_cast hSecondFourR
  have hDensity := secondSteepScale_density_lower hd hDimension.2.2
  have hScaled := mul_le_mul_of_nonneg_left hDenUpper
    (by positivity : (0 : ℝ) ≤ 2 * secondSteepScale n d)
  have hDensityR : (n : ℝ) ≤ 2 * d * secondSteepScale n d := by nlinarith
  have hDensityN : n ≤ 2 * d * secondSteepScale n d := by exact_mod_cast hDensityR
  have hBound : 2 * d * firstSteepScale n d ≤ 2 * d * secondSteepScale n d := by nlinarith
  have hRanks : firstSteepScale n d ≤ secondSteepScale n d := by
    by_contra hBad
    have hScaled := Nat.mul_le_mul_left (2 * d) (by omega : secondSteepScale n d + 1 ≤ firstSteepScale n d)
    nlinarith
  exact ⟨hRanks, by omega, hSecondFour⟩

theorem source_second_third_rank_fit {n d : ℕ} {a₃ : ℝ}
    (h : SourceKernelConditions n d) (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2)
    (hSize : 2 ≤ a₃ * (n : ℝ)) (hDegree : 2 / a₃ ≤ Real.rpow (d : ℝ) (2 / 3)) :
    secondSteepScale n d ≤ thirdSteepScale n a₃ ∧
      thirdSteepScale n a₃ + secondSteepScale n d ≤ n := by
  have hd : 0 < d := (source_kernel_dimension_twice_degree h).2.1
  have hDen : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hScaled := (div_le_iff₀ ha).mp hDegree
  have hCoefficient : 1 / Real.rpow (d : ℝ) (2 / 3) ≤ a₃ / 2 := by
    apply (div_le_iff₀ hDen).mpr
    nlinarith
  have hRatio : (n : ℝ) / Real.rpow (d : ℝ) (2 / 3) ≤ a₃ * n / 2 := by
    have h := mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    convert h using 1 <;> ring
  have hRanksR := (secondSteepScale_upper n d).trans (hRatio.trans (thirdSteepScale_bounds ha hSize).2.1)
  have hRanks : secondSteepScale n d ≤ thirdSteepScale n a₃ := by exact_mod_cast hRanksR
  have hHalf := thirdSteepScale_half (n := n) ha.le haHalf
  have hQuarter := (source_first_second_rank_fit h).2.2
  exact ⟨hRanks, by omega⟩

theorem source_first_net_radius {n d : ℕ} {cw Z₀ : ℝ}
    (hd : 0 < d) (hcw : 0 < cw) (hZ : 0 ≤ Z₀)
    (hDegree : (2 * (1 + Z₀)) ^ 2 ≤ equalBlockNormConstant cw ^ 2 * Real.sqrt d) :
    2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
      equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * firstSteepScale n d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  apply (sq_le_sq₀ (by positivity)
    (mul_nonneg (equalBlockNormConstant_pos hcw).le (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / d)]
  conv_rhs => rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) * firstSteepScale n d)]
  calc
    _ ≤ (equalBlockNormConstant cw ^ 2 * Real.sqrt d) * ((n : ℝ) / d) :=
      mul_le_mul_of_nonneg_right hDegree (by positivity)
    _ = equalBlockNormConstant cw ^ 2 * ((n : ℝ) / Real.sqrt d) := by
      field_simp [hdR.ne', hRoot.ne']
      rw [Real.sq_sqrt hdR.le]
      ring
    _ ≤ equalBlockNormConstant cw ^ 2 * ((d : ℝ) * firstSteepScale n d) :=
      mul_le_mul_of_nonneg_left (firstSteepScale_density_lower hd) (sq_nonneg _)
    _ = _ := by ring

theorem source_second_net_radius {n d : ℕ} {cw Z₀ : ℝ}
    (hd : 0 < d) (hn : 400 * d ≤ n) (hcw : 0 < cw) (hZ : 0 ≤ Z₀)
    (hDegree : 400 * (2 * (1 + Z₀)) ^ 2 ≤ equalBlockNormConstant cw ^ 2 * d) :
    2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
      equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hCoefficient : (2 * (1 + Z₀)) ^ 2 / d ≤ equalBlockNormConstant cw ^ 2 / 400 := by
    apply (div_le_iff₀ hdR).mpr
    nlinarith
  apply (sq_le_sq₀ (by positivity)
    (mul_nonneg (equalBlockNormConstant_pos hcw).le (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / d)]
  conv_rhs => rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) * equalBlockScale n d)]
  calc
    _ = ((2 * (1 + Z₀)) ^ 2 / d) * n := by ring
    _ ≤ (equalBlockNormConstant cw ^ 2 / 400) * n :=
      mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg n)
    _ = equalBlockNormConstant cw ^ 2 * ((n : ℝ) / 400) := by ring
    _ ≤ equalBlockNormConstant cw ^ 2 * ((d : ℝ) * equalBlockScale n d) :=
      mul_le_mul_of_nonneg_left (equalBlockScale_density_lower hd hn) (sq_nonneg _)
    _ = _ := by ring

theorem source_second_net_large_blocks {n d : ℕ} {cw : ℝ}
    (hd : 0 < d) (hDimension : 2 * d ≤ n)
    (hDegree : equalBlockLargeConstant cw ≤ 100 * Real.rpow (d : ℝ) (1 / 3)) :
    equalBlockLargeConstant cw * equalBlockScale n d ≤ (secondSteepScale n d : ℝ) := by
  have hDen : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  apply (mul_le_mul_iff_left₀ hDen).mp
  calc
    _ ≤ (100 * Real.rpow (d : ℝ) (1 / 3) * equalBlockScale n d) * Real.rpow (d : ℝ) (2 / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDegree (Nat.cast_nonneg _)) hDen.le
    _ = 100 * (Real.rpow (d : ℝ) (1 / 3) * Real.rpow (d : ℝ) (2 / 3)) * equalBlockScale n d := by ring
    _ = 100 * (d : ℝ) * equalBlockScale n d := by
      rw [positive_degree_power_mul hd, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num]
      simp only [Real.rpow_eq_pow, Real.rpow_one]
    _ ≤ (n : ℝ) / 2 := by linarith [equalBlockScale_density_upper (n := n) (d := d)]
    _ ≤ (secondSteepScale n d : ℝ) * Real.rpow (d : ℝ) (2 / 3) := by
      linarith [secondSteepScale_density_lower hd hDimension]

structure SourceSteepNetFit (n d : ℕ) (a₃ cw Z₀ : ℝ) : Prop where
  dimension : 400 * d ≤ n
  third_size : 2 ≤ a₃ * (n : ℝ)
  first_ranks : firstSteepScale n d ≤ secondSteepScale n d
  first_fit : secondSteepScale n d + firstSteepScale n d ≤ n
  first_radius : 2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
    equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * firstSteepScale n d)
  second_ranks : secondSteepScale n d ≤ thirdSteepScale n a₃
  second_fit : thirdSteepScale n a₃ + secondSteepScale n d ≤ n
  large_blocks : equalBlockLargeConstant cw * equalBlockScale n d ≤ (secondSteepScale n d : ℝ)
  second_radius : 2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ≤
    equalBlockNormConstant cw * Real.sqrt ((d : ℝ) * equalBlockScale n d)

theorem eventually_source_steep_net_fit_uniform {a₃ cw C Z₀ : ℝ}
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcw : 0 < cw) (hC : 0 < C)
    (hZ : 0 ≤ Z₀) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d → SourceSteepNetFit n d a₃ cw Z₀ := by
  have hq : 0 < equalBlockNormConstant cw ^ 2 := sq_pos_of_pos (equalBlockNormConstant_pos hcw)
  have hDegree : ∀ᶠ d : ℕ in atTop,
      (2 * (1 + Z₀)) ^ 2 / equalBlockNormConstant cw ^ 2 ≤ Real.rpow (d : ℝ) (1 / 2) ∧
      400 * (2 * (1 + Z₀)) ^ 2 / equalBlockNormConstant cw ^ 2 ≤ (d : ℝ) ∧
      2 / a₃ ≤ Real.rpow (d : ℝ) (2 / 3) ∧
      equalBlockLargeConstant cw / 100 ≤ Real.rpow (d : ℝ) (1 / 3) := by
    filter_upwards [eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 2) _,
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop _,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 2 / 3) _,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 3) _]
      with d hFirst hSecond hRanks hLarge
    exact ⟨hFirst, hSecond, hRanks, hLarge⟩
  have hSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC hDegree, hSize] with n hConditions hDegree hSize
  intro d hBand
  have h := hConditions d hBand.1 hBand.2
  have hD := hDegree d hBand.1
  have hDimension := source_kernel_dimension_twice_degree h
  have hd := hDimension.2.1
  have hN := (source_kernel_dimension_four_hundred h).1
  have hThird : 2 ≤ a₃ * (n : ℝ) := by
    have h := (div_le_iff₀ ha).mp hSize
    nlinarith
  have hFirst := source_first_second_rank_fit h
  have hSecond := source_second_third_rank_fit h ha haHalf hThird hD.2.2.1
  refine ⟨hN, hThird, hFirst.1, hFirst.2.1, ?_, hSecond.1, hSecond.2, ?_, ?_⟩
  · apply source_first_net_radius hd hcw hZ
    have h := (div_le_iff₀ hq).mp hD.1
    simpa only [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, mul_comm] using h
  · apply source_second_net_large_blocks hd hDimension.2.2
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 100)).mp hD.2.2.2
    nlinarith
  · apply source_second_net_radius hd hN hcw hZ
    have h := (div_le_iff₀ hq).mp hD.2.1
    nlinarith

end CircularLaw
