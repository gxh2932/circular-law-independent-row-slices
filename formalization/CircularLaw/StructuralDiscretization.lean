import CircularLaw.StructuralParameters

/-!
# Terminal discretization fits the source net range

The lower band's upper exponent is at most two. Its terminal
discretization logarithm and the degree's normalization cost together
fit inside half the dimension logarithm, uniformly over all degrees.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_structural_discretization_budget {σ : ℝ} (hσ : σ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ Real.rpow (Real.log n) (1 + σ) →
      2 * Real.rpow (d : ℝ) (1 / 96) + (3 / 2) * Real.log d ≤
        (1 / 2) * Real.log n := by
  have hCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLogLimit := Real.tendsto_log_atTop.comp hCast
  have hPowerLimit : Tendsto (fun n : ℕ => Real.rpow (Real.log n) (-(47 / 48)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 47 / 48)).comp hLogLimit
  have hRatioLimit : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hLogLimit
  filter_upwards [hLogLimit.eventually_ge_atTop 1,
    hPowerLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hRatioLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))]
    with n hLogOne hPowerSmall hRatioSmall
  change 1 ≤ Real.log n at hLogOne
  have hLog : 0 < Real.log n := by linarith
  intro d hd hDegree
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTop : (d : ℝ) ≤ Real.rpow (Real.log n) 2 := hDegree.trans
    (Real.rpow_le_rpow_of_exponent_le hLogOne (by linarith))
  have hRoot : Real.rpow (d : ℝ) (1 / 96) ≤ Real.rpow (Real.log n) (1 / 48) := by
    apply (Real.rpow_le_rpow hdR.le hTop (by norm_num : (0 : ℝ) ≤ 1 / 96)).trans_eq
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hLog.le]
    norm_num
  change (Real.log n) ^ (-(47 / 48) : ℝ) < 1 / 8 at hPowerSmall
  rw [show -(47 / 48 : ℝ) = 1 / 48 - 1 by norm_num,
    Real.rpow_sub_one hLog.ne'] at hPowerSmall
  have hPowerBudget : Real.rpow (d : ℝ) (1 / 96) ≤ Real.log n / 8 := by
    have h := (div_lt_iff₀ hLog).mp hPowerSmall
    change (Real.log n) ^ (1 / 48 : ℝ) < _ at h
    simp only [Real.rpow_eq_pow] at hRoot ⊢
    nlinarith
  have hLogDegree := Real.log_le_log hdR hTop
  simp only [Real.rpow_eq_pow] at hLogDegree
  rw [Real.log_rpow hLog] at hLogDegree
  have hRatio := (div_lt_iff₀ hLog).mp hRatioSmall
  have hLogBudget : Real.log d ≤ Real.log n / 6 := by linarith
  linarith

theorem structural_discretization_range {n d L u : ℕ} (hn : 0 < n) (hd : 1 < d)
    (hCubic : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (hu : u ≤ structuralTerminalExponent n d L)
    (hBudget : 2 * Real.rpow (d : ℝ) (1 / 96) + (3 / 2) * Real.log d ≤
      (1 / 2) * Real.log n) :
    ((d ^ u : ℕ) : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hkR : (0 : ℝ) < (d ^ u : ℕ) := by exact_mod_cast pow_pos (by omega : 0 < d) u
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hPower : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos hdR _
  apply (Real.log_le_log_iff hkR (div_pos hRoot hPower)).mp
  rw [Real.log_div hRoot.ne' hPower.ne', Real.log_sqrt hnR.le]
  have hLogPower : Real.log (Real.rpow (d : ℝ) (3 / 2)) = (3 / 2) * Real.log d := by
    simpa only [Real.rpow_eq_pow] using Real.log_rpow hdR (3 / 2)
  rw [hLogPower]
  have h := structural_discretization_log_bound hd hCubic hL hu
  linarith

theorem eventually_structural_discretization_range_uniform {C σ : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ((d ^ u : ℕ) : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) := by
  filter_upwards [eventually_structural_discretization_budget hσ,
    eventually_source_kernel_conditions_uniform hC (1 + σ)] with n hBudget hConditions
  intro d hBand L hL u hu
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  exact structural_discretization_range hFinite.1 hd hCubic hL hu
    (hBudget d hFinite.2.1 hBand.2)

end CircularLaw
