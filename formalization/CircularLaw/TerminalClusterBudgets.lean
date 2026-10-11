import CircularLaw.TerminalClusterParameters

/-!
# Degree budgets for the terminal clustered branch

Fixed logarithmic and squared-logarithmic costs are absorbed into the
literal terminal exponent and the cluster-fraction times exponent.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_log_square_power_budget {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (B b : ℝ) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∀ᶠ d : ℕ in atTop,
      B * Real.log d + b * Real.log d ^ 2 ≤ r * Real.rpow (d : ℝ) κ := by
  have hRatio : Tendsto (fun d : ℕ => Real.log d ^ 2 / Real.rpow (d : ℝ) κ) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℕ) hκ).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  have hCoefficient : 0 < B + b + 1 := by linarith
  filter_upwards [eventually_ge_atTop 1, hLog,
    hRatio.eventually (gt_mem_nhds (div_pos hr hCoefficient))] with d hd hLogOne hSmall
  have hPower : 0 < Real.rpow (d : ℝ) κ := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hSmall' := (div_lt_iff₀ hPower).mp hSmall
  have hScaled := mul_lt_mul_of_pos_left hSmall' hCoefficient
  have hCancel : (B + b + 1) * (r / (B + b + 1) * Real.rpow (d : ℝ) κ) =
      r * Real.rpow (d : ℝ) κ := by field_simp
  rw [hCancel] at hScaled
  change 1 ≤ Real.log d at hLogOne
  have hLogSquare : Real.log d ≤ Real.log d ^ 2 := by nlinarith
  have hLinear := mul_le_mul_of_nonneg_left hLogSquare hB
  nlinarith only [hScaled, hLinear, sq_nonneg (Real.log d)]

theorem eventually_terminalCluster_degree_margin :
    ∀ᶠ d : ℕ in atTop, 20 * Real.log d ≤ Real.rpow (d : ℝ) (1 / 96) := by
  filter_upwards [eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 96)
    (by norm_num : (0 : ℝ) < 1) 0 20 (by norm_num)] with d hd
  simpa only [zero_add, one_mul] using hd

theorem eventually_terminalCluster_fraction_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, Real.rpow (d : ℝ) (-(1 / 192)) ≤ ε := by
  have hLimit : Tendsto (fun d : ℕ => Real.rpow (d : ℝ) (-(1 / 192))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 192)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  exact (hLimit.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)

theorem eventually_terminal_margin_log_cost (B b : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ d : ℕ in atTop,
      B + b * Real.log d ≤ s * (Real.rpow (d : ℝ) (1 / 96) / (2 * Real.log d)) := by
  have hB : 0 ≤ |B| := abs_nonneg B
  have hb : 0 ≤ |b| := abs_nonneg b
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [hLog, eventually_log_square_power_budget (by norm_num : (0 : ℝ) < 1 / 96)
    (by positivity : 0 < s / 2) |B| |b| hB hb] with d hLogOne hBudget
  change 1 ≤ Real.log d at hLogOne
  have hLogPos : 0 < Real.log d := by linarith
  have hUpper : B + b * Real.log d ≤ |B| + |b| * Real.log d :=
    add_le_add (le_abs_self B) (mul_le_mul_of_nonneg_right (le_abs_self b) hLogPos.le)
  apply hUpper.trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hLogPos)).mpr
  nlinarith only [hBudget]

theorem eventually_terminal_cluster_log_cost (B b : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ d : ℕ in atTop,
      B + b * Real.log d ≤ s * (Real.rpow (d : ℝ) (1 / 192) / (4 * Real.log d)) := by
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [hLog, eventually_log_square_power_budget (by norm_num : (0 : ℝ) < 1 / 192)
    (by positivity : 0 < s / 4) |B| |b| (abs_nonneg B) (abs_nonneg b)]
    with d hLogOne hBudget
  change 1 ≤ Real.log d at hLogOne
  have hLogPos : 0 < Real.log d := by linarith
  have hUpper : B + b * Real.log d ≤ |B| + |b| * Real.log d :=
    add_le_add (le_abs_self B) (mul_le_mul_of_nonneg_right (le_abs_self b) hLogPos.le)
  apply hUpper.trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hLogPos)).mpr
  nlinarith only [hBudget]

theorem eventually_structuralCluster_log_cost_uniform {C : ℝ} (hC : 0 < C)
    (σ B b : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      8 ≤ structuralTerminalExponent n d L ∧
      B + b * Real.log d ≤ s * structuralClusterFraction n L *
        ((structuralTerminalExponent n d L : ℝ) - 4) := by
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_terminalCluster_degree_margin,
    eventually_degree_property_uniform hC (eventually_terminal_cluster_log_cost B b hs)]
    with n hConditions hMargin hBudget
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega : 0 < d)
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  refine ⟨(structuralTerminalExponent_margin_lower hd hCubic hL (hMargin d hBand.1)).1, ?_⟩
  apply (hBudget d hBand.1).trans
  have h := mul_le_mul_of_nonneg_left
    (structuralCluster_terminal_margin_lower hd hCubic hL (hMargin d hBand.1)) hs.le
  simpa only [mul_assoc] using h

end CircularLaw
