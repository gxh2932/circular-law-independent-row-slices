import CircularLaw.TerminalClusterBudgets

/-!
# Discharging the clustered-Pv hypotheses at the terminal parameters

The source logarithmic separation expression is evaluated with the
literal cluster fraction and radius. All its hypotheses follow from
one uniform threshold in the standing degree band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def terminalPvSeparationConstant (a₃ : ℝ) : ℝ :=
  2 + (2 * Real.log 72 + 2 * Real.log 2 - Real.log ((1 / 65536) * a₃)) / Real.log 2

theorem terminalPv_separation_expression_bound {n d L : ℕ} {a₃ : ℝ}
    (hd : 0 < d) (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    2 * Real.logb 2 d + 2 * Real.logb 2 (72 * Real.sqrt d / structuralClusterFraction n L) +
      2 - Real.logb 2 ((1 / 65536) * a₃) ≤
        terminalPvSeparationConstant a₃ + (4 / Real.log 2) * Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hδ := structuralClusterFraction_pos hd hn hL
  have hLogδ := structuralClusterFraction_log_lower hd hn hL
  have hLogD : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  rw [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 72) hRoot).ne' hδ.ne',
    Real.log_mul (by norm_num : (72 : ℝ) ≠ 0) hRoot.ne', Real.log_sqrt hdR.le]
  calc
    _ = 2 + (2 * Real.log d + 2 * (Real.log 72 + Real.log d / 2 -
        Real.log (structuralClusterFraction n L)) - Real.log ((1 / 65536) * a₃)) / Real.log 2 := by ring
    _ ≤ 2 + (2 * Real.log 72 + 2 * Real.log 2 - Real.log ((1 / 65536) * a₃) +
        4 * Real.log d) / Real.log 2 := by
      apply add_le_add_right (div_le_div_of_nonneg_right ?_ hLog2.le) 2
      linarith
    _ = _ := by unfold terminalPvSeparationConstant; ring

theorem eventually_terminalPv_hypotheses_uniform {a₃ C : ℝ} (ha : 0 < a₃)
    (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      8 ≤ structuralTerminalExponent n d L ∧
      structuralRadius n L ≤ Real.rpow (d : ℝ) (-(structuralTerminalExponent n d L : ℝ)) ∧
      0 < structuralClusterFraction n L ∧
      structuralClusterFraction n L ≤ 36 * (1 / 65536) * a₃ ∧
      (1 / 65536) * a₃ * ((structuralTerminalExponent n d L : ℝ) - 4) ≥
        2 * Real.logb 2 d + 2 * Real.logb 2 (72 * Real.sqrt d / structuralClusterFraction n L) +
          2 - Real.logb 2 ((1 / 65536) * a₃) := by
  have hs : 0 < (1 / 65536 : ℝ) * a₃ := by positivity
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_terminalCluster_degree_margin,
    eventually_degree_property_uniform hC (eventually_terminalCluster_fraction_small
      (by positivity : 0 < 36 * (1 / 65536 : ℝ) * a₃)),
    eventually_degree_property_uniform hC (eventually_terminal_margin_log_cost
      (terminalPvSeparationConstant a₃) (4 / Real.log 2) hs)]
    with n hConditions hMargin hFraction hBudget
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega : 0 < d)
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hV := structuralTerminalExponent_margin_lower hd hCubic hL (hMargin d hBand.1)
  refine ⟨hV.1, structuralRadius_le_terminal_radius hd,
    structuralClusterFraction_pos (by omega) hCubic hL,
    ((structuralClusterFraction_degree_bounds (by omega) hCubic hL).2).trans
      (hFraction d hBand.1), ?_⟩
  apply (terminalPv_separation_expression_bound (by omega) hCubic hL).trans
  apply (hBudget d hBand.1).trans
  exact mul_le_mul_of_nonneg_left hV.2 hs.le

end CircularLaw
