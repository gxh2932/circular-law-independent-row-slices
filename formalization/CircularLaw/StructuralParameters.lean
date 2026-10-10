import CircularLaw.GradualNetEntropy

/-!
# The literal terminal parameters in the structural theorem

The growth, radius, cluster fraction and terminal exponent retain the
source codimension and floor. Bounds hold for both allowed codimensions.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def structuralGrowth (n L : ℕ) : ℝ := Real.rpow ((n : ℝ) / L) (1 / 288)

def structuralRadius (n L : ℕ) : ℝ := Real.exp (-structuralGrowth n L)

def structuralClusterFraction (n L : ℕ) : ℝ := Real.rpow ((L : ℝ) / n) (1 / 576)

def structuralTerminalExponent (n d L : ℕ) : ℕ :=
  ⌊structuralGrowth n L / Real.log d⌋₊

theorem kernelCodimension_inverse_ratio_bounds {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    (d : ℝ) ^ 3 ≤ (n : ℝ) / L ∧ (n : ℝ) / L ≤ 2 * (d : ℝ) ^ 3 := by
  have hBounds := kernelCodimension_bounds hd hn hL
  have hLPos : (0 : ℝ) < L := by
    exact_mod_cast (kernelCodimension_quotient_bounds hd hn hL).2.2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hLPos).mpr
    have h := (le_div_iff₀ (pow_pos hdR 3)).mp hBounds.2
    nlinarith
  · apply (div_le_iff₀ hLPos).mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 3)).mp hBounds.1
    nlinarith

theorem structuralGrowth_degree_bounds {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    Real.rpow (d : ℝ) (1 / 96) ≤ structuralGrowth n L ∧
      structuralGrowth n L ≤ 2 * Real.rpow (d : ℝ) (1 / 96) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hBounds := kernelCodimension_inverse_ratio_bounds hd hn hL
  have hCube : Real.rpow ((d : ℝ) ^ 3) (1 / 288) = Real.rpow (d : ℝ) (1 / 96) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (d : ℝ) 3, ← Real.rpow_mul hdR.le]
    norm_num
  have hTwo : Real.rpow (2 : ℝ) (1 / 288) ≤ 2 := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 288 : ℝ) ≤ 1)
  constructor
  · exact hCube ▸ Real.rpow_le_rpow (by positivity) hBounds.1 (by norm_num)
  · calc
      structuralGrowth n L ≤ Real.rpow (2 * (d : ℝ) ^ 3) (1 / 288) :=
        Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg L))
          hBounds.2 (by norm_num)
      _ = Real.rpow 2 (1 / 288) * Real.rpow (d : ℝ) (1 / 96) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        exact congrArg (fun t => (2 : ℝ) ^ (1 / 288 : ℝ) * t) hCube
      _ ≤ _ := mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hdR.le _)

theorem structuralTerminalExponent_log_bound {n d L : ℕ} (hd : 1 < d) :
    (structuralTerminalExponent n d L : ℝ) * Real.log d ≤ structuralGrowth n L := by
  have hLog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd)
  have hGrowth : 0 ≤ structuralGrowth n L := Real.rpow_nonneg (by positivity) _
  exact (le_div_iff₀ hLog).mp (Nat.floor_le (div_nonneg hGrowth hLog.le))

theorem structuralRadius_le_terminal_radius {n d L : ℕ} (hd : 1 < d) :
    structuralRadius n L ≤ Real.rpow (d : ℝ) (-(structuralTerminalExponent n d L : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h := structuralTerminalExponent_log_bound (n := n) (L := L) hd
  unfold structuralRadius
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hdR]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem structural_discretization_log_bound {n d L u : ℕ} (hd : 1 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (hu : u ≤ structuralTerminalExponent n d L) :
    Real.log (d ^ u : ℕ) ≤ 2 * Real.rpow (d : ℝ) (1 / 96) := by
  have hLog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  have hU : (u : ℝ) ≤ structuralTerminalExponent n d L := by exact_mod_cast hu
  rw [Nat.cast_pow, Real.log_pow]
  exact (mul_le_mul_of_nonneg_right hU hLog).trans
    ((structuralTerminalExponent_log_bound hd).trans
      (structuralGrowth_degree_bounds (by omega) hn hL).2)

theorem eventually_structuralGradualNet_count_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ, ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
      (canonicalApproxFamily (d ^ u) X).Finite ∧
      (Nat.card (canonicalApproxFamily (d ^ u) X) : ℝ) ≤
        Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_restrictedGradualApprox_family_exp_cube_root_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hCount hConditions
  intro d hBand L hL a₃ u hu X hX
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega : 0 < d)
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  exact hCount d hBand L hL a₃ (d ^ u) (pow_pos (by omega) u)
    (structural_discretization_log_bound hd hCubic hL hu) X hX

end CircularLaw
