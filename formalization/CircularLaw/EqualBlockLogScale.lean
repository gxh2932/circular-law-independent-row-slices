import CircularLaw.EqualBlockScale

/-!
# Absolute large-block parameters

At a large enough ratio `x=d*m1/n`, the checked Esseen coefficient gives
a probability `p <= 1/2` and `log(1/p) >= log(x)/4`. The constants depend
only on the fixed positive witness constant.
-/

noncomputable section

namespace CircularLaw

def equalBlockEsseen : ℝ := 2 * (24 * Real.exp 1 / Real.pi)

def equalBlockCoefficient (cw : ℝ) : ℝ :=
  max 2 (equalBlockEsseen / Real.sqrt (cw / 8))

def equalBlockRatioThreshold (cw : ℝ) : ℝ :=
  max (8 / cw) (equalBlockCoefficient cw ^ 4)

def equalBlockLargeConstant (cw : ℝ) : ℝ := 400 * equalBlockRatioThreshold cw

theorem equalBlockCoefficient_ge_two (cw : ℝ) : 2 ≤ equalBlockCoefficient cw :=
  le_max_left _ _

theorem equalBlockLargeConstant_ge_one (cw : ℝ) : 1 ≤ equalBlockLargeConstant cw := by
  have hD := equalBlockCoefficient_ge_two cw
  have hPow : (2 : ℝ) ^ 4 ≤ equalBlockCoefficient cw ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hD 4
  have hR := le_max_right (8 / cw) (equalBlockCoefficient cw ^ 4)
  unfold equalBlockLargeConstant equalBlockRatioThreshold
  nlinarith

theorem equal_block_large_probability_parameters {cw x a : ℝ} (hcw : 0 < cw)
    (hx : equalBlockRatioThreshold cw ≤ x) (ha : cw / 8 * x ≤ a) :
    1 ≤ a ∧
      0 < equalBlockCoefficient cw / Real.sqrt x ∧
      equalBlockCoefficient cw / Real.sqrt x ≤ 1 / 2 ∧
      equalBlockEsseen / Real.sqrt a ≤ equalBlockCoefficient cw / Real.sqrt x ∧
      Real.log x / 4 ≤ Real.log (1 / (equalBlockCoefficient cw / Real.sqrt x)) := by
  let D := equalBlockCoefficient cw
  have hD : 2 ≤ D := equalBlockCoefficient_ge_two cw
  have hDPos : 0 < D := by linarith
  have hPower : D ^ 4 ≤ x := (le_max_right _ _).trans hx
  have hLarge : 8 / cw ≤ x := (le_max_left _ _).trans hx
  have hxPos : 0 < x := (pow_pos hDPos 4).trans_le hPower
  have hRoot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxPos
  have hcwRoot : 0 < Real.sqrt (cw / 8) := Real.sqrt_pos.mpr (by positivity)
  have hA : 1 ≤ a := by
    have h := (div_le_iff₀ hcw).mp hLarge
    nlinarith
  have hRootPower : D ^ 2 ≤ Real.sqrt x := by
    apply (sq_le_sq₀ (sq_nonneg D) (Real.sqrt_nonneg x)).mp
    rw [Real.sq_sqrt hxPos.le]
    nlinarith
  refine ⟨hA, div_pos hDPos hRoot, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hRoot).mpr
    nlinarith
  · have hDenominator : Real.sqrt (cw / 8) * Real.sqrt x ≤ Real.sqrt a := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt ha
    calc
      _ ≤ equalBlockEsseen / (Real.sqrt (cw / 8) * Real.sqrt x) :=
        div_le_div_of_nonneg_left (by unfold equalBlockEsseen; positivity)
          (mul_pos hcwRoot hRoot) hDenominator
      _ = (equalBlockEsseen / Real.sqrt (cw / 8)) / Real.sqrt x := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hRoot.le
  · have hLog : 4 * Real.log D ≤ Real.log x := by
      have h := Real.log_le_log (pow_pos hDPos 4) hPower
      rw [Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      exact h
    have hInverse : 1 / (D / Real.sqrt x) = Real.sqrt x / D := by field_simp
    rw [hInverse, Real.log_div hRoot.ne' hDPos.ne', Real.log_sqrt hxPos.le]
    linarith

end CircularLaw
