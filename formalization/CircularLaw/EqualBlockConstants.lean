import CircularLaw.EqualBlockLogScale

/-!
# Common norm and exponential constants for both equal-block cases

The chosen norm coefficient is smaller than both checked witness radii.
The minimum rate is valid for the exponential and logarithmic estimates.
-/

noncomputable section

namespace CircularLaw

def equalBlockNormConstant (cw : ℝ) : ℝ := Real.sqrt cw / 100

def equalBlockRateConstant (cw : ℝ) : ℝ :=
  min (witnessHalfRate * cw) (3 * witnessLogRate * cw / 16)

theorem equalBlockNormConstant_pos {cw : ℝ} (hcw : 0 < cw) :
    0 < equalBlockNormConstant cw := div_pos (Real.sqrt_pos.mpr hcw) (by norm_num)

theorem equalBlockRateConstant_pos {cw : ℝ} (hcw : 0 < cw) :
    0 < equalBlockRateConstant cw :=
  lt_min (mul_pos witnessHalfRate_pos hcw)
    (div_pos (mul_pos (mul_pos (by norm_num) witnessLogRate_pos) hcw) (by norm_num))

theorem equalBlockNormConstant_sq {cw : ℝ} (hcw : 0 ≤ cw) :
    equalBlockNormConstant cw ^ 2 = cw / 10000 := by
  rw [equalBlockNormConstant, div_pow, Real.sq_sqrt hcw]
  norm_num

theorem equal_block_small_radius {cw t : ℝ} (hcw : 0 < cw) (ht : 0 ≤ t) :
    equalBlockNormConstant cw * Real.sqrt t ≤ (1 / 3 : ℝ) * Real.sqrt (cw * t / 8) := by
  apply (sq_le_sq₀ (mul_nonneg (equalBlockNormConstant_pos hcw).le (Real.sqrt_nonneg t))
    (by positivity : 0 ≤ (1 / 3 : ℝ) * Real.sqrt (cw * t / 8))).mp
  rw [mul_pow, equalBlockNormConstant_sq hcw.le, Real.sq_sqrt ht,
    mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg hcw.le ht]

theorem equal_block_large_radius {cw t : ℝ} (hcw : 0 < cw) (ht : 0 ≤ t) :
    equalBlockNormConstant cw * Real.sqrt t ≤ (1 / 3 : ℝ) * Real.sqrt (3 * (cw * t) / 32) := by
  apply (sq_le_sq₀ (mul_nonneg (equalBlockNormConstant_pos hcw).le (Real.sqrt_nonneg t))
    (by positivity : 0 ≤ (1 / 3 : ℝ) * Real.sqrt (3 * (cw * t) / 32))).mp
  rw [mul_pow, equalBlockNormConstant_sq hcw.le, Real.sq_sqrt ht,
    mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg hcw.le ht]

end CircularLaw
