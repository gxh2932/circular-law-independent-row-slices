import CircularLaw.WeightEntropy

/-!
# Cancellation of weight entropy by dispersion

This is the analytic step in equation `eq:entropy-dispersion-cancel`.
The counting/compression inequality is an explicit input; the bound on
entropy and the uniform exponential cancellation are proved here.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace CircularLaw

theorem integer_entropy_real_bound (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    (∑' j : ℤ, integerEntropyAtom p j) ≤
      weightEntropyConstant + Real.log (1 + (integerDispersion p).toReal) := by
  have hLog : 0 ≤ Real.log (1 + (integerDispersion p).toReal) :=
    Real.log_nonneg (by linarith [ENNReal.toReal_nonneg (a := integerDispersion p)])
  have hTotal : 0 ≤ weightEntropyConstant + Real.log (1 + (integerDispersion p).toReal) :=
    add_nonneg weightEntropyConstant_pos.le hLog
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (integer_entropy_dispersion_finite p hD)
  rwa [integerEntropy_eq_ofReal_tsum p hD,
    ENNReal.toReal_ofReal (tsum_nonneg (integerEntropyAtom_nonneg p)),
    ENNReal.toReal_ofReal hTotal] at h

def entropyPenaltyConstant (β : ℝ) : ℝ := weightEntropyConstant + β - 1 - Real.log β

theorem entropyPenaltyConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < entropyPenaltyConstant β := by
  have hLog := Real.log_le_sub_one_of_pos hβ
  have hC := weightEntropyConstant_pos
  dsimp [entropyPenaltyConstant]
  linarith

theorem log_one_add_linear_penalty {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    Real.log (1 + t) - β * t ≤ β - 1 - Real.log β := by
  have htPos : 0 < 1 + t := by linarith
  have h := Real.log_le_sub_one_of_pos (mul_pos hβ htPos)
  rw [Real.log_mul hβ.ne' htPos.ne'] at h
  nlinarith only [h]

theorem integer_entropy_linear_penalty {β : ℝ} (hβ : 0 < β) (p : PMF ℤ)
    (hD : integerDispersion p ≠ ∞) :
    (∑' j : ℤ, integerEntropyAtom p j) - β * (integerDispersion p).toReal ≤
      entropyPenaltyConstant β := by
  have hH := integer_entropy_real_bound p hD
  have hLog := log_one_add_linear_penalty hβ (ENNReal.toReal_nonneg (a := integerDispersion p))
  dsimp [entropyPenaltyConstant]
  linarith

theorem integer_entropy_retained_rows_penalty {c n K : ℝ} (hc : 0 < c) (hn : 0 ≤ n)
    (hK : n / 2 ≤ K) (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    n * (∑' j : ℤ, integerEntropyAtom p j) - c * K * (integerDispersion p).toReal ≤
      entropyPenaltyConstant (c / 2) * n := by
  have hHalf : 0 < c / 2 := by positivity
  have h := mul_le_mul_of_nonneg_left (integer_entropy_linear_penalty hHalf p hD) hn
  have hRetained := mul_le_mul_of_nonneg_right hK
    (mul_nonneg hc.le (ENNReal.toReal_nonneg (a := integerDispersion p)))
  nlinarith only [h, hRetained]

theorem integer_entropy_compression_cancel {c n K A M : ℝ} (hc : 0 < c) (hn : 0 ≤ n)
    (hK : n / 2 ≤ K) (p : PMF ℤ) (hD : integerDispersion p ≠ ∞)
    (hCompression : M ≤ Real.exp (A * n + n * ∑' j : ℤ, integerEntropyAtom p j)) :
    M * Real.exp (-c * K * (integerDispersion p).toReal) ≤
      Real.exp ((A + entropyPenaltyConstant (c / 2)) * n) := by
  calc
    M * Real.exp (-c * K * (integerDispersion p).toReal) ≤
        Real.exp (A * n + n * ∑' j : ℤ, integerEntropyAtom p j) *
          Real.exp (-c * K * (integerDispersion p).toReal) :=
      mul_le_mul_of_nonneg_right hCompression (Real.exp_nonneg _)
    _ = Real.exp (A * n + n * (∑' j : ℤ, integerEntropyAtom p j) -
        c * K * (integerDispersion p).toReal) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((A + entropyPenaltyConstant (c / 2)) * n) := by
      apply Real.exp_le_exp.mpr
      have h := integer_entropy_retained_rows_penalty hc hn hK p hD
      nlinarith only [h]

end CircularLaw
