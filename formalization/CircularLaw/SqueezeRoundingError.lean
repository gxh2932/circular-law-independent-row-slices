import CircularLaw.BernoulliSqueezeRounding

/-!
# An explicit omitted-prefix error for the two manuscript floors

The omitted fraction is at most `5*epsilon/4 + 2/n`. Multiplying by a
logarithmic cutoff gives the exact deterministic error used in the slow
diagonal argument.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem bernoulli_squeeze_removed_fraction_upper {n : ℕ} (hn : 0 < n)
    {epsilon : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) :
    (n - bernoulliSqueezePrefixLength n epsilon : ℕ) / (n : ℝ) ≤
      5 * epsilon / 4 + 2 / n := by
  let m := bernoulliSqueezeMinorDimension n epsilon
  let ell := bernoulliSqueezePrefixLength n epsilon
  have hMinor : (m : ℝ) ≤ (1 - epsilon) * n :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hEpsilonOne) (Nat.cast_nonneg n))
  have hMinorLower : (1 - epsilon) * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hPrefixLower : (1 - epsilon / 4) * (m : ℝ) < (ell : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hFactor : 0 ≤ 1 - epsilon / 4 := by linarith
  have hFactorOne : 1 - epsilon / 4 ≤ 1 := by linarith
  have hRound : (1 - epsilon) * n - (m : ℝ) ≤ 1 := by linarith
  have hScaledRound : (1 - epsilon / 4) * ((1 - epsilon) * n - (m : ℝ)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hRound hFactor).trans (by simpa only [mul_one] using hFactorOne)
  have hSquare : (0 : ℝ) ≤ epsilon ^ 2 * n := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  have hCount : (n : ℝ) - ell ≤ (5 * epsilon / 4) * n + 2 := by
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_sub (bernoulli_squeeze_prefix_le hEpsilon)]
  apply (div_le_iff₀ hnR).mpr
  rw [add_mul, div_mul_cancel₀ _ hnR.ne']
  exact hCount

theorem bernoulli_squeeze_cutoff_error_upper {n : ℕ} (hn : 0 < n)
    {epsilon T : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) (hT : 0 ≤ T) :
    ((n - bernoulliSqueezePrefixLength n epsilon : ℕ) / (n : ℝ)) * T ≤
      (5 / 4 : ℝ) * (epsilon * T) + 2 * T / n := by
  have h := mul_le_mul_of_nonneg_right
    (bernoulli_squeeze_removed_fraction_upper hn hEpsilon hEpsilonOne) hT
  convert h using 1
  ring

end CircularLaw
