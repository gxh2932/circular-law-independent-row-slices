import CircularLaw.BernoulliAmbientSmallSetExpansion
import CircularLaw.SourceGraphGrowthRange

/-!
# Explicit scalar bounds in the larger source expansion range

For degree at least exp(1024), the source threshold is at most half
the lower bound on the unique-neighbourhood mean. The subset entropy
costs at most half the fixed-set exponential tail.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

theorem large_set_expansion_degree_range {d : ℝ} (hd : Real.exp 1024 ≤ d) :
    429981696 ≤ d ∧ 1024 ≤ Real.log d ∧ Real.exp (Real.exp 1) ≤ d := by
  have hBase : (257 : ℝ) ≤ Real.exp 256 := by linarith [Real.add_one_le_exp (256 : ℝ)]
  have hPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 257) hBase 4
  have hExpEq : Real.exp (1024 : ℝ) = Real.exp 256 ^ 4 := by
    rw [show (1024 : ℝ) = (4 : ℕ) * 256 by norm_num, Real.exp_nat_mul]
  rw [← hExpEq] at hPower
  have hLarge : 429981696 ≤ d := by norm_num at hPower; linarith
  have hLog : 1024 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos 1024) hd
    simpa only [Real.log_exp] using h
  exact ⟨hLarge, hLog, (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_three])).trans hd⟩

theorem large_set_loglog_to_log_bound {x : ℝ} (hx : 1024 ≤ x) :
    16 * Real.log x ≤ x := by
  have hLog := log_nat_power_le_sqrt (by linarith : 1 ≤ x) (by norm_num : (0 : ℕ) < 1)
  norm_num only [pow_one, Nat.cast_one, mul_one] at hLog
  have hRoot : 32 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h
    exact h
  have hSquare := Real.sq_sqrt (by linarith : 0 ≤ x)
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (by linarith : 0 ≤ Real.sqrt x - 32)]

theorem large_set_entropy_polynomial_bound {d : ℝ} (hd : Real.exp 1024 ≤ d) :
    96 * Real.log d ^ 2 * Real.log (Real.log d) ≤ d := by
  obtain ⟨hLarge, hLogD, _⟩ := large_set_expansion_degree_range hd
  have hLogLog : Real.log (Real.log d) ≤ Real.log d := Real.log_le_self (by linarith)
  have hCubic := log_nat_power_le_sqrt (by linarith : 1 ≤ d) (by norm_num : (0 : ℕ) < 3)
  norm_num only [Nat.cast_ofNat] at hCubic
  have hRoot : 20736 ≤ Real.sqrt d := by
    have h := Real.sqrt_le_sqrt hLarge
    norm_num at h
    exact h
  have hProduct := mul_le_mul_of_nonneg_left hLogLog (sq_nonneg (Real.log d))
  have hSquare := Real.sq_sqrt (by linarith : 0 ≤ d)
  nlinarith [mul_nonneg (Real.sqrt_nonneg d) (by linarith : 0 ≤ Real.sqrt d - 20736)]

theorem source_graph_large_set_log_ratio_lower {n d ell : ℝ}
    (hn : 0 < n) (he : 0 < ell) (hd : Real.exp (Real.exp 1) ≤ d)
    (hRange : ell ≤ sourceGraphTerminalScale n d) :
    Real.log d / 2 ≤ Real.log (n / ell) := by
  have hdp : 0 < d := (Real.exp_pos _).trans_le hd
  have hLogD : Real.exp 1 ≤ Real.log d := (Real.le_log_iff_exp_le hdp).mpr hd
  have hLogDp : 0 < Real.log d := (Real.exp_pos _).trans_le hLogD
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  have hLog := log_nat_power_le_sqrt (by linarith [Real.add_one_le_exp (Real.exp 1), Real.exp_pos 1] : 1 ≤ d)
    (by norm_num : (0 : ℕ) < 1)
  norm_num only [pow_one, Nat.cast_one, mul_one] at hLog
  have hLogLog : Real.log (Real.log d) ≤ 2 * Real.sqrt d := (Real.log_le_self hLogDp.le).trans hLog
  have hTerminal : sourceGraphTerminalScale n d ≤ n / Real.sqrt d := by
    calc
      _ ≤ n / (2 * d) * (2 * Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hLogLog (by positivity)
      _ = _ := by
        have hSquare := Real.sq_sqrt hdp.le
        field_simp
        nlinarith
  have hRatio : Real.sqrt d ≤ n / ell := by
    apply (le_div_iff₀ he).mpr
    have h := (le_div_iff₀ hRoot).mp (hRange.trans hTerminal)
    simpa only [mul_comm] using h
  have h := Real.log_le_log hRoot hRatio
  rwa [Real.log_sqrt hdp.le] at h

theorem source_graph_large_set_threshold_upper {n d ell : ℝ}
    (hn : 0 < n) (he : 0 < ell) (hd : Real.exp 1024 ≤ d)
    (hRange : ell ≤ sourceGraphTerminalScale n d) :
    sourceGraphExpansion n d ell ≤ n / (8 * Real.log d) := by
  obtain ⟨hLarge, hLogD, hSource⟩ := large_set_expansion_degree_range hd
  have hdp : 0 < d := by linarith
  have hLogDp : 0 < Real.log d := by linarith
  have hLogLog : 0 ≤ Real.log (Real.log d) := Real.log_nonneg (by linarith)
  have hRatio := source_graph_large_set_log_ratio_lower hn he hSource hRange
  have hRatioPos : 0 < Real.log (n / ell) := by linarith
  have hSize : d * ell ≤ n * Real.log (Real.log d) / 2 := by
    have h := mul_le_mul_of_nonneg_left hRange hdp.le
    dsimp only [sourceGraphTerminalScale] at h
    have hEq : d * (n / (2 * d) * Real.log (Real.log d)) = n * Real.log (Real.log d) / 2 := by field_simp
    rwa [hEq] at h
  have hSquare : Real.log d ^ 2 / 4 ≤ Real.log (n / ell) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log (n / ell) - Real.log d / 2)
      (by linarith : 0 ≤ Real.log (n / ell) + Real.log d / 2)]
  have hLogLogBound := large_set_loglog_to_log_bound hLogD
  have hFraction : 16 * Real.log (Real.log d) / Real.log d ≤ 1 := by
    apply (div_le_iff₀ hLogDp).mpr
    simpa only [one_mul] using hLogLogBound
  calc
    _ ≤ (n * Real.log (Real.log d) / 2) / Real.log (n / ell) ^ 2 :=
      div_le_div_of_nonneg_right hSize (sq_nonneg _)
    _ ≤ (n * Real.log (Real.log d) / 2) / (Real.log d ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hSquare
    _ = (n / (8 * Real.log d)) * (16 * Real.log (Real.log d) / Real.log d) := by field_simp; ring
    _ ≤ n / (8 * Real.log d) := by
      have h := mul_le_mul_of_nonneg_left hFraction (by positivity : 0 ≤ n / (8 * Real.log d))
      simpa only [mul_one] using h

theorem source_graph_large_set_entropy_upper {n d ell : ℝ}
    (hn : 0 < n) (he : 0 < ell) (hd : Real.exp 1024 ≤ d)
    (hLower : n / (2 * d) ≤ ell) (hRange : ell ≤ sourceGraphTerminalScale n d) :
    ell * (1 + Real.log (n / ell)) ≤ n / (64 * Real.log d) := by
  obtain ⟨hLarge, hLogD, _⟩ := large_set_expansion_degree_range hd
  have hdp : 0 < d := by linarith
  have hLogDp : 0 < Real.log d := by linarith
  have hRatio : n / ell ≤ 2 * d := by
    apply (div_le_iff₀ he).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 2 * d)).mp hLower
    nlinarith
  have hLogRatio : Real.log (n / ell) ≤ 2 * Real.log d := by
    have h := Real.log_le_log (div_pos hn he) hRatio
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdp.ne'] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hPolynomial := large_set_entropy_polynomial_bound hd
  have hFactor : 96 * Real.log d ^ 2 * Real.log (Real.log d) / d ≤ 1 := by
    apply (div_le_iff₀ hdp).mpr
    simpa only [one_mul] using hPolynomial
  calc
    _ ≤ ell * (3 * Real.log d) := mul_le_mul_of_nonneg_left (by linarith) he.le
    _ ≤ (n / (2 * d) * Real.log (Real.log d)) * (3 * Real.log d) :=
      mul_le_mul_of_nonneg_right hRange (by positivity)
    _ = (n / (64 * Real.log d)) *
        (96 * Real.log d ^ 2 * Real.log (Real.log d) / d) := by field_simp; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hFactor (by positivity : 0 ≤ n / (64 * Real.log d))
      simpa only [mul_one] using h

end CircularLaw
