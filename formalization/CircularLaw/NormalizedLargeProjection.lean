import CircularLaw.SourceLargeProjection

/-!
# The normalized large-branch projection threshold

The factor sqrt(d) is retained in the actual projection event. When
the global remaining fraction is at most epsilon and its logarithm is
at least four, completing a square puts that threshold below the proved
large projection radius with kappa=epsilon. The probability is bounded
by an explicit constant times epsilon+3*d^(-1/4).
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem exp_neg_log_square_le_remaining_power {n g : ℝ}
    (hn : 0 < n) (hg : 0 < g) (hL : 4 ≤ Real.log (n / g)) :
    Real.exp (-Real.log (n / g) ^ 2) ≤ (g / n) / 27 * (g / n) ^ (3 / 2 : ℝ) := by
  have hRatio : 0 < g / n := div_pos hg hn
  have hLogInv : Real.log (g / n) = -Real.log (n / g) := by
    rw [Real.log_div hg.ne' hn.ne', Real.log_div hn.ne' hg.ne']
    ring
  have hLogThree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hLog27 : Real.log 27 ≤ 6 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  apply (Real.le_log_iff_exp_le (by positivity :
    0 < (g / n) / 27 * (g / n) ^ (3 / 2 : ℝ))).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div hRatio.ne' (by norm_num), Real.log_rpow hRatio, hLogInv]
  nlinarith [sq_nonneg (Real.log (n / g) - 4)]

theorem remaining_three_halves_le_local {n g h : ℝ}
    (hn : 0 < n) (hg : 0 < g) (hh : 0 < h) (hGap : g ≤ 9 * h) :
    (g / n) ^ (3 / 2 : ℝ) ≤ 27 * (h / n) ^ (3 / 2 : ℝ) := by
  have hRatio : g / n ≤ 9 * (h / n) := by
    have h := div_le_div_of_nonneg_right hGap hn.le
    simpa only [mul_div_assoc] using h
  have hPower := Real.rpow_le_rpow (div_pos hg hn).le hRatio (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (div_pos hh hn).le,
    projection_three_halves_eq (by norm_num : (0 : ℝ) < 9)] at hPower
  have hNine : (9 : ℝ) * Real.sqrt 9 = 27 := by norm_num
  rwa [hNine] at hPower

theorem normalized_large_threshold_radius {n d g h ε : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hg : 0 < g) (hh : 0 < h)
    (hGap : g ≤ 9 * h) (hL : 4 ≤ Real.log (n / g)) (hFraction : g / n ≤ ε) :
    Real.sqrt d * Real.exp (-Real.log (n / g) ^ 2) ≤
      ε * Real.sqrt d * h ^ (3 / 2 : ℝ) * n ^ (-3 / 2 : ℝ) := by
  have hPower := remaining_three_halves_le_local hn hg hh hGap
  have hFirst := (exp_neg_log_square_le_remaining_power hn hg hL).trans
    (mul_le_mul_of_nonneg_left hPower (by positivity : 0 ≤ (g / n) / 27))
  have hLocal : Real.exp (-Real.log (n / g) ^ 2) ≤ (g / n) * (h / n) ^ (3 / 2 : ℝ) := by
    convert hFirst using 1
    ring
  have hFractionPower := mul_le_mul_of_nonneg_right hFraction
    (Real.rpow_nonneg (div_pos hh hn).le (3 / 2))
  have hFinal := mul_le_mul_of_nonneg_left (hLocal.trans hFractionPower) (Real.sqrt_pos.mpr hd).le
  rw [Real.div_rpow hh.le hn.le (3 / 2 : ℝ)] at hFinal
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hn.le]
  convert hFinal using 1
  ring

set_option maxHeartbeats 1500000 in
theorem bernoulli_projection_of_normalized_source_large_threshold
    {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (hN : 0 < N) (hAmbient : Fintype.card ι ≤ N) (hd : 1 ≤ (N : ℝ) * p)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    {g ε : ℝ} (hg : 0 < g) (hGap : g ≤ 9 * (Module.finrank ℂ V : ℝ))
    (hRange : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ g)
    (hL : 4 ≤ Real.log ((N : ℝ) / g)) (hFraction : g / N ≤ ε)
    (w : EuclideanSpace ℂ ι) :
    (bernoulliCubeLaw ι p hp).real {x |
      ‖V.starProjection (bernoulliCubeVector x + w)‖ <
        Real.sqrt ((N : ℝ) * p) * Real.exp (-(N : ℝ) * sourceLargeLogIncrement N g)} ≤
      bernoulliLargeProjectionConstant * (ε + 3 * ((N : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hDim : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  have hdp : 0 < (N : ℝ) * p := by linarith
  have hε : 0 ≤ ε := (div_pos hg hn).le.trans hFraction
  have hRadius := normalized_large_threshold_radius hn hdp hg hDim hGap hL hFraction
  rw [← source_large_log_increment_threshold_eq hn,
    large_projection_source_radius_eq hN hDim] at hRadius
  have hContainment : {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ <
        Real.sqrt ((N : ℝ) * p) * Real.exp (-(N : ℝ) * sourceLargeLogIncrement N g)} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ <
        ε * Real.sqrt (p : ℝ) * (Module.finrank ℂ V : ℝ) *
          Real.sqrt (Module.finrank ℂ V : ℝ) / N} := fun _ hx => hx.trans_le hRadius
  have hProb := (measureReal_mono (h₂ := by finiteness) hContainment).trans
    (bernoulli_projection_radius_bound_of_ambient_le p hp hpPos hHalf V hV w hε hN hAmbient)
  have hInv := large_projection_nine_inverse_dimension p.coe_nonneg hd (hRange.trans hGap)
  have hBound := mul_le_mul_of_nonneg_left (add_le_add (le_rfl : ε ≤ ε) hInv)
    bernoulli_large_projection_constant_pos.le
  unfold bernoulliLargeProjectionConstant at *
  exact hProb.trans hBound

end CircularLaw
