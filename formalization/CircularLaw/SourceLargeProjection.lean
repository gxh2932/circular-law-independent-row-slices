import CircularLaw.BernoulliLargeExposure
import CircularLaw.SourceGraphProjectionThreshold

/-!
# The squared-log threshold for the large-dimension exposure branch

The exposure guard permits a factor nine between global remaining size
and local dimension. Completing a square controls the source threshold,
and the checked spread-basis projection bound permits that factor nine
without an assumed radius comparison.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceLargeLogIncrement (n g : ℝ) : ℝ := Real.log (n / g) ^ 2 / n

def sourceLargeExposureConstant : ℝ :=
  bernoulliLargeProjectionConstant * (27 * Real.exp 1 + 3)

theorem source_large_exposure_constant_pos : 0 < sourceLargeExposureConstant := by
  unfold sourceLargeExposureConstant
  exact mul_pos bernoulli_large_projection_constant_pos (by positivity)

theorem source_large_log_increment_threshold_eq {n g : ℝ} (hn : 0 < n) :
    Real.exp (-n * sourceLargeLogIncrement n g) = Real.exp (-Real.log (n / g) ^ 2) := by
  congr 1
  unfold sourceLargeLogIncrement
  field_simp

theorem exp_neg_log_square_le_three_halves {n g : ℝ} (hn : 0 < n) (hg : 0 < g) :
    Real.exp (-Real.log (n / g) ^ 2) ≤ Real.exp 1 * (g / n) ^ (3 / 2 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos hg hn), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hLog : Real.log (g / n) = -Real.log (n / g) := by
    rw [Real.log_div hg.ne' hn.ne', Real.log_div hn.ne' hg.ne']
    ring
  rw [hLog]
  nlinarith [sq_nonneg (Real.log (n / g) - 3 / 4)]

theorem source_large_threshold_radius {n d g h : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hg : 0 < g) (hh : 0 < h) (hGap : g ≤ 9 * h) :
    Real.exp (-Real.log (n / g) ^ 2) ≤
      (27 * Real.exp 1 / Real.sqrt d) * Real.sqrt d * h ^ (3 / 2 : ℝ) * n ^ (-3 / 2 : ℝ) := by
  have hRatio : g / n ≤ 9 * (h / n) := by
    have h := div_le_div_of_nonneg_right hGap hn.le
    simpa only [mul_div_assoc] using h
  have hPower := Real.rpow_le_rpow (div_pos hg hn).le hRatio (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (div_pos hh hn).le,
    projection_three_halves_eq (by norm_num : (0 : ℝ) < 9)] at hPower
  have hNine : (9 : ℝ) * Real.sqrt 9 = 27 := by norm_num
  rw [hNine, Real.div_rpow hh.le hn.le (3 / 2 : ℝ)] at hPower
  have hBound := (exp_neg_log_square_le_three_halves hn hg).trans
    (mul_le_mul_of_nonneg_left hPower (Real.exp_pos _).le)
  have hRoot : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hn.le]
  convert hBound using 1
  field_simp

theorem large_projection_nine_inverse_dimension {N : ℕ} {p h : ℝ}
    (hp : 0 ≤ p) (hd : 1 ≤ (N : ℝ) * p)
    (hLarge : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ 9 * h) :
    1 / Real.sqrt (h * p) ≤ 3 * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) := by
  have hBase := large_projection_inverse_dimension hp hd hLarge
  have hRoot : Real.sqrt ((9 * h) * p) = 3 * Real.sqrt (h * p) := by
    rw [show (9 * h) * p = 9 * (h * p) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
    norm_num
  rw [hRoot] at hBase
  have hThree := mul_le_mul_of_nonneg_left hBase (by norm_num : (0 : ℝ) ≤ 3)
  convert hThree using 1
  ring

theorem source_large_radius_coefficient_le {d : ℝ} (hd : 1 ≤ d) :
    27 * Real.exp 1 / Real.sqrt d ≤ 27 * Real.exp 1 * d ^ (-1 / 4 : ℝ) := by
  have hdp : 0 < d := by linarith
  have hPower := Real.rpow_le_rpow_of_exponent_le hd (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hdp.le,
    ← Real.sqrt_eq_rpow] at hPower
  have h := mul_le_mul_of_nonneg_left hPower (by positivity : 0 ≤ 27 * Real.exp 1)
  simpa only [div_eq_mul_inv] using h

set_option maxHeartbeats 1500000 in
theorem bernoulli_projection_of_source_large_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (hN : 0 < N) (hAmbient : Fintype.card ι ≤ N) (hd : 1 ≤ (N : ℝ) * p)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    {g : ℝ} (hg : 0 < g) (hGap : g ≤ 9 * (Module.finrank ℂ V : ℝ))
    (hRange : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ g)
    (w : EuclideanSpace ℂ ι) :
    (bernoulliCubeLaw ι p hp).real {x |
      ‖V.starProjection (bernoulliCubeVector x + w)‖ < Real.exp (-(N : ℝ) * sourceLargeLogIncrement N g)} ≤
      sourceLargeExposureConstant * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hDim : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  have hdp : 0 < (N : ℝ) * p := by linarith
  let κ := 27 * Real.exp 1 / Real.sqrt ((N : ℝ) * p)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hRadius := source_large_threshold_radius hn hdp hg hDim hGap
  rw [← source_large_log_increment_threshold_eq hn,
    large_projection_source_radius_eq hN hDim] at hRadius
  have hContainment : {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ <
        Real.exp (-(N : ℝ) * sourceLargeLogIncrement N g)} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ <
        κ * Real.sqrt (p : ℝ) * (Module.finrank ℂ V : ℝ) *
          Real.sqrt (Module.finrank ℂ V : ℝ) / N} := fun _ hx => hx.trans_le hRadius
  have hProb := (measureReal_mono (h₂ := by finiteness) hContainment).trans
    (bernoulli_projection_radius_bound_of_ambient_le p hp hpPos hHalf V hV w hκ hN hAmbient)
  have hInv := large_projection_nine_inverse_dimension p.coe_nonneg hd (hRange.trans hGap)
  have hCoeff := source_large_radius_coefficient_le hd
  have hSum : κ + 1 / Real.sqrt ((Module.finrank ℂ V : ℝ) * p) ≤
      (27 * Real.exp 1 + 3) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) := by
    dsimp [κ]
    nlinarith
  have hFinal := mul_le_mul_of_nonneg_left hSum bernoulli_large_projection_constant_pos.le
  unfold sourceLargeExposureConstant bernoulliLargeProjectionConstant at *
  exact hProb.trans (by nlinarith [hFinal])

end CircularLaw
