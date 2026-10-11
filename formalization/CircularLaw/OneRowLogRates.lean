import CircularLaw.LogComparisonExpectation
import CircularLaw.DistanceLogDegreeMoment

/-!
# Explicit good-event and exceptional-event rates for one row

The lower mean bound `sqrt(Q)/8` converts distance concentration into
the manuscript's `sqrt(log(e*d)/Q)` and `exp(-c*Q)` scales.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem one_row_log_mean_rates {Q m L : ℝ} (hQ : 1 ≤ Q) (hL : 0 ≤ L)
    (hMean : Real.sqrt Q / 8 ≤ m) :
    0 < m ∧
      (2 / m) * (288 * Real.sqrt L + 288 * Real.sqrt L) ≤ 9216 * Real.sqrt (L / Q) ∧
      Real.exp (-(1 / 1024) * (m / 2) ^ 2) ≤ Real.exp (-(1 / 262144) * Q) := by
  have hQpos : 0 < Q := by linarith
  have hRoot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hm : 0 < m := (div_pos hRoot (by norm_num)).trans_le hMean
  refine ⟨hm, ?_, ?_⟩
  · have hCoef : 2 / m ≤ 16 / Real.sqrt Q := (div_le_div_iff₀ hm hRoot).mpr (by linarith)
    have hMul := mul_le_mul_of_nonneg_right hCoef
      (show 0 ≤ 288 * Real.sqrt L + 288 * Real.sqrt L from by positivity)
    rw [Real.sqrt_div hL]
    convert hMul using 1
    ring
  · apply Real.exp_le_exp.mpr
    nlinarith [Real.sq_sqrt hQpos.le]

theorem one_row_log_bound_of_centered_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {η U m Q : ℝ} (hη : 0 < η) (hηU : η ≤ U) {d : ℕ} (hd : 0 < d)
    (hQ : 1 ≤ Q) (hMean : Real.sqrt Q / 8 ≤ m)
    (hBounds : ∀ᵐ ω ∂μ, η ≤ f ω ∧ f ω ≤ U ∧ η ≤ g ω ∧ g ω ≤ U)
    (hfInt : Integrable (fun ω => |f ω - m|) μ)
    (hgInt : Integrable (fun ω => |g ω - m|) μ)
    (hfMoment : (∫ ω, |f ω - m| ∂μ) ≤ 288 * Real.sqrt (rowLogDegree d))
    (hgMoment : (∫ ω, |g ω - m| ∂μ) ≤ 288 * Real.sqrt (rowLogDegree d))
    (hfTail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ |f ω - m|} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2))
    (hgTail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ |g ω - m|} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2)) :
    (∫ ω, |Real.log (f ω) - Real.log (g ω)| ∂μ) ≤
      9216 * Real.sqrt (rowLogDegree d / Q) +
        (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) * Real.log (U / η) *
          Real.exp (-(1 / 262144) * Q) := by
  have hL : 0 ≤ rowLogDegree d := (by norm_num : (0 : ℝ) ≤ 1).trans (rowLogDegree_ge_one hd)
  obtain ⟨hm, hGoodRate, hBadRate⟩ := one_row_log_mean_rates hQ hL hMean
  have hMain := log_comparison_expectation_bound μ hf hg hη hηU hm hBounds hfInt hgInt
  have hGood : (2 / m) * ((∫ ω, |f ω - m| ∂μ) + (∫ ω, |g ω - m| ∂μ)) ≤
      9216 * Real.sqrt (rowLogDegree d / Q) :=
    (mul_le_mul_of_nonneg_left (add_le_add hfMoment hgMoment) (by positivity)).trans hGoodRate
  have hTailf := hfTail (m / 2) (by linarith)
  have hTailg := hgTail (m / 2) (by linarith)
  have hPref : 0 ≤ rowDistanceTailConstant * Real.sqrt (d : ℝ) := by
    dsimp [rowDistanceTailConstant]
    positivity
  have hWeighted := mul_le_mul_of_nonneg_left hBadRate hPref
  have hBad : μ.real {ω | m / 2 ≤ |f ω - m|} + μ.real {ω | m / 2 ≤ |g ω - m|} ≤
      (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) * Real.exp (-(1 / 262144) * Q) := by
    nlinarith
  have hδ : 0 ≤ Real.log (U / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa only [one_mul] using hηU))
  have hExceptional := mul_le_mul_of_nonneg_left hBad hδ
  nlinarith

end CircularLaw
