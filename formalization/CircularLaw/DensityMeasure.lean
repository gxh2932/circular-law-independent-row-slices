import CircularLaw.BoundedDensity
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Probability laws dominated by planar area

A probability law dominated by Lebesgue area has a unit-bounded density.
Convolution with another probability law preserves that domination.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution

namespace CircularLaw

theorem densityLaw_le_volume {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    densityLaw p ≤ volume := by
  have h : (fun x => ENNReal.ofReal (p x)) ≤ᵐ[volume] (fun _ => 1) := by
    filter_upwards [hp.le_one] with x hx
    exact (ENNReal.ofReal_le_ofReal hx).trans_eq ENNReal.ofReal_one
  simpa only [densityLaw, ← Pi.one_def, withDensity_one] using withDensity_mono h

theorem densityLaw_le_scaled_volume {p : ℂ → ℝ} {B : ℝ}
    (hB : ∀ᵐ x ∂volume, p x ≤ B) :
    densityLaw p ≤ ENNReal.ofReal B • volume := by
  have h : (fun x => ENNReal.ofReal (p x)) ≤ᵐ[volume] (fun _ => ENNReal.ofReal B) := by
    filter_upwards [hB] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  simpa only [densityLaw, withDensity_const] using withDensity_mono h

theorem densityLaw_closedBall_le {p : ℂ → ℝ} {B r : ℝ} (hB0 : 0 ≤ B) (hr : 0 ≤ r)
    (hB : ∀ᵐ x ∂volume, p x ≤ B) (z : ℂ) :
    densityLaw p (Metric.closedBall z r) ≤ ENNReal.ofReal (B * (r ^ 2 * Real.pi)) := by
  have h := densityLaw_le_scaled_volume hB (Metric.closedBall z r)
  rw [Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall] at h
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  convert h using 1
  rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul (sq_nonneg r),
    ENNReal.ofReal_pow hr, hpi]

def areaDensity (μ : Measure ℂ) (x : ℂ) : ℝ := (μ.rnDeriv volume x).toReal

theorem areaDensity_unit_bounded (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) : UnitBoundedDensity (areaDensity μ) := by
  constructor
  · exact Measure.integrable_toReal_rnDeriv
  · exact ae_of_all _ fun _ => ENNReal.toReal_nonneg
  · filter_upwards [Measure.rnDeriv_le_one_of_le hμ] with x hx
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hx
  · simpa only [areaDensity, measureReal_def, measure_univ, ENNReal.toReal_one] using
      Measure.integral_toReal_rnDeriv hμ.absolutelyContinuous

theorem densityLaw_areaDensity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) : densityLaw (areaDensity μ) = μ := by
  rw [densityLaw]
  calc
    _ = volume.withDensity (μ.rnDeriv volume) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_ne_top μ volume] with x hx
      exact ENNReal.ofReal_toReal hx
    _ = μ := Measure.withDensity_rnDeriv_eq μ volume hμ.absolutelyContinuous

theorem probability_conv_le_volume (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hν : ν ≤ volume) :
    μ ∗ ν ≤ volume := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [← lintegral_indicator_one hs, Measure.lintegral_conv (measurable_one.indicator hs)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) (x + y) ∂volume ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_mono' hν le_rfl
    _ = volume s := by
      simp only [lintegral_add_left_eq_self, ← Pi.one_def, lintegral_indicator_one hs,
        lintegral_const, measure_univ, mul_one]

end CircularLaw
