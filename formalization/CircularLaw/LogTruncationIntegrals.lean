import CircularLaw.LogTruncationGeometry
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Truncated logarithmic integrals at a finite logarithmic limit

A finite Lebesgue logarithmic integral includes no mass at zero and
integrability of the ordinary real logarithm off zero. Dominated
convergence then recovers both parts from their continuous truncations.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

def FiniteLogarithmicIntegral (ν : Measure ℝ≥0) : Prop :=
  ν {0} = 0 ∧ Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν

theorem hermitizationNegativeLog_measurable : Measurable hermitizationNegativeLog :=
  (Real.measurable_log.comp measurable_subtype_coe).neg.max measurable_const

theorem integrable_hermitizationPositiveLog {ν : Measure ℝ≥0}
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν) :
    Integrable hermitizationPositiveLog ν := by
  apply hLog.norm.mono' continuous_hermitizationPositiveLog.measurable.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hermitizationPositiveLog_nonneg t),
    hermitizationPositiveLog_eq_max, Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem integrable_hermitizationNegativeLog {ν : Measure ℝ≥0}
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν) :
    Integrable hermitizationNegativeLog ν := by
  apply hLog.norm.mono' hermitizationNegativeLog_measurable.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem finiteLogarithmicIntegral_ae_pos {ν : Measure ℝ≥0}
    (hν : FiniteLogarithmicIntegral ν) : ∀ᵐ t ∂ν, 0 < t := by
  rw [ae_iff]
  have hSet : {t : ℝ≥0 | ¬0 < t} = {0} := by ext t; simp [not_lt]
  rw [hSet]
  exact hν.1

theorem clippedPositiveLog_integral_tendsto {ν : Measure ℝ≥0}
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν) :
    Tendsto (fun T : ℕ => ∫ t, clippedPositiveLog T t ∂ν) atTop
      (𝓝 (∫ t, hermitizationPositiveLog t ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence hermitizationPositiveLog
    (fun T => (continuous_clippedPositiveLog T).measurable.aestronglyMeasurable)
    (integrable_hermitizationPositiveLog hLog)
  · intro T
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (clippedPositiveLog_bounds (Nat.cast_nonneg T) t).1]
    exact min_le_left _ _
  · apply ae_of_all
    intro t
    have hLarge : ∀ᶠ T : ℕ in atTop, hermitizationPositiveLog t ≤ (T : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop _)
    exact (tendsto_congr' (hLarge.mono (fun _ h => min_eq_left h))).mpr tendsto_const_nhds

theorem clippedNegativeLog_integral_tendsto {ν : Measure ℝ≥0}
    (hν : FiniteLogarithmicIntegral ν) :
    Tendsto (fun T : ℕ => ∫ t, clippedNegativeLog T t ∂ν) atTop
      (𝓝 (∫ t, hermitizationNegativeLog t ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence hermitizationNegativeLog
    (fun T => (continuous_clippedNegativeLog T).measurable.aestronglyMeasurable)
    (integrable_hermitizationNegativeLog hν.2)
  · intro T
    filter_upwards [finiteLogarithmicIntegral_ae_pos hν] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (clippedNegativeLog_bounds (Nat.cast_nonneg T) t).1,
      clippedNegativeLog_eq_min (Nat.cast_nonneg T) ht]
    exact min_le_left _ _
  · filter_upwards [finiteLogarithmicIntegral_ae_pos hν] with t ht
    have hLarge : ∀ᶠ T : ℕ in atTop, hermitizationNegativeLog t ≤ (T : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop _)
    have hEq : (fun T : ℕ => clippedNegativeLog T t) =ᶠ[atTop]
        (fun _ => hermitizationNegativeLog t) := hLarge.mono (fun T h => by
      change clippedNegativeLog (T : ℝ) t = hermitizationNegativeLog t
      rw [clippedNegativeLog_eq_min (Nat.cast_nonneg T) ht, min_eq_left h])
    exact (tendsto_congr' hEq).mpr tendsto_const_nhds

theorem hermitization_log_integral_decomposition {ν : Measure ℝ≥0}
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν) :
    (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) =
      (∫ t, hermitizationPositiveLog t ∂ν) - ∫ t, hermitizationNegativeLog t ∂ν := by
  simp_rw [hermitization_log_decomposition]
  exact integral_sub (integrable_hermitizationPositiveLog hLog) (integrable_hermitizationNegativeLog hLog)

end CircularLaw
