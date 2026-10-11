import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous truncations of the positive and negative logarithms

The real-valued negative part below is used only together with explicit
zero events in empirical tails. The extended negative logarithm assigns
infinite value to zero, as required by hermitization.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CircularLaw

def hermitizationPositiveLog (t : ℝ≥0) : ℝ := Real.log (max (t : ℝ) 1)

def hermitizationNegativeLog (t : ℝ≥0) : ℝ := max (-Real.log (t : ℝ)) 0

def extendedNegativeLog (t : ℝ≥0) : ℝ≥0∞ :=
  if t = 0 then ⊤ else ENNReal.ofReal (hermitizationNegativeLog t)

def clippedPositiveLog (T : ℝ) (t : ℝ≥0) : ℝ := min (hermitizationPositiveLog t) T

def clippedNegativeLog (T : ℝ) (t : ℝ≥0) : ℝ :=
  max (-Real.log (max (t : ℝ) (Real.exp (-T)))) 0

theorem hermitizationPositiveLog_nonneg (t : ℝ≥0) : 0 ≤ hermitizationPositiveLog t :=
  Real.log_nonneg (le_max_right _ _)

theorem hermitizationPositiveLog_eq_max (t : ℝ≥0) :
    hermitizationPositiveLog t = max (Real.log (t : ℝ)) 0 := by
  by_cases ht : 1 ≤ (t : ℝ)
  · simp only [hermitizationPositiveLog, max_eq_left ht,
      max_eq_left (Real.log_nonneg ht)]
  · have hLog : Real.log (t : ℝ) ≤ 0 := Real.log_nonpos t.coe_nonneg (le_of_not_ge ht)
    simp only [hermitizationPositiveLog, max_eq_right (le_of_not_ge ht), Real.log_one,
      max_eq_right hLog]

theorem hermitization_log_decomposition (t : ℝ≥0) :
    Real.log (t : ℝ) = hermitizationPositiveLog t - hermitizationNegativeLog t := by
  rw [hermitizationPositiveLog_eq_max]
  unfold hermitizationNegativeLog
  by_cases h : 0 ≤ Real.log (t : ℝ)
  · rw [max_eq_left h, max_eq_right (by linarith)]
    simp
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem continuous_hermitizationPositiveLog : Continuous hermitizationPositiveLog := by
  exact (continuous_subtype_val.max continuous_const).log (fun t => by positivity)

theorem continuous_clippedPositiveLog (T : ℝ) : Continuous (clippedPositiveLog T) :=
  continuous_hermitizationPositiveLog.min continuous_const

theorem continuous_clippedNegativeLog (T : ℝ) : Continuous (clippedNegativeLog T) := by
  exact ((continuous_subtype_val.max continuous_const).log
    (fun t => ne_of_gt ((Real.exp_pos (-T)).trans_le (le_max_right _ _)))).neg.max continuous_const

theorem clippedPositiveLog_bounds {T : ℝ} (hT : 0 ≤ T) (t : ℝ≥0) :
    0 ≤ clippedPositiveLog T t ∧ clippedPositiveLog T t ≤ T :=
  ⟨le_min (hermitizationPositiveLog_nonneg t) hT, min_le_right _ _⟩

theorem clippedNegativeLog_bounds {T : ℝ} (hT : 0 ≤ T) (t : ℝ≥0) :
    0 ≤ clippedNegativeLog T t ∧ clippedNegativeLog T t ≤ T := by
  have hLog : -T ≤ Real.log (max (t : ℝ) (Real.exp (-T))) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (-T)) (le_max_right (t : ℝ) (Real.exp (-T)))
  exact ⟨le_max_right _ _, max_le (by linarith) hT⟩

theorem clippedNegativeLog_zero {T : ℝ} (hT : 0 ≤ T) : clippedNegativeLog T 0 = T := by
  simp only [clippedNegativeLog, NNReal.coe_zero, max_eq_right (Real.exp_pos (-T)).le,
    Real.log_exp, neg_neg, max_eq_left hT]

theorem clippedNegativeLog_eq_min {T : ℝ} (hT : 0 ≤ T) {t : ℝ≥0} (ht : 0 < t) :
    clippedNegativeLog T t = min (hermitizationNegativeLog t) T := by
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  by_cases hFloor : Real.exp (-T) ≤ (t : ℝ)
  · have hLog : -Real.log (t : ℝ) ≤ T := by
      have h := Real.log_le_log (Real.exp_pos (-T)) hFloor
      rw [Real.log_exp] at h
      linarith
    simp only [clippedNegativeLog, max_eq_left hFloor, hermitizationNegativeLog,
      min_eq_left (max_le hLog hT)]
  · have hLog : T ≤ -Real.log (t : ℝ) := by
      have h := Real.log_le_log htReal (le_of_not_ge hFloor)
      rw [Real.log_exp] at h
      linarith
    simp only [clippedNegativeLog, max_eq_right (le_of_not_ge hFloor), Real.log_exp, neg_neg,
      max_eq_left hT, hermitizationNegativeLog, min_eq_right (hLog.trans (le_max_left _ _))]

theorem hermitizationPositiveLog_excess_le_second_moment {T : ℝ} (hT : 0 < T) (t : ℝ≥0) :
    hermitizationPositiveLog t - clippedPositiveLog T t ≤ (1 / T) * (t : ℝ) ^ 2 := by
  by_cases hSmall : hermitizationPositiveLog t ≤ T
  · rw [clippedPositiveLog, min_eq_left hSmall, sub_self]
    positivity
  · have hLarge : T < hermitizationPositiveLog t := lt_of_not_ge hSmall
    have ht : 1 < (t : ℝ) := by
      by_contra h
      have hz : hermitizationPositiveLog t = 0 := by
        simp only [hermitizationPositiveLog, max_eq_right (le_of_not_gt h), Real.log_one]
      rw [hz] at hLarge
      linarith
    have hPosEq : hermitizationPositiveLog t = Real.log (t : ℝ) := by
      simp only [hermitizationPositiveLog, max_eq_left ht.le]
    have hLog := Real.log_le_self t.coe_nonneg
    have hTL : T ≤ (t : ℝ) := by rw [hPosEq] at hLarge; linarith
    have hProd : (t : ℝ) * T ≤ (t : ℝ) ^ 2 := by nlinarith
    have hBound : (t : ℝ) ≤ (1 / T) * (t : ℝ) ^ 2 := by
      rw [one_div, ← div_eq_inv_mul]
      exact (le_div_iff₀ hT).mpr hProd
    rw [clippedPositiveLog, min_eq_right hLarge.le, hPosEq]
    linarith

theorem negativeLog_tail_le_twice_excess {T : ℝ} (hT : 0 ≤ T) {t : ℝ≥0} (ht : 0 < t) :
    (if 2 * T < hermitizationNegativeLog t then hermitizationNegativeLog t else 0) ≤
      2 * (hermitizationNegativeLog t - clippedNegativeLog T t) := by
  rw [clippedNegativeLog_eq_min hT ht]
  split_ifs with h
  · rw [min_eq_right (by linarith)]
    linarith
  · have hMin := min_le_left (hermitizationNegativeLog t) T
    linarith

end CircularLaw
