import CircularLaw.BottomLogConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Empirical means and the literal measure from the manuscript

The real integral is the actual normalized finite sum. For the extended
negative-log tail, any zero entry gives infinity; otherwise its Lebesgue
integral is exactly the nonnegative real tail mean.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CircularLaw

def empiricalNonnegativeMeasure {n : ℕ} (s : Fin n → ℝ≥0) : Measure ℝ≥0 :=
  (n : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (s j)

theorem empiricalNonnegativeMeasure_probability {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ≥0) :
    IsProbabilityMeasure (empiricalNonnegativeMeasure s) := by
  constructor
  have hMass : (∑ j, Measure.dirac (s j)) Set.univ = (n : ℝ≥0∞) := by
    simp
  rw [empiricalNonnegativeMeasure, Measure.smul_apply, smul_eq_mul, hMass]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)

theorem empiricalNonnegativeMeasure_integral {n : ℕ} (s : Fin n → ℝ≥0) (f : ℝ≥0 → ℝ) :
    (∫ t, f t ∂empiricalNonnegativeMeasure s) = empiricalNonnegativeMean s f := by
  rw [empiricalNonnegativeMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    empiricalNonnegativeMean, finiteMean, Fintype.card_fin]
  ring

theorem empiricalNonnegativeMeasure_lintegral {n : ℕ} (s : Fin n → ℝ≥0) (f : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ t, f t ∂empiricalNonnegativeMeasure s) = (n : ℝ≥0∞)⁻¹ * ∑ j, f (s j) := by
  rw [empiricalNonnegativeMeasure, lintegral_smul_measure, lintegral_finset_sum_measure]
  simp only [lintegral_dirac, smul_eq_mul]

def extendedNegativeLogTail (T : ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  if ENNReal.ofReal T < extendedNegativeLog t then extendedNegativeLog t else 0

theorem extendedNegativeLogTail_of_pos {T : ℝ} (hT : 0 ≤ T) {t : ℝ≥0} (ht : 0 < t) :
    extendedNegativeLogTail T t = ENNReal.ofReal
      (if T < hermitizationNegativeLog t then hermitizationNegativeLog t else 0) := by
  unfold extendedNegativeLogTail extendedNegativeLog
  rw [if_neg ht.ne']
  simp only [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT]
  split_ifs <;> simp

theorem extendedNegativeLogTail_zero (T : ℝ) : extendedNegativeLogTail T 0 = ⊤ := by
  simp [extendedNegativeLogTail, extendedNegativeLog]

theorem empiricalNegativeLogTail_lintegral {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure s) =
      if empiricalHasZero s then ⊤ else ENNReal.ofReal (empiricalNegativeLogTail s T) := by
  rw [empiricalNonnegativeMeasure_lintegral]
  by_cases hZero : empiricalHasZero s
  · rw [if_pos hZero]
    obtain ⟨j, hj⟩ := hZero
    have hSum : (∑ i, extendedNegativeLogTail T (s i)) = ⊤ := by
      apply ENNReal.sum_eq_top.mpr
      exact ⟨j, Finset.mem_univ _, by rw [hj, extendedNegativeLogTail_zero]⟩
    rw [hSum]
    simp
  · rw [if_neg hZero]
    have hPos (j : Fin n) : 0 < s j :=
      lt_of_le_of_ne (zero_le _) (fun h => hZero ⟨j, h.symm⟩)
    simp_rw [extendedNegativeLogTail_of_pos hT (hPos _)]
    have hNonneg (j : Fin n) : 0 ≤
        (if T < hermitizationNegativeLog (s j) then hermitizationNegativeLog (s j) else 0) := by
      split_ifs
      · exact le_max_right _ _
      · exact le_refl _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hNonneg j)]
    unfold empiricalNegativeLogTail empiricalNonnegativeMean finiteMean
    rw [Fintype.card_fin, ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]
    exact mul_comm _ _

theorem empiricalNegativeLogTail_lintegral_event {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ≥0)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ENNReal.ofReal ε < (∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure s) ↔
      EmpiricalNegativeLogTailEvent s T ε := by
  rw [empiricalNegativeLogTail_lintegral hn s hT]
  by_cases hZero : empiricalHasZero s
  · simp [hZero, EmpiricalNegativeLogTailEvent]
  · rw [if_neg hZero, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le]
    simp only [EmpiricalNegativeLogTailEvent, hZero, false_or]

end CircularLaw
