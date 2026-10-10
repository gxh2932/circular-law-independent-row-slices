import CircularLaw.NonnegativeEmpiricalMeasure
import Mathlib.Data.EReal.Basic

/-!
# Extended logarithmic values and exact finite-limit events

The signed empirical log is minus infinity when any value is zero.
The bottom negative-log sum is plus infinity exactly when a selected
value is zero. Their finite-neighborhood events agree with the events
used by the probability-limit proofs.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CircularLaw

def empiricalExtendedLogIntegral {n : ℕ} (s : Fin n → ℝ≥0) : EReal :=
  if empiricalHasZero s then ⊥ else (empiricalNonnegativeMean s (fun t => Real.log (t : ℝ)) : EReal)

theorem empiricalExtendedLogIntegral_outside_interval {n : ℕ}
    (s : Fin n → ℝ≥0) (a ε : ℝ) :
    ¬((a - ε : ℝ) ≤ empiricalExtendedLogIntegral s ∧ empiricalExtendedLogIntegral s ≤ (a + ε : ℝ)) ↔
      empiricalHasZero s ∨ ε < |empiricalNonnegativeMean s (fun t => Real.log (t : ℝ)) - a| := by
  unfold empiricalExtendedLogIntegral
  by_cases hZero : empiricalHasZero s
  · rw [if_pos hZero]
    constructor
    · intro _
      exact Or.inl hZero
    · intro _ h
      exact (not_le.mpr (EReal.bot_lt_coe (a - ε))) h.1
  · simp only [hZero, if_false, false_or, EReal.coe_le_coe_iff]
    rw [← not_le]
    apply not_congr
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

def empiricalExtendedBottomNegativeLog {n : ℕ} (s : Fin n → ℝ≥0) (r : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹ * ∑ j ∈ bottomLogIndices n r, extendedNegativeLog (s j)

theorem empiricalExtendedBottomNegativeLog_eq {n : ℕ} (hn : 0 < n)
    (s : Fin n → ℝ≥0) (r : ℕ) :
    empiricalExtendedBottomNegativeLog s r =
      if empiricalBottomHasZero s r then ⊤ else ENNReal.ofReal (empiricalBottomNegativeLog s r) := by
  unfold empiricalExtendedBottomNegativeLog
  by_cases hZero : empiricalBottomHasZero s r
  · rw [if_pos hZero]
    obtain ⟨j, hj, hs⟩ := hZero
    have hSum : (∑ i ∈ bottomLogIndices n r, extendedNegativeLog (s i)) = ⊤ := by
      apply ENNReal.sum_eq_top.mpr
      exact ⟨j, hj, by simp [extendedNegativeLog, hs]⟩
    rw [hSum]
    simp
  · rw [if_neg hZero]
    have hSum : (∑ j ∈ bottomLogIndices n r, extendedNegativeLog (s j)) =
        ∑ j ∈ bottomLogIndices n r, ENNReal.ofReal (hermitizationNegativeLog (s j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact if_neg (fun hs => hZero ⟨j, hj, hs⟩)
    have hNonneg : ∀ j ∈ bottomLogIndices n r, 0 ≤ hermitizationNegativeLog (s j) :=
      fun _ _ => le_max_right _ _
    rw [hSum, ← ENNReal.ofReal_sum_of_nonneg hNonneg]
    rw [empiricalBottomNegativeLog, ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]
    exact mul_comm _ _

theorem empiricalExtendedBottomNegativeLog_event {n : ℕ} (hn : 0 < n)
    (s : Fin n → ℝ≥0) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ε < empiricalExtendedBottomNegativeLog s r ↔ EmpiricalBottomLogTailEvent s r ε := by
  rw [empiricalExtendedBottomNegativeLog_eq hn s r]
  by_cases hZero : empiricalBottomHasZero s r
  · simp [hZero, EmpiricalBottomLogTailEvent]
  · rw [if_neg hZero, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le]
    simp only [EmpiricalBottomLogTailEvent, hZero, false_or]

end CircularLaw
