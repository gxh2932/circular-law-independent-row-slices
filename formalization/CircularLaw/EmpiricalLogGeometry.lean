import CircularLaw.FiniteMean
import CircularLaw.LogTruncationIntegrals

/-!
# Logarithmic truncation bounds for literal empirical means

The finite mean is exactly the `1/n` sum from the manuscript. Zero values
are recorded separately because their extended negative logarithm is infinite.
-/

noncomputable section
open Classical
open scoped NNReal BigOperators

namespace CircularLaw

def empiricalNonnegativeMean {n : ℕ} (s : Fin n → ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ :=
  finiteMean (fun j => f (s j))

def empiricalHasZero {n : ℕ} (s : Fin n → ℝ≥0) : Prop := ∃ j, s j = 0

def empiricalNegativeLogTail {n : ℕ} (s : Fin n → ℝ≥0) (T : ℝ) : ℝ :=
  empiricalNonnegativeMean s (fun t => if T < hermitizationNegativeLog t then hermitizationNegativeLog t else 0)

theorem empirical_log_decomposition {n : ℕ} (s : Fin n → ℝ≥0) :
    empiricalNonnegativeMean s (fun t => Real.log (t : ℝ)) =
      empiricalNonnegativeMean s hermitizationPositiveLog - empiricalNonnegativeMean s hermitizationNegativeLog := by
  simp only [empiricalNonnegativeMean, hermitization_log_decomposition, finiteMean_sub]

theorem empirical_positive_log_excess_bounds {n : ℕ} (s : Fin n → ℝ≥0) {T : ℝ} (hT : 0 < T) :
    0 ≤ empiricalNonnegativeMean s hermitizationPositiveLog - empiricalNonnegativeMean s (clippedPositiveLog T) ∧
    empiricalNonnegativeMean s hermitizationPositiveLog - empiricalNonnegativeMean s (clippedPositiveLog T) ≤
      (1 / T) * empiricalNonnegativeMean s (fun t => (t : ℝ) ^ 2) := by
  unfold empiricalNonnegativeMean
  rw [← finiteMean_sub]
  constructor
  · exact finiteMean_nonneg (fun j => sub_nonneg.mpr (min_le_left _ _))
  · rw [← finiteMean_const_mul]
    exact finiteMean_mono (fun j => hermitizationPositiveLog_excess_le_second_moment hT (s j))

theorem empirical_negative_log_tail_bound {n : ℕ} (s : Fin n → ℝ≥0)
    (hZero : ¬empiricalHasZero s) {T : ℝ} (hT : 0 ≤ T) :
    empiricalNegativeLogTail s (2 * T) ≤
      2 * (empiricalNonnegativeMean s hermitizationNegativeLog - empiricalNonnegativeMean s (clippedNegativeLog T)) := by
  unfold empiricalNegativeLogTail empiricalNonnegativeMean
  rw [← finiteMean_sub, ← finiteMean_const_mul]
  apply finiteMean_mono
  intro j
  have ht : 0 < s j := lt_of_le_of_ne (zero_le _) (fun h => hZero ⟨j, h.symm⟩)
  exact negativeLog_tail_le_twice_excess hT ht

theorem empirical_negative_log_tail_antitone {n : ℕ} (s : Fin n → ℝ≥0) :
    Antitone (empiricalNegativeLogTail s) := by
  intro T U hTU
  apply finiteMean_mono
  intro j
  dsimp only
  split_ifs with hU hT hT
  · exact le_refl _
  · exact False.elim (hT (hTU.trans_lt hU))
  · exact le_max_right _ _
  · exact le_refl _

end CircularLaw
