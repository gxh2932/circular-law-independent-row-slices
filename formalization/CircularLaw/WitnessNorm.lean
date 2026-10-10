import CircularLaw.IndependentWitnessTail

/-!
# A small Euclidean norm forces many row small balls

If the squared norm is at most `r^2*N/8`, at least seven eighths of the
coordinates have modulus below `r`. The independent-event bound therefore
gives an exponential norm estimate from one-half row concentration.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem norm_sq_small_implies_many_small {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {r : ℝ} (hr : 0 < r)
    (hNorm : (∑ i, ‖z i‖ ^ 2) ≤ r ^ 2 * (Fintype.card ι : ℝ) / 8) :
    (7 / 8 : ℝ) * Fintype.card ι ≤
      coordinateEventCount (fun _ : ι => fun a : ℂ => ‖a‖ < r) z := by
  classical
  let E := fun _ : ι => fun a : ℂ => ‖a‖ < r
  have hBad : r ^ 2 * (coordinateEventCount (fun i a => ¬E i a) z : ℝ) ≤ ∑ i, ‖z i‖ ^ 2 := by
    rw [coordinateEventCount_cast, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ‖z i‖ < r
    · simp only [E, hi, not_true_eq_false, ↓reduceIte, mul_zero]
      exact sq_nonneg _
    · simp only [E, hi, not_false_eq_true, ↓reduceIte, mul_one]
      exact pow_le_pow_left₀ hr.le (le_of_not_gt hi) 2
  have hCount := coordinateEventCount_compl E z
  have hCountReal : (coordinateEventCount E z : ℝ) +
      coordinateEventCount (fun i a => ¬E i a) z = Fintype.card ι := by exact_mod_cast hCount
  have hBadCount : (coordinateEventCount (fun i a => ¬E i a) z : ℝ) ≤ (Fintype.card ι : ℝ) / 8 := by
    have hSquare : 0 < r ^ 2 := sq_pos_of_pos hr
    nlinarith [hBad.trans hNorm]
  change (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E z
  linarith

theorem independent_norm_small_ball_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (Y : ∀ i, α i → ℂ) {r : ℝ} (hr : 0 < r)
    (hHalf : ∀ i, uniformProbability (fun a : α i => ‖Y i a‖ < r) ≤ 1 / 2) :
    uniformProbability (fun x : ∀ i, α i =>
      (∑ i, ‖Y i (x i)‖ ^ 2) ≤ r ^ 2 * (Fintype.card ι : ℝ) / 8) ≤
        Real.exp (-witnessHalfRate * Fintype.card ι) := by
  apply (uniformProbability_mono ?_).trans
    (independent_many_events_half (fun i a => ‖Y i a‖ < r) hHalf)
  intro x hx
  exact norm_sq_small_implies_many_small (fun i => Y i (x i)) hr hx

end CircularLaw
