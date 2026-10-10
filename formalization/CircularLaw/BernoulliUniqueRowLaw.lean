import CircularLaw.BernoulliRowPatterns
import CircularLaw.BernoulliColumnSubsetCounts

/-!
# Actual Bernoulli probabilities in a unique neighbourhood

A diagonal row in the selected set contributes when all selected entries
are zero. An outside row contributes when exactly one selected entry is
one. Both probabilities and the row exponential moment are exact.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def BernoulliUniqueRowEvent {ι : Type*} (a : ι) (S : Finset ι) (row : ι → Bool) : Prop :=
  if a ∈ S then (∀ j ∈ S, row j = false) else (∃ j ∈ S, BernoulliRowSingle S j row)

def bernoulliUniqueRowProbability {ι : Type*} (p : ℝ≥0) (a : ι) (S : Finset ι) : ℝ :=
  if a ∈ S then (1 - (p : ℝ)) ^ S.card else
    (S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1)

def bernoulliUniqueRowIndicator {ι : Type*} (a : ι) (S : Finset ι) (row : ι → Bool) : ℝ :=
  if BernoulliUniqueRowEvent a S row then 1 else 0

theorem bernoulli_rectangular_entry_zero_iff {ρ ι : Type*}
    (x : ρ × ι → Bool) (i : ρ) (j : ι) :
    bernoulliRectangularMatrix x i j = 0 ↔ x (i, j) = false := by
  cases h : x (i, j) <;> simp [bernoulliRectangularMatrix, h]

theorem bernoulli_rectangular_entry_norm_ge_iff {ρ ι : Type*}
    (x : ρ × ι → Bool) (i : ρ) (j : ι) {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    β ≤ ‖bernoulliRectangularMatrix x i j‖ ↔ x (i, j) = true := by
  cases h : x (i, j) <;>
    simp [bernoulliRectangularMatrix, h, not_le_of_gt hβ, hβOne]

theorem bernoulli_unique_neighbourhood_row_event {ρ ι : Type*} [Fintype ρ]
    (x : ρ × ι → Bool) (e : ρ ↪ ι) (S : Finset ι) (i : ρ)
    {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    i ∈ matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S ↔
      BernoulliUniqueRowEvent (e i) S (fun j => x (i, j)) := by
  rw [matrix_unique_neighbourhood_mem]
  simp_rw [bernoulli_rectangular_entry_norm_ge_iff x _ _ hβ hβOne,
    bernoulli_rectangular_entry_zero_iff]
  by_cases hi : e i ∈ S <;> simp only [BernoulliUniqueRowEvent, BernoulliRowSingle, hi,
    if_true, if_false, not_true_eq_false, not_false_eq_true, false_and, true_and,
    false_or, or_false]

theorem bernoulli_unique_row_probability {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι) (S : Finset ι) :
    (bernoulliCubeLaw ι p hp).real {row | BernoulliUniqueRowEvent a S row} =
      bernoulliUniqueRowProbability p a S := by
  by_cases ha : a ∈ S
  · simpa only [BernoulliUniqueRowEvent, bernoulliUniqueRowProbability, if_pos ha] using
      bernoulli_row_zero_probability p hp S
  · simpa only [BernoulliUniqueRowEvent, bernoulliUniqueRowProbability, if_neg ha] using
      bernoulli_row_exactly_one_probability p hp S

theorem bernoulli_unique_row_probability_bounds {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι) (S : Finset ι) :
    0 ≤ bernoulliUniqueRowProbability p a S ∧ bernoulliUniqueRowProbability p a S ≤ 1 := by
  rw [← bernoulli_unique_row_probability p hp a S]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem bernoulli_unique_row_indicator_integral {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι) (S : Finset ι) :
    (∫ row, bernoulliUniqueRowIndicator a S row ∂bernoulliCubeLaw ι p hp) =
      bernoulliUniqueRowProbability p a S := by
  change (∫ row, ({row | BernoulliUniqueRowEvent a S row}.indicator (fun _ => (1 : ℝ))) row
    ∂bernoulliCubeLaw ι p hp) = _
  calc
    _ = (bernoulliCubeLaw ι p hp).real {row | BernoulliUniqueRowEvent a S row} := by
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const
        (μ := bernoulliCubeLaw ι p hp) (1 : ℝ)
        (Set.to_countable {row : ι → Bool | BernoulliUniqueRowEvent a S row}).measurableSet
    _ = _ := bernoulli_unique_row_probability p hp a S

theorem bernoulli_unique_row_exponential_integral {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι) (S : Finset ι) (t : ℝ) :
    (∫ row, Real.exp (-t * bernoulliUniqueRowIndicator a S row) ∂bernoulliCubeLaw ι p hp) =
      1 + (Real.exp (-t) - 1) * bernoulliUniqueRowProbability p a S := by
  have hPoint (row : ι → Bool) :
      Real.exp (-t * bernoulliUniqueRowIndicator a S row) =
        1 + (Real.exp (-t) - 1) * bernoulliUniqueRowIndicator a S row := by
    by_cases hx : BernoulliUniqueRowEvent a S row <;>
      simp [bernoulliUniqueRowIndicator, hx]
  simp_rw [hPoint]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const,
    integral_const_mul, probReal_univ, one_smul, bernoulli_unique_row_indicator_integral]

end CircularLaw
