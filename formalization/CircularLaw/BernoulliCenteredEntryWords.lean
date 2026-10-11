import CircularLaw.BernoulliCubeLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual centered Bernoulli entry words at every order

Independence factors each word by its literal entry multiplicities.
Singleton entries force zero expectation. Every moment of order at
least two is bounded in absolute value by the variance, which is at
most p. These are the coefficient estimates needed in the sparse
trace-moment comparison; weak convergence is not assumed here.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliCenteredMoment (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) : ℝ :=
  ∫ b, bernoulliCenteredValue p b ^ k ∂bernoulliCoordinateLaw p hp

theorem bernoulli_centered_moment_formula (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    bernoulliCenteredMoment p hp k = (1 - (p : ℝ)) * (-(p : ℝ)) ^ k +
      (p : ℝ) * (1 - (p : ℝ)) ^ k := by
  rw [bernoulliCenteredMoment, bernoulliCoordinateLaw_integral]
  simp only [bernoulliCenteredValue, Bool.cond_false, Bool.cond_true, zero_sub]

theorem bernoulli_centered_moment_zero (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliCenteredMoment p hp 0 = 1 := by
  rw [bernoulli_centered_moment_formula]
  simp

theorem bernoulli_centered_moment_one (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliCenteredMoment p hp 1 = 0 := by
  simpa only [bernoulliCenteredMoment, pow_one] using bernoulliCenteredValue_mean p hp

theorem bernoulli_centered_moment_two (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliCenteredMoment p hp 2 = p * (1 - (p : ℝ)) :=
  bernoulliCenteredValue_second_moment p hp

theorem bernoulli_centered_value_abs_bound (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    |bernoulliCenteredValue p b| ≤ 1 := by
  have h0 := p.coe_nonneg
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  cases b <;> simp only [bernoulliCenteredValue, Bool.cond_false, Bool.cond_true]
  · simpa only [zero_sub, abs_neg, abs_of_nonneg h0] using h1
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem bernoulli_centered_power_abs_bound (p : ℝ≥0) (hp : p ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) (b : Bool) :
    |bernoulliCenteredValue p b ^ k| ≤ bernoulliCenteredValue p b ^ 2 := by
  rw [abs_pow, ← sq_abs]
  exact pow_le_pow_of_le_one (abs_nonneg _) (bernoulli_centered_value_abs_bound p hp b) hk

theorem bernoulli_centered_moment_abs_bound (p : ℝ≥0) (hp : p ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) : |bernoulliCenteredMoment p hp k| ≤ p * (1 - (p : ℝ)) := by
  calc
    _ ≤ ∫ b, |bernoulliCenteredValue p b ^ k| ∂bernoulliCoordinateLaw p hp :=
      abs_integral_le_integral_abs
    _ ≤ ∫ b, bernoulliCenteredValue p b ^ 2 ∂bernoulliCoordinateLaw p hp :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (bernoulli_centered_power_abs_bound p hp hk)
    _ = _ := bernoulliCenteredValue_second_moment p hp

theorem bernoulli_centered_moment_abs_le_parameter (p : ℝ≥0) (hp : p ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) : |bernoulliCenteredMoment p hp k| ≤ (p : ℝ) := by
  have h := bernoulli_centered_moment_abs_bound p hp hk
  nlinarith [sq_nonneg (p : ℝ)]

def bernoulliCenteredEntryWord {ι : Type*} (p : ℝ≥0) (w : List ι) (x : ι → Bool) : ℝ :=
  (w.map (fun i => bernoulliCenteredValue p (x i))).prod

theorem bernoulli_centered_entry_word_append {ι : Type*} (p : ℝ≥0) (u v : List ι)
    (x : ι → Bool) : bernoulliCenteredEntryWord p (u ++ v) x =
      bernoulliCenteredEntryWord p u x * bernoulliCenteredEntryWord p v x := by
  simp only [bernoulliCenteredEntryWord, List.map_append, List.prod_append]

theorem bernoulli_centered_entry_word_count_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (w : List ι) (x : ι → Bool) :
    bernoulliCenteredEntryWord p w x = ∏ i, bernoulliCenteredValue p (x i) ^ w.count i := by
  rw [bernoulliCenteredEntryWord, Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hi), pow_zero]

theorem bernoulli_centered_entry_word_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) :
    (∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp) =
      ∏ i, bernoulliCenteredMoment p hp (w.count i) := by
  simp only [bernoulli_centered_entry_word_count_product, bernoulliCubeLaw]
  exact integral_fintype_prod_eq_prod (fun i b => bernoulliCenteredValue p b ^ w.count i)

theorem bernoulli_centered_entry_word_singleton_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) (i : ι) (hi : w.count i = 1) :
    (∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp) = 0 := by
  rw [bernoulli_centered_entry_word_integral]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, bernoulli_centered_moment_one])

theorem bernoulli_centered_entry_word_integral_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) :
    (∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp) =
      ∏ i ∈ w.toFinset, bernoulliCenteredMoment p hp (w.count i) := by
  rw [bernoulli_centered_entry_word_integral]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hi),
    bernoulli_centered_moment_zero]

theorem bernoulli_centered_entry_word_integral_abs_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) (hNoSingleton : ∀ i, w.count i ≠ 1) :
    |∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp| ≤
      (p : ℝ) ^ w.toFinset.card := by
  rw [bernoulli_centered_entry_word_integral_support, Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ w.toFinset, (p : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i hi
      have hPos : 0 < w.count i := List.count_pos_iff.mpr (List.mem_toFinset.mp hi)
      exact bernoulli_centered_moment_abs_le_parameter p hp (by have h := hNoSingleton i; omega)
    _ = _ := by simp

theorem bernoulli_centered_entry_word_distinct_count_bound {ι : Type*} [DecidableEq ι]
    (w : List ι) (hNoSingleton : ∀ i, w.count i ≠ 1) :
    2 * w.toFinset.card ≤ w.length := by
  calc
    _ = ∑ _i ∈ w.toFinset, 2 := by simp [mul_comm]
    _ ≤ ∑ i ∈ w.toFinset, w.count i := by
      apply Finset.sum_le_sum
      intro i hi
      have hPos : 0 < w.count i := List.count_pos_iff.mpr (List.mem_toFinset.mp hi)
      have h := hNoSingleton i
      omega
    _ = _ := List.sum_toFinset_count_eq_length w

theorem bernoulli_centered_entry_word_integral_abs_bound_all {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) :
    |∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp| ≤
      if ∀ i, w.count i ≠ 1 then (p : ℝ) ^ w.toFinset.card else 0 := by
  split_ifs with h
  · exact bernoulli_centered_entry_word_integral_abs_bound p hp w h
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [bernoulli_centered_entry_word_singleton_zero p hp w i hi, abs_zero]

theorem bernoulli_centered_entry_paired_word_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) (hPaired : ∀ i ∈ w.toFinset, w.count i = 2) :
    (∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp) =
      ((p : ℝ) * (1 - (p : ℝ))) ^ w.toFinset.card := by
  rw [bernoulli_centered_entry_word_integral_support]
  calc
    _ = ∏ _i ∈ w.toFinset, (p : ℝ) * (1 - (p : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hPaired i hi, bernoulli_centered_moment_two]
    _ = _ := by simp

end CircularLaw
