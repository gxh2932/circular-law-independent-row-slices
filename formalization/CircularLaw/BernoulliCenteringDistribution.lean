import CircularLaw.BernoulliCenteringInterlacing

/-!
# The deterministic empirical distribution error from Bernoulli centering

One-index interlacing gives at most one entry of discrepancy below every
real threshold. With the actual dimension normalization, the empirical
distribution functions differ by at most 1/n, at every sample, degree
and shift. This supplies the centering step of the weak-law argument.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

def finiteBelowCount {n : ℕ} (s : Fin n → ℝ) (t : ℝ) : ℕ :=
  ∑ i, if s i < t then 1 else 0

theorem finite_below_count_le_of_one_shift {n : ℕ} (a b : Fin n → ℝ) (t : ℝ)
    (hShift : ∀ i j : Fin n, j.val = i.val + 1 → a j ≤ b i) :
    finiteBelowCount b t ≤ finiteBelowCount a t + 1 := by
  cases n with
  | zero => simp [finiteBelowCount]
  | succ n =>
    have hSum : (∑ i : Fin n, if b i.castSucc < t then (1 : ℕ) else 0) ≤
        ∑ i : Fin n, if a i.succ < t then (1 : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hb : b i.castSucc < t
      · rw [if_pos hb, if_pos ((hShift i.castSucc i.succ rfl).trans_lt hb)]
      · rw [if_neg hb]
        exact Nat.zero_le _
    have hB : finiteBelowCount b t =
        (∑ i : Fin n, if b i.castSucc < t then (1 : ℕ) else 0) +
          (if b (Fin.last n) < t then 1 else 0) := by
      rw [finiteBelowCount, Fin.sum_univ_castSucc]
    have hA : finiteBelowCount a t = (if a 0 < t then (1 : ℕ) else 0) +
        ∑ i : Fin n, if a i.succ < t then (1 : ℕ) else 0 := by
      rw [finiteBelowCount, Fin.sum_univ_succ]
    have hLast : (if b (Fin.last n) < t then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
    rw [hB, hA]
    omega

theorem finite_below_count_difference_bound {n : ℕ} (a b : Fin n → ℝ) (t : ℝ)
    (hAB : ∀ i j : Fin n, j.val = i.val + 1 → a j ≤ b i)
    (hBA : ∀ i j : Fin n, j.val = i.val + 1 → b j ≤ a i) :
    |(finiteBelowCount a t : ℝ) - (finiteBelowCount b t : ℝ)| ≤ 1 := by
  have h1 : (finiteBelowCount b t : ℝ) ≤ (finiteBelowCount a t : ℝ) + 1 := by
    exact_mod_cast finite_below_count_le_of_one_shift a b t hAB
  have h2 : (finiteBelowCount a t : ℝ) ≤ (finiteBelowCount b t : ℝ) + 1 := by
    exact_mod_cast finite_below_count_le_of_one_shift b a t hBA
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def squareSingularBelowFraction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : ℝ :=
  (finiteBelowCount (orderedSquareSingularValues A) t : ℝ) / n

theorem square_singular_measure_below_eq_fraction {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    (squareSingularMeasure A).real {s : ℝ≥0 | (s : ℝ) < t} =
      squareSingularBelowFraction A t := by
  have hMeas : MeasurableSet {s : ℝ≥0 | (s : ℝ) < t} :=
    measurableSet_lt NNReal.continuous_coe.measurable measurable_const
  rw [← integral_indicator_one hMeas, squareSingularMeasure,
    empiricalNonnegativeMeasure_integral]
  simp [empiricalNonnegativeMean, finiteMean, squareSingularValuesNNReal,
    squareSingularBelowFraction, finiteBelowCount, Set.indicator]

theorem constant_entry_perturbation_distribution_bound {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (t : ℝ) :
    |squareSingularBelowFraction (B + constantEntryMatrix n c) t -
      squareSingularBelowFraction B t| ≤ 1 / (n : ℝ) := by
  unfold squareSingularBelowFraction
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply finite_below_count_difference_bound
  · intro i j hIndex
    exact (constant_entry_perturbation_singular_values_interlace B c i j hIndex).1
  · intro i j hIndex
    exact (constant_entry_perturbation_singular_values_interlace B c i j hIndex).2

theorem bernoulli_centering_distribution_bound {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (t : ℝ) :
    |squareSingularBelowFraction (normalizedShiftedBernoulliMatrix d z x) t -
      squareSingularBelowFraction (normalizedCenteredBernoulliMatrix d x - z • 1) t| ≤
        1 / (n : ℝ) := by
  unfold squareSingularBelowFraction
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply finite_below_count_difference_bound
  · intro i j hIndex
    exact (bernoulli_centering_singular_values_interlace d z x i j hIndex).1
  · intro i j hIndex
    exact (bernoulli_centering_singular_values_interlace d z x i j hIndex).2

theorem constant_entry_perturbation_measure_below_bound {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (t : ℝ) :
    |(squareSingularMeasure (B + constantEntryMatrix n c)).real
        {s : ℝ≥0 | (s : ℝ) < t} -
      (squareSingularMeasure B).real {s : ℝ≥0 | (s : ℝ) < t}| ≤ 1 / (n : ℝ) := by
  simp only [square_singular_measure_below_eq_fraction]
  exact constant_entry_perturbation_distribution_bound B c t

theorem bernoulli_centering_measure_below_bound {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (t : ℝ) :
    |(squareSingularMeasure (normalizedShiftedBernoulliMatrix d z x)).real
        {s : ℝ≥0 | (s : ℝ) < t} -
      (squareSingularMeasure (normalizedCenteredBernoulliMatrix d x - z • 1)).real
        {s : ℝ≥0 | (s : ℝ) < t}| ≤ 1 / (n : ℝ) := by
  simp only [square_singular_measure_below_eq_fraction]
  exact bernoulli_centering_distribution_bound d z x t

end CircularLaw
