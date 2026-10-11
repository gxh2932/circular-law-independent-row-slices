import CircularLaw.BernoulliCenteredEntryWords
import CircularLaw.BernoulliSquareMatrixLaw
import CircularLaw.MatrixWordWalks
import CircularLaw.MatrixScalarShiftWords

/-!
# Exact actual centered Bernoulli matrix-word trace means

Every direct/adjoint factor retains its ordered entry index in a closed
walk. The integral is a finite sum of products of centered marginal
moments, with repeated-index multiplicities included. The same formula
holds for two traces by concatenating the two entry lists. Singleton
entries vanish and each remaining walk has at most half as many distinct
entries as factors. Asymptotic walk enumeration remains a later step.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

-- Match the multiplicity convention of the generic finite-word lemmas.
local instance bernoulliMatrixWordBEq (n : ℕ) : BEq (Fin n × Fin n) := instBEqOfDecidableEq

def bernoulliCenteredSquareMatrix {n : ℕ} (p : ℝ≥0) (x : BernoulliSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (bernoulliCenteredValue p (x (i, j)) : ℂ)

def bernoulliWalkEntries {n k : ℕ} (b : Fin (k + 1) → Bool)
    (v : Fin (k + 1) → Fin n) : List (Fin n × Fin n) :=
  List.ofFn (fun t => if b t then (v (finRotate (k + 1) t), v t)
    else (v t, v (finRotate (k + 1) t)))

theorem bernoulli_walk_entries_length {n k : ℕ} (b : Fin (k + 1) → Bool)
    (v : Fin (k + 1) → Fin n) : (bernoulliWalkEntries b v).length = k + 1 := by
  simp only [bernoulliWalkEntries, List.length_ofFn]

theorem bernoulli_centered_matrix_word_closed_walk {n k : ℕ} (p : ℝ≥0)
    (b : Fin (k + 1) → Bool) (v : Fin (k + 1) → Fin n) (x : BernoulliSquareSample n) :
    (∏ t, (if b t then (bernoulliCenteredSquareMatrix p x).conjTranspose
        else bernoulliCenteredSquareMatrix p x) (v t) (v (finRotate (k + 1) t))) =
      (bernoulliCenteredEntryWord p (bernoulliWalkEntries b v) x : ℂ) := by
  rw [bernoulliCenteredEntryWord, bernoulliWalkEntries, List.map_ofFn, List.prod_ofFn,
    Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro t _
  cases h : b t <;> simp [h, bernoulliCenteredSquareMatrix, Matrix.conjTranspose_apply]

theorem bernoulli_centered_matrix_word_trace_expansion {n : ℕ} (p : ℝ≥0) (k : ℕ)
    (b : Fin (k + 1) → Bool) (x : BernoulliSquareSample n) :
    (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace =
      ∑ v : Fin (k + 1) → Fin n,
        (bernoulliCenteredEntryWord p (bernoulliWalkEntries b v) x : ℂ) := by
  rw [matrixAdjointWord, List.map_ofFn, matrix_word_trace_closed_walk_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact bernoulli_centered_matrix_word_closed_walk p b v x

theorem bernoulli_centered_matrix_word_trace_real_expansion {n : ℕ} (p : ℝ≥0) (k : ℕ)
    (b : Fin (k + 1) → Bool) (x : BernoulliSquareSample n) :
    (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re =
      ∑ v : Fin (k + 1) → Fin n, bernoulliCenteredEntryWord p (bernoulliWalkEntries b v) x := by
  rw [bernoulli_centered_matrix_word_trace_expansion, Complex.re_sum]
  simp only [Complex.ofReal_re]

theorem bernoulli_centered_matrix_word_trace_integral (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp) =
      ∑ v : Fin (k + 1) → Fin n,
        ∏ e : Fin n × Fin n, bernoulliCenteredMoment p hp ((bernoulliWalkEntries b v).count e) := by
  simp_rw [bernoulli_centered_matrix_word_trace_real_expansion]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp only [bernoulliSquareMatrixLaw, bernoulli_centered_entry_word_integral]

theorem bernoulli_centered_matrix_word_trace_integral_abs_bound (n : ℕ) (p : ℝ≥0)
    (hp : p ≤ 1) (k : ℕ) (b : Fin (k + 1) → Bool) :
    |∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp| ≤
      ∑ v : Fin (k + 1) → Fin n,
        if ∀ e, (bernoulliWalkEntries b v).count e ≠ 1
          then (p : ℝ) ^ (bernoulliWalkEntries b v).toFinset.card else 0 := by
  simp_rw [bernoulli_centered_matrix_word_trace_real_expansion]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ =>
    bernoulli_centered_entry_word_integral_abs_bound_all p hp (bernoulliWalkEntries b v)))

theorem bernoulli_centered_walk_distinct_entry_bound {n k : ℕ}
    (b : Fin (k + 1) → Bool) (v : Fin (k + 1) → Fin n)
    (hNoSingleton : ∀ e, (bernoulliWalkEntries b v).count e ≠ 1) :
    2 * (bernoulliWalkEntries b v).toFinset.card ≤ k + 1 := by
  simpa only [bernoulli_walk_entries_length] using
    bernoulli_centered_entry_word_distinct_count_bound (bernoulliWalkEntries b v) hNoSingleton

theorem bernoulli_centered_two_trace_integral (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (k l : ℕ) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re *
      (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn c)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp) =
      ∑ v : Fin (k + 1) → Fin n, ∑ u : Fin (l + 1) → Fin n,
        ∏ e : Fin n × Fin n, bernoulliCenteredMoment p hp
          (((bernoulliWalkEntries b v) ++ (bernoulliWalkEntries c u)).count e) := by
  simp_rw [bernoulli_centered_matrix_word_trace_real_expansion,
    Finset.sum_mul, Finset.mul_sum, ← bernoulli_centered_entry_word_append]
  rw [integral_finset_sum _ (fun _ _ => integrable_finset_sum _ (fun _ _ => Integrable.of_finite))]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite),
    bernoulliSquareMatrixLaw, bernoulli_centered_entry_word_integral]

end CircularLaw
