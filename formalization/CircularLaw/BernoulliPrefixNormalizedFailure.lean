import CircularLaw.BernoulliPrefixInsertionViews
import CircularLaw.SourceConditionalInsertion

/-!
# Conditional failure events are the actual prefix failure events

The insertion interfaces use a reindexed inserted product. These checked
identities identify its zero-product and logarithmic failure with the
actual next square or rectangle, including the conjugate raw shift in
the adjoint column interface.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem last_row_degree_normalized_failure_iff {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1)
    (d N δ : ℝ) :
    degreeNormalizedRowStepFailure d N δ (B.submatrix Fin.castSucc id) hOld (lastRowVector B) ↔
      leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew = 0 ∨
        degreeNormalizedLeadingLogPrefix d (B.submatrix Fin.castSucc id) hOld / N + δ <
          degreeNormalizedLeadingLogPrefix d B hNew / N := by
  have hProduct := last_row_leading_singular_product (degreeNormalizingScalar d • B) hOld hNew
  rw [last_row_vector_smul] at hProduct
  change leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew =
    insertedLeadingSingularProduct (degreeNormalizingScalar d • B.submatrix Fin.castSucc id)
      hOld (degreeNormalizingScalar d • lastRowVector B) at hProduct
  rw [degreeNormalizedRowStepFailure, ← hProduct,
    ← last_row_degree_normalized_log_prefix B hOld hNew d]

theorem last_column_degree_normalized_failure_iff {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n)
    (d N δ : ℝ) :
    degreeNormalizedColumnStepFailure d N δ (B.submatrix id Fin.castSucc) hOld hNew
      (lastColumnVector B) ↔
      leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew = 0 ∨
        degreeNormalizedLeadingLogPrefix d (B.submatrix id Fin.castSucc) hOld / N + δ <
          degreeNormalizedLeadingLogPrefix d B hNew / N := by
  have hProduct := last_column_leading_singular_product (degreeNormalizingScalar d • B) hNew
  rw [last_column_vector_smul] at hProduct
  change leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew =
    insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • B.submatrix id Fin.castSucc)
      hNew (degreeNormalizingScalar d • lastColumnVector B) at hProduct
  rw [degreeNormalizedColumnStepFailure, ← hProduct,
    ← last_column_degree_normalized_log_prefix B hNew d]

theorem bernoulli_ambient_row_normalized_failure_iff {N m r : ℕ}
    (hm : m ≤ N) (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ)
    (hr : r ≤ m) (d δ : ℝ) :
    degreeNormalizedRowStepFailure d N δ
      (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z) hr
      (bernoulliCubeVector (fun j => x (bernoulliFreshRowEntryEmbedding hNext hNext j)) +
        sourceLastDiagonalRowShift m z) ↔
      leadingRowSingularProduct
        (degreeNormalizingScalar d • bernoulliShiftedSquarePrefix (bernoulliPrefixSample hNext hNext x) z)
        (Nat.succ_le_succ hr) = 0 ∨
      degreeNormalizedLeadingLogPrefix d
        (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z) hr / N + δ <
      degreeNormalizedLeadingLogPrefix d
        (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hNext hNext x) z)
        (Nat.succ_le_succ hr) / N := by
  have hFailure := last_row_degree_normalized_failure_iff
    (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hNext hNext x) z)
    hr (Nat.succ_le_succ hr) d N δ
  rw [bernoulli_ambient_row_prefix_old hm hNext,
    bernoulli_ambient_row_prefix_fresh hNext] at hFailure
  exact hFailure

theorem bernoulli_ambient_column_normalized_failure_iff {N m r : ℕ}
    (hm : m ≤ N) (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ)
    (hr : r ≤ m) (hrNext : r + 1 ≤ m) (d δ : ℝ) :
    degreeNormalizedColumnStepFailure d N δ
      (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hm hm x) z) hr hrNext
      (bernoulliCubeVector (fun i => x (bernoulliFreshColumnEntryEmbedding hm hNext i))) ↔
      leadingRowSingularProduct
        (degreeNormalizingScalar d • bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z)
        hrNext = 0 ∨
      degreeNormalizedLeadingLogPrefix d
        (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hm hm x) z) hr / N + δ <
      degreeNormalizedLeadingLogPrefix d
        (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z) hrNext / N := by
  have hFailure := last_column_degree_normalized_failure_iff
    (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z) hr hrNext d N δ
  rw [bernoulli_ambient_column_prefix_old hm hNext,
    bernoulli_ambient_column_prefix_fresh hm hNext] at hFailure
  exact hFailure

theorem source_prefix_adjoint_column_failure_eq_square_failure {N m : ℕ}
    (u : Fin m × Fin m → Bool) (y : Fin m → Bool) (z : ℂ) (β d : ℝ)
    (r : (Fin m × Fin m → Bool) → ℕ) (hr : ∀ v, r v ≤ m)
    (hNext : r u + 1 ≤ m) :
    sourcePrefixAdjointColumnInsertionFailure (N := N) (Function.Embedding.refl _) (star z)
      β d r hr (fun _ => 0) u y ↔
      degreeNormalizedColumnStepFailure d N
        (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r u : ℕ))
        (bernoulliShiftedSquarePrefix u z) (hr u) hNext (bernoulliCubeVector y) := by
  rw [sourcePrefixAdjointColumnInsertionFailure, dif_pos hNext,
    ← bernoulli_shifted_square_prefix_adjoint, Matrix.conjTranspose_conjTranspose, add_zero]

end CircularLaw
