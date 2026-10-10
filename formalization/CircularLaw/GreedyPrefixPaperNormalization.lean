import CircularLaw.GreedyExposureCompletion
import CircularLaw.SquareRetainedPrefixIdentities
import CircularLaw.BernoulliPrincipalMinorLaw

/-!
# The actual normalized manuscript matrices in the greedy comparison

The process uses the raw shift z*sqrt(d). Degree normalization gives
exactly B/sqrt(d)-z I, including every principal minor. The initial and
terminal retained products and log sums are identified with the literal
manuscript quantities, retaining the ambient denominator N.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal

namespace CircularLaw

def sourceRawBernoulliShift (d : ℕ) (z : ℂ) : ℂ := z * (Real.sqrt (d : ℝ) : ℂ)

theorem degree_normalized_square_embedded_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {d : ℝ} (hd : 0 < d) :
    degreeNormalizingScalar d • diagonalEmbeddedShift A (Function.Embedding.refl _)
      (z * (Real.sqrt d : ℂ)) = degreeNormalizingScalar d • A - z • 1 := by
  have hRoot : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  ext i j
  by_cases hij : i = j
  · simp only [diagonalEmbeddedShift, Function.Embedding.refl_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.sub_apply, Matrix.one_apply, if_pos hij, mul_one, degreeNormalizingScalar]
    field_simp [hRoot]
  · simp [diagonalEmbeddedShift, hij, degreeNormalizingScalar, Matrix.smul_apply,
      smul_eq_mul, Matrix.sub_apply]

theorem degree_normalized_bernoulli_ambient_square_prefix {N M : ℕ}
    (hM : M ≤ N) {d : ℕ} (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample N) :
    degreeNormalizingScalar (d : ℝ) • bernoulliShiftedAmbientPrefix hM hM (le_refl M)
      (sourceRawBernoulliShift d z) x = squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hM := by
  rw [bernoulli_shifted_principal_minor_matrix_eq]
  exact degree_normalized_square_embedded_shift _ z (by exact_mod_cast hd)

theorem source_initial_normalized_retained_product {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ M) {d : ℕ} (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedProduct N M 0 r d (sourceRawBernoulliShift d z)
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x) =
      leadingRowSingularProduct (squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hM) hr := by
  have hProduct := source_prefix_retained_product_at_dimensions hM hM (le_refl M)
    (source_alternating_prefix_initial hM).1 (source_alternating_prefix_initial hM).2
    hr d (sourceRawBernoulliShift d z) x
  rw [degree_normalized_bernoulli_ambient_square_prefix hM hd] at hProduct
  exact hProduct

theorem source_initial_normalized_retained_log {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ M) {d : ℕ} (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedLog N M 0 r d (sourceRawBernoulliShift d z)
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x) =
      squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix d z x) hM r := by
  have hLog := source_prefix_retained_log_at_dimensions hM hM (le_refl M)
    (source_alternating_prefix_initial hM).1 (source_alternating_prefix_initial hM).2
    hr d (sourceRawBernoulliShift d z) x
  rw [degreeNormalizedLeadingLogPrefix, degree_normalized_bernoulli_ambient_square_prefix hM hd,
    leading_row_square_log_prefix_eq_range_sum] at hLog
  exact hLog

theorem source_terminal_normalized_retained_product {N M : ℕ}
    (hM : M ≤ N) {d : ℕ} (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedProduct N M (2 * (N - M)) N d (sourceRawBernoulliShift d z)
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (2 * (N - M)))
        (source_alternating_prefix_columns_le N M (2 * (N - M))) x) =
      leadingRowSingularProduct (normalizedShiftedBernoulliMatrix d z x) (le_refl N) := by
  have hProduct := source_prefix_retained_product_at_dimensions (le_refl N) (le_refl N) (le_refl N)
    (source_alternating_prefix_terminal hM).1 (source_alternating_prefix_terminal hM).2
    (le_refl N) d (sourceRawBernoulliShift d z) x
  rw [degree_normalized_bernoulli_ambient_square_prefix (le_refl N) hd] at hProduct
  exact hProduct

theorem source_terminal_normalized_retained_log {N M : ℕ}
    (hM : M ≤ N) {d : ℕ} (hd : 0 < d) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedLog N M (2 * (N - M)) N d (sourceRawBernoulliShift d z)
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (2 * (N - M)))
        (source_alternating_prefix_columns_le N M (2 * (N - M))) x) =
      squareNegativeLogMean (normalizedShiftedBernoulliMatrix d z x) := by
  have hLog := source_prefix_retained_log_at_dimensions (le_refl N) (le_refl N) (le_refl N)
    (source_alternating_prefix_terminal hM).1 (source_alternating_prefix_terminal hM).2
    (le_refl N) d (sourceRawBernoulliShift d z) x
  rw [degreeNormalizedLeadingLogPrefix, degree_normalized_bernoulli_ambient_square_prefix (le_refl N) hd,
    leading_row_square_full_log_prefix] at hLog
  exact hLog

theorem source_initial_positive_complement_eq_minor_zero {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ M) {d : ℕ} (hd : 0 < d) (β : ℝ) (z : ℂ) :
    (sourceGreedyInitialPositiveEvent N M r β d (sourceRawBernoulliShift d z))ᶜ =
      {x | empiricalPrefixHasZero
        (squareSingularValuesNNReal (squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hM)) r} := by
  ext x
  change ¬ (0 < sourcePrefixRetainedProduct N M 0
    (sourceGreedyPrefixRank N M r β d (sourceRawBernoulliShift d z) 0 x) d (sourceRawBernoulliShift d z)
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
      (source_alternating_prefix_columns_le N M 0) x)) ↔ _
  rw [source_greedy_prefix_initial_rank hM hr, source_initial_normalized_retained_product hM hr hd,
    leading_row_square_product_pos_iff_prefix_no_zero, not_not]
  rfl

end CircularLaw
