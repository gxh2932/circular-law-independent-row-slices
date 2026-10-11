import CircularLaw.FiniteUniformEmbeddingRestriction
import CircularLaw.RowSliceColumnLowerBounds

/-!
# Lower column degrees for the actual retained square-matrix rows

Every injective row selection has the unchanged ambient d/n law. In
particular, the one-row-deleted column estimates apply to the actual
square sample, with no assumed marginal law.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem row_slice_retained_column_lower_probability {m n d : ℕ}
    (hdn : d ≤ n) (u : Fin m ↪ Fin n) (B : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RowSliceColumnLowerBound B (fun i => rows (u i))) =
        uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceColumnLowerBound B rows) := by
  haveI := rowSlice_nonempty hdn
  exact uniformProbability_pi_embedding_restrict (α := RowSlice n d) u
    (fun rows : Fin m → RowSlice n d => ¬RowSliceColumnLowerBound B rows)

theorem actual_one_row_deleted_column_five_sixths_failure {n d : ℕ}
    (hn : 11 ≤ n) (hdn : d ≤ n) (u : Fin (n - 1) ↪ Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) (fun i => rows (u i))) ≤
        (n : ℝ) * Real.exp (-(d : ℝ) / 320) := by
  rw [row_slice_retained_column_lower_probability hdn]
  exact one_row_deleted_column_five_sixths_failure hn hdn

theorem actual_one_row_deleted_column_lower_failure_polynomial {n d : ℕ}
    (hn : 11 ≤ n) (hdn : d ≤ n) (u : Fin (n - 1) ↪ Fin n) (A : ℝ)
    (hDegree : 320 * (A + 1) * Real.log (n : ℝ) ≤ d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) (fun i => rows (u i))) ≤ (n : ℝ) ^ (-A) := by
  rw [row_slice_retained_column_lower_probability hdn]
  exact one_row_deleted_column_lower_failure_polynomial hn hdn A hDegree

end CircularLaw
