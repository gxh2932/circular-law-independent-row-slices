import CircularLaw.MatrixDiscrepancy
import CircularLaw.RowSliceColumnBounds
import CircularLaw.Moments

/-!
# The actual rectangular matrix satisfies the checked discrepancy law

This bridge identifies support-intersection counts with sums of the
literal zero-one matrix entries. Its discrepancy and row/column
conditions are therefore the exact deterministic inputs required by
the heavy-term argument.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rectangularSliceMatrixReal {m n d : ℕ} (rows : Fin m → RowSlice n d) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => rowEntryReal (rows i) j

theorem rectangularSliceMatrixReal_nonneg {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (i : Fin m) (j : Fin n) : 0 ≤ rectangularSliceMatrixReal rows i j := by
  unfold rectangularSliceMatrixReal rowEntryReal
  split_ifs <;> norm_num

theorem rectangularSliceMatrixReal_rowSum {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (i : Fin m) : (∑ j : Fin n, rectangularSliceMatrixReal rows i j) = d := by
  simp [rectangularSliceMatrixReal, rowEntryReal, (rows i).property]

theorem rectangularSliceMatrixReal_edgeCount {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    matrixEdgeCount (rectangularSliceMatrixReal rows) S T = rowSliceEdgeCount S T rows := by
  rw [rowSliceEdgeCount_eq_intersection_sum]
  rw [Nat.cast_sum]
  unfold matrixEdgeCount
  apply Finset.sum_congr rfl
  intro i _
  simp only [rectangularSliceMatrixReal, rowEntryReal, Finset.sum_boole]
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

theorem rectangularSliceMatrixReal_columnCount {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (j : Fin n) : rowSliceColumnCount rows j = ∑ i : Fin m, rectangularSliceMatrixReal rows i j := by
  unfold rowSliceColumnCount
  rw [← rectangularSliceMatrixReal_edgeCount]
  simp only [matrixEdgeCount, Finset.sum_singleton]

theorem rectangularSliceMatrixReal_discrepancy_iff {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (kappa₁ kappa₂ : ℝ) :
    MatrixDiscrepancy ((d : ℝ) / n) kappa₁ kappa₂ (rectangularSliceMatrixReal rows) ↔
      RowSliceDiscrepancy kappa₁ kappa₂ rows := by
  simp only [MatrixDiscrepancy, RowSliceDiscrepancy, rectangularSliceMatrixReal_edgeCount, rowSliceEdgeMean]

theorem rectangularSliceMatrixReal_rowColumnBound_iff {m n d : ℕ} (rows : Fin m → RowSlice n d) :
    MatrixRowColumnBound (9 * d) (rectangularSliceMatrixReal rows) ↔ RowSliceColumnBound (9 * d) rows := by
  constructor
  · intro h j
    rw [rectangularSliceMatrixReal_columnCount]
    exact h.2 j
  · intro h
    constructor
    · intro i
      rw [rectangularSliceMatrixReal_rowSum]
      nlinarith only [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    · intro j
      rw [← rectangularSliceMatrixReal_columnCount]
      exact h j

theorem rectangularSliceMatrixReal_discrepancy_probability {m n d : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    1 - (n : ℝ) ^ (-beta) ≤ uniformProbability (fun rows : Fin m → RowSlice n d =>
      MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (rectangularSliceMatrixReal rows)) := by
  simp_rw [rectangularSliceMatrixReal_discrepancy_iff]
  exact rowSliceDiscrepancy_good_probability hn hmn hd hdn hBeta

theorem weightedSliceMatrixSum_eq_real_bilinear {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (Q : Fin m → Fin n → ℝ) :
    weightedSliceMatrixSum Q rows = ∑ i : Fin m, ∑ j : Fin n, rectangularSliceMatrixReal rows i j * Q i j := by
  unfold weightedSliceMatrixSum weightedSliceSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold rectangularSliceMatrixReal rowEntryReal
  split_ifs <;> simp only [one_mul, zero_mul]

end CircularLaw
