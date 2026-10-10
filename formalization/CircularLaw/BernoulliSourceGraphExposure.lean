import CircularLaw.BernoulliGraphExposure
import CircularLaw.SourceGraphProjectionThreshold

/-!
# Bernoulli graph exposure at a proved source-power threshold

The source small-rank range and the integer exposure guard discharge
both scalar comparisons. These actual row and adjoint-column log-step
probability bounds assume only the graph budgets and the stated range,
with an explicit coefficient of the source eighth-power logarithms.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem source_graph_exposure_degree_range {n d p : ℝ}
    (hn : 0 < n) (hHalf : p ≤ 1 / 2) (hDegree : d = n * p) (hd : Real.exp 4 ≤ d) :
    4 ≤ n ∧ Real.exp (Real.exp 1) ≤ d := by
  have hD : 5 ≤ d := (by linarith [Real.add_one_le_exp (4 : ℝ)] : 5 ≤ Real.exp 4).trans hd
  have hUpper : d ≤ n * (1 / 2) := by
    rw [hDegree]
    exact mul_le_mul_of_nonneg_left hHalf hn.le
  have hE : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_three]
  exact ⟨by linarith, (Real.exp_le_exp.mpr hE).trans hd⟩

set_option maxHeartbeats 1500000 in
theorem bernoulli_row_log_failure_of_source_graph_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z) h / N +
          sourceGraphLogIncrement K β N d (N - r : ℕ) <
        insertedLeadingLogPrefix (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) / N} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  obtain ⟨hN, hTerminal⟩ := source_graph_exposure_degree_range hn hHalf hDegree hd
  obtain ⟨hEnergy, hRadius⟩ := leading_kernel_source_threshold_comparisons
    (diagonalEmbeddedShift A e z) h hrm hOld.ne' hK hβ hβOne hN hd hAmbient hGuard hRange
  exact bernoulli_row_log_failure_of_terminal_graph p hp hpPos hHalf A e z h hrm hOld
    hK hβ hβOne hn hTerminal hDegree (by exact_mod_cast hAmbient) hAmbientLower hz hzUpper
    hColumns hUnique hHeavy hn hEnergy hRadius w

set_option maxHeartbeats 1500000 in
theorem bernoulli_adjoint_column_log_failure_of_source_graph_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hRow / N +
          sourceGraphLogIncrement K β N d (N - r : ℕ) <
        insertedColumnLeadingLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hNext
          (bernoulliCubeVector x + w) / N} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  obtain ⟨hN, hTerminal⟩ := source_graph_exposure_degree_range hn hHalf hDegree hd
  obtain ⟨hEnergy, hRadius⟩ := leading_kernel_source_threshold_comparisons
    (diagonalEmbeddedShift A e z) h (by omega) hOld.ne' hK hβ hβOne hN hd hAmbient hGuard hRange
  exact bernoulli_adjoint_column_log_failure_of_terminal_graph p hp hpPos hHalf A e z h hRow hNext hOld
    hK hβ hβOne hn hTerminal hDegree (by exact_mod_cast hAmbient) hAmbientLower hz hzUpper
    hColumns hUnique hHeavy hn hEnergy hRadius w

end CircularLaw
