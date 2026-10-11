import CircularLaw.NormalizedInsertionLogIncrement
import CircularLaw.NormalizedSourceProjection

/-!
# Actual degree-normalized Bernoulli insertion failure bounds

Failure means either a zero new retained product or an excessive actual
degree-normalized log prefix. A large next singular value makes both
failures impossible. Otherwise the checked normalized source projection
estimate applies. Graph events remain explicit deterministic hypotheses.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem leading_kernel_scale_lt_of_degree_normalized_row_failure {r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hFailure : degreeNormalizedRowStepFailure d N δ A h x) :
    leadingKernelSingularScale r A < Real.sqrt d * Real.exp (-N * δ) := by
  by_cases hr : r < a
  · by_contra hNot
    have hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
        ⟨r, by simpa only [Fintype.card_fin] using hr⟩ := by
      rw [← leading_kernel_singular_scale_eq_next A hr]
      exact le_of_not_gt hNot
    have hSuccess := row_addition_degree_normalized_success_of_next_singular_value A h (by omega)
      x hOld hd hN hThreshold
    exact (not_degree_normalized_row_failure_iff d N δ A h x).mpr hSuccess hFailure
  · simp only [leadingKernelSingularScale, dif_neg hr]
    exact mul_pos (Real.sqrt_pos.mpr hd) (Real.exp_pos _)

theorem leading_kernel_scale_lt_of_degree_normalized_adjoint_column_failure {r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (x : EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hFailure : degreeNormalizedColumnStepFailure d N δ A.conjTranspose hRow hNext x) :
    leadingKernelSingularScale r A < Real.sqrt d * Real.exp (-N * δ) := by
  by_cases hr : r < a
  · by_contra hNot
    have hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues A.conjTranspose
        ⟨r, by simp only [Fintype.card_fin]; omega⟩ := by
      rw [← ordered_matrix_singular_values_conjTranspose A
        ⟨r, by simpa only [Fintype.card_fin] using hr⟩
        ⟨r, by simp only [Fintype.card_fin]; omega⟩ rfl,
        ← leading_kernel_singular_scale_eq_next A hr]
      exact le_of_not_gt hNot
    have hOldAdj : 0 < leadingRowSingularProduct A.conjTranspose hRow := by
      rwa [← leading_row_singular_product_conjTranspose A h hRow]
    have hSuccess := column_addition_degree_normalized_success_of_next_singular_value
      A.conjTranspose hRow h hNext (by omega) x hOldAdj hd hN hThreshold
    exact (not_degree_normalized_column_failure_iff d N δ A.conjTranspose hRow hNext x).mpr hSuccess hFailure
  · simp only [leadingKernelSingularScale, dif_neg hr]
    exact mul_pos (Real.sqrt_pos.mpr hd) (Real.exp_pos _)

set_option maxHeartbeats 1500000 in
theorem bernoulli_row_degree_normalized_failure_of_source_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d ε : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hFraction : ((N - r : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      degreeNormalizedRowStepFailure d N
        (sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
        (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w)} ≤
      normalizedSourceProjectionFailureBound ε d := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  by_cases hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) ≤
      Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
  · have hFailure := row_degree_normalized_failure_probability_le_projection_small
      (bernoulliCubeLaw (Fin m) p hp) (diagonalEmbeddedShift A e z) h
      (fun x => bernoulliCubeVector x + w) hOld hdPos hn
      (δ := sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
    simp_rw [row_adjoint_bernoulli_shift] at hFailure
    exact hFailure.trans (bernoulli_leading_kernel_projection_of_normalized_source_threshold
      p hp hpPos hHalf A e z h hrm hOld.ne' hK hβ hβOne hd hDegree hAmbient hAmbientLower
      hGuard hFraction hε hz hzUpper hColumns hUnique hHeavy hScale (rowAdjointVector w))
  · have hEmpty : {x : Fin m → Bool |
        degreeNormalizedRowStepFailure d N
          (sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
          (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hFailure
      exact hScale (leading_kernel_scale_lt_of_degree_normalized_row_failure
        (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) hOld hdPos hn hFailure).le
    rw [hEmpty, measureReal_empty]
    exact normalized_source_projection_failure_bound_nonneg
      ((div_nonneg (by positivity) hn.le).trans hFraction) hdPos.le

set_option maxHeartbeats 1500000 in
theorem bernoulli_adjoint_column_degree_normalized_failure_of_source_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d ε : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hFraction : ((N - r : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      degreeNormalizedColumnStepFailure d N
        (sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
        (diagonalEmbeddedShift A e z).conjTranspose hRow hNext (bernoulliCubeVector x + w)} ≤
      normalizedSourceProjectionFailureBound ε d := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  have hOldAdj : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z).conjTranspose hRow := by
    rwa [← leading_row_singular_product_conjTranspose (diagonalEmbeddedShift A e z) h hRow]
  by_cases hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) ≤
      Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
  · have hFailure := column_degree_normalized_failure_probability_le_projection_small
      (bernoulliCubeLaw (Fin m) p hp) (diagonalEmbeddedShift A e z).conjTranspose hRow h hNext
      (fun x => bernoulliCubeVector x + w) hOldAdj hdPos hn
      (δ := sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
    simp only [Matrix.conjTranspose_conjTranspose] at hFailure
    exact hFailure.trans (bernoulli_leading_kernel_projection_of_normalized_source_threshold
      p hp hpPos hHalf A e z h (by omega) hOld.ne' hK hβ hβOne hd hDegree hAmbient hAmbientLower
      hGuard hFraction hε hz hzUpper hColumns hUnique hHeavy hScale w)
  · have hEmpty : {x : Fin m → Bool |
        degreeNormalizedColumnStepFailure d N
          (sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))
          (diagonalEmbeddedShift A e z).conjTranspose hRow hNext (bernoulliCubeVector x + w)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hFailure
      exact hScale (leading_kernel_scale_lt_of_degree_normalized_adjoint_column_failure
        (diagonalEmbeddedShift A e z) h hRow hNext (bernoulliCubeVector x + w) hOld hdPos hn hFailure).le
    rw [hEmpty, measureReal_empty]
    exact normalized_source_projection_failure_bound_nonneg
      ((div_nonneg (by positivity) hn.le).trans hFraction) hdPos.le

end CircularLaw
