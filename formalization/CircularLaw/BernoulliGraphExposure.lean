import CircularLaw.GraphLeadingKernel

/-!
# Actual Bernoulli log-step failure bounds from graph expansion

A failed logarithmic step forces the actual next singular scale below
the projection threshold. If the scale is larger, deterministic
interlacing makes failure impossible. Otherwise the proved leading-kernel
geometry and graph spreading supply the projection probability. Only
the graph events and two scalar threshold comparisons remain inputs.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem leading_kernel_scale_lt_of_row_log_failure {r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {N δ : ℝ} (hN : 0 < N)
    (hFailure : leadingRowLogPrefix A h / N + δ < insertedLeadingLogPrefix A h x / N) :
    leadingKernelSingularScale r A < Real.exp (-N * δ) := by
  by_cases hr : r < a
  · by_contra hNot
    have hThreshold : Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
        ⟨r, by simpa only [Fintype.card_fin] using hr⟩ := by
      rw [← leading_kernel_singular_scale_eq_next A hr]
      exact le_of_not_gt hNot
    exact not_lt_of_ge (row_addition_normalized_log_increment_of_next_singular_value
      A h (by omega) x hOld hN hThreshold) hFailure
  · simp only [leadingKernelSingularScale, dif_neg hr]
    exact Real.exp_pos _

theorem leading_kernel_scale_lt_of_adjoint_column_log_failure {r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (x : EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {N δ : ℝ} (hN : 0 < N)
    (hFailure : leadingRowLogPrefix A.conjTranspose hRow / N + δ <
      insertedColumnLeadingLogPrefix A.conjTranspose hNext x / N) :
    leadingKernelSingularScale r A < Real.exp (-N * δ) := by
  rw [inserted_column_log_prefix_eq_adjoint_row_prefix A.conjTranspose h hNext x,
    Matrix.conjTranspose_conjTranspose, ← leading_row_log_prefix_conjTranspose A h hRow] at hFailure
  exact leading_kernel_scale_lt_of_row_log_failure A h (rowAdjointVector x) hOld hN hFailure

set_option maxHeartbeats 1500000 in
theorem bernoulli_row_log_failure_of_terminal_graph {r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β n d N δ : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : Real.exp (Real.exp 1) ≤ d) (hDegree : d = n * p)
    (hAmbientUpper : (m : ℝ) ≤ n) (hAmbient : n / 2 ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale n d)) (hHeavy : MatrixHeavyRowBudget A β n d)
    (hN : 0 < N)
    (hEnergy : Real.exp (-N * δ) ^ 2 <
      sourceGraphExpansion n d (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)) *
      β ^ 2 * graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 8)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤
      (Module.finrank ℂ
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) : ℝ) *
      graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 2) (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z) h / N + δ <
        insertedLeadingLogPrefix (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) / N} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  by_cases hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) < Real.exp (-N * δ)
  · have hSmall := ((sq_le_sq₀ (leading_kernel_singular_scale_nonneg _)
      (Real.exp_pos _).le).mpr hScale.le).trans_lt hEnergy
    have hFailure := row_addition_log_failure_probability_le_projection_small
      (bernoulliCubeLaw (Fin m) p hp) (diagonalEmbeddedShift A e z) h
      (fun x => bernoulliCubeVector x + w) hOld (δ := δ) hN
    simp_rw [row_adjoint_bernoulli_shift] at hFailure
    exact hFailure.trans (bernoulli_leading_kernel_projection_of_terminal_graph
      p hp hpPos hHalf A e z h hrm hOld.ne' hK hβ hβOne hn hd hDegree hAmbientUpper hAmbient
      hz hzUpper hColumns hUnique hHeavy hSmall (Real.exp_pos _).le hRadius (rowAdjointVector w))
  · have hEmpty : {x : Fin m → Bool |
        leadingRowLogPrefix (diagonalEmbeddedShift A e z) h / N + δ <
          insertedLeadingLogPrefix (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) / N} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hFailure => hScale (leading_kernel_scale_lt_of_row_log_failure
        (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) hOld hN hFailure)
    rw [hEmpty, measureReal_empty]
    exact div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
      (Real.sqrt_nonneg _)

set_option maxHeartbeats 1500000 in
theorem bernoulli_adjoint_column_log_failure_of_terminal_graph {r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β n d N δ : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : Real.exp (Real.exp 1) ≤ d) (hDegree : d = n * p)
    (hAmbientUpper : (m : ℝ) ≤ n) (hAmbient : n / 2 ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale n d)) (hHeavy : MatrixHeavyRowBudget A β n d)
    (hN : 0 < N)
    (hEnergy : Real.exp (-N * δ) ^ 2 <
      sourceGraphExpansion n d (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)) *
      β ^ 2 * graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 8)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤
      (Module.finrank ℂ
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) : ℝ) *
      graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 2) (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hRow / N + δ <
        insertedColumnLeadingLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hNext
          (bernoulliCubeVector x + w) / N} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  by_cases hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) < Real.exp (-N * δ)
  · have hSmall := ((sq_le_sq₀ (leading_kernel_singular_scale_nonneg _)
      (Real.exp_pos _).le).mpr hScale.le).trans_lt hEnergy
    have hOldAdj : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z).conjTranspose hRow := by
      rwa [← leading_row_singular_product_conjTranspose (diagonalEmbeddedShift A e z) h hRow]
    have hFailure := column_addition_log_failure_probability_le_projection_small
      (bernoulliCubeLaw (Fin m) p hp) (diagonalEmbeddedShift A e z).conjTranspose hRow h hNext
      (fun x => bernoulliCubeVector x + w) hOldAdj (δ := δ) hN
    simp only [Matrix.conjTranspose_conjTranspose] at hFailure
    exact hFailure.trans (bernoulli_leading_kernel_projection_of_terminal_graph
      p hp hpPos hHalf A e z h (by omega) hOld.ne' hK hβ hβOne hn hd hDegree hAmbientUpper hAmbient
      hz hzUpper hColumns hUnique hHeavy hSmall (Real.exp_pos _).le hRadius w)
  · have hEmpty : {x : Fin m → Bool |
        leadingRowLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hRow / N + δ <
          insertedColumnLeadingLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hNext
            (bernoulliCubeVector x + w) / N} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hFailure => hScale (leading_kernel_scale_lt_of_adjoint_column_log_failure
        (diagonalEmbeddedShift A e z) h hRow hNext (bernoulliCubeVector x + w) hOld hN hFailure)
    rw [hEmpty, measureReal_empty]
    exact div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
      (Real.sqrt_nonneg _)

end CircularLaw
