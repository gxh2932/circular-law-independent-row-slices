import CircularLaw.GraphSubspaceSmallBall
import CircularLaw.LeadingRowKernelGeometry

/-!
# Graph projection bounds for the actual leading-row kernel

The singular scale is the next singular value, or zero when every row
has been retained. The uniform near-kernel estimate is proved from the
singular decomposition. A nonzero old product gives the exact kernel
dimension, so the graph projection bound needs no assumed basis or
assumed uniform image estimate.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal InnerProductSpace

namespace CircularLaw

def leadingKernelSingularScale {n m : ℕ} (r : ℕ)
    (A : Matrix (Fin n) (Fin m) ℂ) : ℝ :=
  if hr : r < n then
    orderedMatrixSingularValues A ⟨r, by simpa only [Fintype.card_fin] using hr⟩
  else 0

theorem leading_kernel_singular_scale_nonneg {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) : 0 ≤ leadingKernelSingularScale r A := by
  unfold leadingKernelSingularScale
  split
  · exact ordered_matrix_singular_values_nonneg _ _
  · exact le_refl 0

theorem leading_kernel_singular_scale_eq_next {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hr : r < n) :
    leadingKernelSingularScale r A =
      orderedMatrixSingularValues A ⟨r, by simpa only [Fintype.card_fin] using hr⟩ := by
  simp only [leadingKernelSingularScale, dif_pos hr]

theorem leading_kernel_singular_scale_eq_zero_of_full {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) : leadingKernelSingularScale n A = 0 := by
  simp only [leadingKernelSingularScale, lt_self_iff_false, ↓reduceDIte]

theorem leading_row_kernel_image_le_scale {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) :
    ‖A.toEuclideanLin v‖ ≤ leadingKernelSingularScale r A * ‖v‖ := by
  by_cases hr : r < n
  · rw [leading_kernel_singular_scale_eq_next A hr]
    exact leading_row_kernel_near_kernel_bound A h hr v hv
  · have hEq : r = n := by omega
    subst r
    rw [leading_kernel_singular_scale_eq_zero_of_full, zero_mul,
      leading_full_row_kernel_image_zero A v hv, norm_zero]

theorem leading_row_kernel_squared_image_le_scale {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (v : LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) :
    ‖A.toEuclideanLin (v : EuclideanSpace ℂ (Fin m))‖ ^ 2 ≤
      leadingKernelSingularScale r A ^ 2 * ‖v‖ ^ 2 := by
  have hBound := leading_row_kernel_image_le_scale A h
    (v : EuclideanSpace ℂ (Fin m)) v.property
  have hSquared := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (leading_kernel_singular_scale_nonneg A) (norm_nonneg _))).mpr hBound
  simpa only [mul_pow, Submodule.norm_coe] using hSquared

theorem leading_kernel_spread_coordinate_count_eq {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hProd : leadingRowSingularProduct A h ≠ 0) :
    subspaceSpreadCoordinateCount (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) =
      Nat.ceil ((m - r : ℕ) / (4096 : ℝ)) := by
  unfold subspaceSpreadCoordinateCount
  rw [leading_row_kernel_dimension A h hProd]

set_option maxHeartbeats 1500000 in
theorem bernoulli_leading_kernel_projection_of_terminal_graph {r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hProd : leadingRowSingularProduct (diagonalEmbeddedShift A e z) h ≠ 0)
    {K β n d L : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : Real.exp (Real.exp 1) ≤ d) (hDegree : d = n * p)
    (hAmbientUpper : (m : ℝ) ≤ n) (hAmbient : n / 2 ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale n d)) (hHeavy : MatrixHeavyRowBudget A β n d)
    (hSmall : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) ^ 2 <
      sourceGraphExpansion n d (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)) *
      β ^ 2 * graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 8)
    (hL : 0 ≤ L) (hRadius : L ^ 2 ≤
      (Module.finrank ℂ
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) : ℝ) *
      graphSubspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin)
        K β n d ^ 2 / 2) (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      ‖(LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin).starProjection
        (bernoulliCubeVector x + w)‖ < L} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  have hV : 0 < Module.finrank ℂ
      (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) := by
    rw [leading_row_kernel_dimension _ h hProd]
    omega
  exact bernoulli_projection_norm_small_ball_of_terminal_graph p hp hpPos hHalf A e z _ hV
    hK hβ hβOne hn hd hDegree hAmbientUpper hAmbient hz hzUpper hColumns hUnique hHeavy
    (leading_row_kernel_squared_image_le_scale _ h) hSmall hL hRadius w

end CircularLaw
