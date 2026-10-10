import CircularLaw.RowAdditionSingularProducts

/-!
# Geometry of the leading-row kernel

The selected left-singular coordinates vanish on the leading-row
kernel. Its dimension is m-r whenever the leading singular product
is nonzero. The following Rayleigh estimate identifies its vectors as
near-kernel vectors at the next singular-value scale.
-/

noncomputable section
open Classical
open scoped Matrix InnerProductSpace BigOperators

namespace CircularLaw

theorem hermitian_eigenvector_unitary_coordinates {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.IsHermitian)
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hG.eigenvectorUnitary.val.conjTranspose.toEuclideanLin v i =
      hG.eigenvectorBasis.repr v i := by
  rw [OrthonormalBasis.repr_apply_apply, PiLp.inner_apply]
  change (∑ j, star (hG.eigenvectorUnitary.val j i) * v j) =
    ∑ j, ⟪hG.eigenvectorBasis i j, v j⟫_ℂ
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, RCLike.inner_apply]
  exact mul_comm _ _

theorem leading_row_compression_coordinates {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (v : EuclideanSpace ℂ (Fin n)) (j : Fin r) :
    (leadingRowCompression A h).toEuclideanLin v j =
      ((Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A)).eigenvectorBasis
        finrank_euclideanSpace).repr v (leadingSingularIndex h j) := by
  change (Matrix.isHermitian_mul_conjTranspose_self A).eigenvectorUnitary.val.conjTranspose.toEuclideanLin
    v (leadingRowEigenIndex h j) = _
  rw [hermitian_eigenvector_unitary_coordinates]
  simp only [Matrix.IsHermitian.eigenvectorBasis, OrthonormalBasis.repr_reindex,
    leadingRowEigenIndex, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]

theorem leading_row_kernel_dimension {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hProd : leadingRowSingularProduct A h ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) = m - r := by
  simpa only [Fintype.card_fin] using full_row_gram_kernel_dimension
    (leadingCompressedRows A h) (leading_compressed_rows_gram_invertible A h hProd)

theorem leading_row_kernel_image_coordinates_zero {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val < r) :
    ((Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A)).eigenvectorBasis
      finrank_euclideanSpace).repr (A.toEuclideanLin v) i = 0 := by
  let j : Fin r := ⟨i.val, hi⟩
  have hZero := congrArg (fun w : EuclideanSpace ℂ (Fin r) => w j) (LinearMap.mem_ker.mp hv)
  simp only [leadingCompressedRows, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply, PiLp.zero_apply] at hZero
  change ((leadingRowCompression A h).toEuclideanLin (A.toEuclideanLin v)) j = 0 at hZero
  rw [leading_row_compression_coordinates] at hZero
  exact hZero

theorem leading_row_kernel_near_kernel_bound {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hr : r < n)
    (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) :
    ‖A.toEuclideanLin v‖ ≤
      orderedMatrixSingularValues A ⟨r, by simpa only [Fintype.card_fin] using hr⟩ * ‖v‖ := by
  let j : Fin (Fintype.card (Fin n)) := ⟨r, by simpa only [Fintype.card_fin] using hr⟩
  have hRay := symmetric_quadratic_le_tail
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A))
    finrank_euclideanSpace j (A.toEuclideanLin v) (by
      intro i hi
      exact leading_row_kernel_image_coordinates_zero A h v hv i hi)
  rw [matrix_row_gram_quadratic_eq_adjoint_norm] at hRay
  change ‖A.conjTranspose.toEuclideanLin (A.toEuclideanLin v)‖ ^ 2 ≤
    (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ j * ‖A.toEuclideanLin v‖ ^ 2 at hRay
  rw [← ordered_matrix_singular_values_sq A j] at hRay
  have hAdj := congrArg Complex.re (LinearMap.adjoint_inner_left A.toEuclideanLin v (A.toEuclideanLin v))
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hAdj
  change RCLike.re ⟪A.conjTranspose.toEuclideanLin (A.toEuclideanLin v), v⟫_ℂ =
    RCLike.re ⟪A.toEuclideanLin v, A.toEuclideanLin v⟫_ℂ at hAdj
  have hCauchy := re_inner_le_norm (𝕜 := ℂ)
    (A.conjTranspose.toEuclideanLin (A.toEuclideanLin v)) v
  rw [hAdj, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at hCauchy
  have hSq := (sq_le_sq₀ (sq_nonneg ‖A.toEuclideanLin v‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg v))).mpr hCauchy
  rw [mul_pow] at hSq
  have hCombined := hSq.trans (mul_le_mul_of_nonneg_right hRay (sq_nonneg ‖v‖))
  by_cases hZero : ‖A.toEuclideanLin v‖ = 0
  · rw [hZero]
    exact mul_nonneg (ordered_matrix_singular_values_nonneg A j) (norm_nonneg v)
  · have hPos : 0 < ‖A.toEuclideanLin v‖ ^ 2 := sq_pos_of_ne_zero hZero
    have hCancel : ‖A.toEuclideanLin v‖ ^ 2 ≤ (orderedMatrixSingularValues A j * ‖v‖) ^ 2 := by
      apply (mul_le_mul_iff_left₀ hPos).mp
      nlinarith [hCombined]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      (ordered_matrix_singular_values_nonneg A j) (norm_nonneg v))).mp hCancel

theorem leading_full_row_kernel_image_zero {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (leadingCompressedRows A (le_refl n)).toEuclideanLin) :
    A.toEuclideanLin v = 0 := by
  let Q := leadingRowCompression A (le_refl n)
  have hQ : Q.conjTranspose * Q = 1 :=
    mul_eq_one_comm.mp (leading_row_compression_coisometry A (le_refl n))
  have hZero := LinearMap.mem_ker.mp hv
  simp only [leadingCompressedRows, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply] at hZero
  change Q.toEuclideanLin (A.toEuclideanLin v) = 0 at hZero
  have hBack := congrArg Q.conjTranspose.toEuclideanLin hZero
  change ((Q.conjTranspose.toLpLin 2 2) ∘ₗ (Q.toLpLin 2 2)) (A.toEuclideanLin v) = _ at hBack
  rw [← Matrix.toLpLin_mul_same, hQ, Matrix.toLpLin_one, LinearMap.id_apply] at hBack
  simpa only [map_zero] using hBack

theorem leading_full_row_kernel_eq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) :
    LinearMap.ker (leadingCompressedRows A (le_refl n)).toEuclideanLin =
      LinearMap.ker A.toEuclideanLin := by
  ext v
  constructor
  · exact fun hv => LinearMap.mem_ker.mpr (leading_full_row_kernel_image_zero A v hv)
  · intro hv
    apply LinearMap.mem_ker.mpr
    simp only [leadingCompressedRows, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply]
    change (leadingRowCompression A (le_refl n)).toEuclideanLin (A.toEuclideanLin v) = 0
    rw [LinearMap.mem_ker.mp hv, map_zero]

end CircularLaw
