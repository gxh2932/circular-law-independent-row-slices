import CircularLaw.MatrixSingularVolumes
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The exact unregularized projection onto a full-row-rank matrix kernel

For an invertible row Gram, 1 - K* (K K*)^-1 K is self-adjoint,
idempotent, and equals the actual orthogonal projection onto ker K.
This supplies the projection factor in the row-addition singular-volume
inequality, without replacing it by a regularized quadratic form.
-/

noncomputable section
open Classical
open scoped Matrix InnerProductSpace

namespace CircularLaw

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def rowKernelProjectionMatrix (K : Matrix ι τ ℂ) : Matrix τ τ ℂ :=
  1 - K.conjTranspose * (K * K.conjTranspose)⁻¹ * K

theorem row_kernel_projection_matrix_hermitian (K : Matrix ι τ ℂ) :
    (rowKernelProjectionMatrix K).IsHermitian :=
  Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_mul K
    (Matrix.isHermitian_mul_conjTranspose_self K).inv)

theorem row_kernel_projection_matrix_kernel_identity (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) : K * rowKernelProjectionMatrix K = 0 := by
  simp only [rowKernelProjectionMatrix, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hGram, Matrix.one_mul, sub_self]

theorem row_kernel_projection_matrix_idempotent (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) :
    rowKernelProjectionMatrix K * rowKernelProjectionMatrix K = rowKernelProjectionMatrix K := by
  change (1 - K.conjTranspose * (K * K.conjTranspose)⁻¹ * K) * rowKernelProjectionMatrix K = _
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    row_kernel_projection_matrix_kernel_identity K hGram, Matrix.mul_zero, Matrix.mul_zero, sub_zero]

theorem row_kernel_projection_matrix_mem_kernel (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (v : EuclideanSpace ℂ τ) :
    (rowKernelProjectionMatrix K).toEuclideanLin v ∈ LinearMap.ker K.toEuclideanLin := by
  apply LinearMap.mem_ker.mpr
  change ((K.toLpLin 2 2) ∘ₗ ((rowKernelProjectionMatrix K).toLpLin 2 2)) v = 0
  rw [← Matrix.toLpLin_mul_same, row_kernel_projection_matrix_kernel_identity K hGram]
  simp

theorem row_kernel_projection_matrix_fixed_on_kernel (K : Matrix ι τ ℂ)
    (v : EuclideanSpace ℂ τ) (hv : v ∈ LinearMap.ker K.toEuclideanLin) :
    (rowKernelProjectionMatrix K).toEuclideanLin v = v := by
  have hZero : K.toEuclideanLin v = 0 := LinearMap.mem_ker.mp hv
  simp only [rowKernelProjectionMatrix, Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_one,
    Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  change v - K.conjTranspose.toEuclideanLin ((K * K.conjTranspose)⁻¹.toEuclideanLin (K.toEuclideanLin v)) = v
  rw [hZero, map_zero, map_zero, sub_zero]

theorem row_kernel_projection_matrix_eq_orthogonal_projection (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (v : EuclideanSpace ℂ τ) :
    (LinearMap.ker K.toEuclideanLin).starProjection v =
      (rowKernelProjectionMatrix K).toEuclideanLin v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (row_kernel_projection_matrix_mem_kernel K hGram v)
  intro w hw
  have h := LinearMap.adjoint_inner_right (rowKernelProjectionMatrix K).toEuclideanLin v w
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    (row_kernel_projection_matrix_hermitian K).eq,
    row_kernel_projection_matrix_fixed_on_kernel K w hw] at h
  rw [inner_sub_left, ← h, sub_self]

theorem row_kernel_projection_matrix_quadratic_eq_norm (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (v : EuclideanSpace ℂ τ) :
    (⟪(rowKernelProjectionMatrix K).toEuclideanLin v, v⟫_ℂ).re =
      ‖(rowKernelProjectionMatrix K).toEuclideanLin v‖ ^ 2 := by
  have h := matrix_row_gram_quadratic_eq_adjoint_norm (rowKernelProjectionMatrix K) v
  rw [(row_kernel_projection_matrix_hermitian K).eq,
    row_kernel_projection_matrix_idempotent K hGram] at h
  exact h

theorem full_row_gram_map_surjective (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) :
    Function.Surjective K.toEuclideanLin := by
  intro w
  refine ⟨K.conjTranspose.toEuclideanLin ((K * K.conjTranspose)⁻¹.toEuclideanLin w), ?_⟩
  change ((K.toLpLin 2 2) ∘ₗ ((K.conjTranspose.toLpLin 2 2) ∘ₗ
    ((K * K.conjTranspose)⁻¹.toLpLin 2 2))) w = w
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hGram, Matrix.toLpLin_one, LinearMap.id_apply]

theorem full_row_gram_kernel_dimension (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) :
    Module.finrank ℂ (LinearMap.ker K.toEuclideanLin) = Fintype.card τ - Fintype.card ι := by
  have hRank := K.toEuclideanLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (full_row_gram_map_surjective K hGram),
    finrank_top] at hRank
  simp only [finrank_euclideanSpace] at hRank
  omega

end CircularLaw
