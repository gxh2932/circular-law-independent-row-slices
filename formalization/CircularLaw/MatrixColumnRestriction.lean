import CircularLaw.RectangularSingularInterlacing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Column restriction and the exact erased-coordinate kernel

The row-Gram quadratic form equals the squared Euclidean norm of `A* v`.
Deleting columns removes exactly those coordinates. On the kernel of the
actual erased-coordinate matrix, both quadratic forms are identical.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix InnerProductSpace

namespace CircularLaw

def matrixColumnRestriction {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) :
    Matrix (Fin m) (Fin k) ℂ := A.submatrix id f

def erasedColumnIndices {n k : ℕ} (f : Fin k ↪ Fin n) : Finset (Fin n) :=
  Finset.univ \ Finset.univ.image f

theorem erasedColumnIndices_card {n k : ℕ} (f : Fin k ↪ Fin n) :
    Fintype.card (erasedColumnIndices f) = n - k := by
  rw [Fintype.card_coe, erasedColumnIndices,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin,
    Finset.card_image_of_injective _ f.injective]

def erasedColumnMap {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (erasedColumnIndices f) :=
  (A.conjTranspose.submatrix (fun j : erasedColumnIndices f => j.val) id).toEuclideanLin

theorem erasedColumnMap_apply {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (f : Fin k ↪ Fin n) (v : EuclideanSpace ℂ (Fin m)) (j : erasedColumnIndices f) :
    erasedColumnMap A f v j = A.conjTranspose.toEuclideanLin v j.val := rfl

theorem column_restriction_adjoint_apply {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (f : Fin k ↪ Fin n) (v : EuclideanSpace ℂ (Fin m)) (j : Fin k) :
    (matrixColumnRestriction A f).conjTranspose.toEuclideanLin v j =
      A.conjTranspose.toEuclideanLin v (f j) := rfl

theorem row_gram_quadratic_eq_adjoint_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    (⟪(A * A.conjTranspose).toEuclideanLin v, v⟫_ℂ).re =
      ‖A.conjTranspose.toEuclideanLin v‖ ^ 2 := by
  have h := LinearMap.adjoint_inner_right A.toEuclideanLin (A.conjTranspose.toEuclideanLin v) v
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [← h]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A.conjTranspose.toEuclideanLin v)).symm

theorem erasedColumnMap_kernel_zero {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (f : Fin k ↪ Fin n) (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (erasedColumnMap A f)) (j : Fin n)
    (hj : j ∈ erasedColumnIndices f) : A.conjTranspose.toEuclideanLin v j = 0 := by
  have h := congrArg (fun w : EuclideanSpace ℂ (erasedColumnIndices f) => w ⟨j, hj⟩)
    (LinearMap.mem_ker.mp hv)
  simpa only [erasedColumnMap_apply, PiLp.zero_apply] using h

theorem euclidean_coordinate_restriction_energy_le {n k : ℕ} (f : Fin k ↪ Fin n)
    (w : EuclideanSpace ℂ (Fin n)) : (∑ j, ‖w (f j)‖ ^ 2) ≤ ∑ j, ‖w j‖ ^ 2 := by
  calc
    _ = ∑ j ∈ Finset.univ.image f, ‖w j‖ ^ 2 := by
      rw [Finset.sum_image (fun _ _ _ _ h => f.injective h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

theorem euclidean_coordinate_restriction_energy_eq {n k : ℕ} (f : Fin k ↪ Fin n)
    (w : EuclideanSpace ℂ (Fin n)) (hZero : ∀ j ∈ erasedColumnIndices f, w j = 0) :
    (∑ j, ‖w j‖ ^ 2) = ∑ j, ‖w (f j)‖ ^ 2 := by
  have hSum : (∑ j ∈ Finset.univ.image f, ‖w j‖ ^ 2) = ∑ j, ‖w j‖ ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hNot
    rw [hZero j (Finset.mem_sdiff.mpr ⟨hj, hNot⟩)]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [← hSum, Finset.sum_image (fun _ _ _ _ h => f.injective h)]

theorem column_restriction_quadratic_le {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (f : Fin k ↪ Fin n) (v : EuclideanSpace ℂ (Fin m)) :
    (⟪(matrixColumnRestriction A f * (matrixColumnRestriction A f).conjTranspose).toEuclideanLin v,
      v⟫_ℂ).re ≤ (⟪(A * A.conjTranspose).toEuclideanLin v, v⟫_ℂ).re := by
  rw [row_gram_quadratic_eq_adjoint_norm, row_gram_quadratic_eq_adjoint_norm,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [column_restriction_adjoint_apply]
  exact euclidean_coordinate_restriction_energy_le f _

theorem column_restriction_quadratic_eq_on_kernel {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) (v : EuclideanSpace ℂ (Fin m))
    (hv : v ∈ LinearMap.ker (erasedColumnMap A f)) :
    (⟪(A * A.conjTranspose).toEuclideanLin v, v⟫_ℂ).re =
      (⟪(matrixColumnRestriction A f * (matrixColumnRestriction A f).conjTranspose).toEuclideanLin v,
        v⟫_ℂ).re := by
  rw [row_gram_quadratic_eq_adjoint_norm, row_gram_quadratic_eq_adjoint_norm,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [column_restriction_adjoint_apply]
  exact euclidean_coordinate_restriction_energy_eq f _ (erasedColumnMap_kernel_zero A f v hv)

end CircularLaw
