import CircularLaw.EuclideanCoordinateEmbedding

/-!
# Ordered eigenvalues of a principal Hermitian submatrix

The coordinate isometry identifies the principal quadratic form with the
ambient quadratic form. The checked spectral dimension comparison then
bounds each decreasingly ordered principal eigenvalue by the ambient
eigenvalue at the same zero-based position.
-/

noncomputable section
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem hermitian_principal_eigenvalues_le {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : κ ↪ ι)
    (i : Fin (Fintype.card κ)) (j : Fin (Fintype.card ι)) (hIndex : i.val = j.val) :
    (hA.submatrix f).eigenvalues₀ i ≤ hA.eigenvalues₀ j := by
  apply symmetric_ordered_eigenvalues_le_under_isometry
    (Matrix.isHermitian_iff_isSymmetric.mp (hA.submatrix f))
    (Matrix.isHermitian_iff_isSymmetric.mp hA)
    finrank_euclideanSpace finrank_euclideanSpace (euclideanCoordinateEmbedding f)
    _ i j hIndex
  intro v
  exact (congrArg Complex.re (principal_matrix_quadratic_embedding A f v)).symm.le

end CircularLaw
