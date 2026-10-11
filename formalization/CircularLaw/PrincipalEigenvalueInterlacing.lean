import CircularLaw.PrincipalEigenvalueComparison
import CircularLaw.SpectralCodimensionComparison

/-!
# Both sides of Cauchy interlacing for an actual principal matrix

The coordinate embedding preserves the principal quadratic form. The
same-position upper comparison and the exact codimension-shifted lower
comparison therefore bracket every ordered principal eigenvalue.
-/

noncomputable section
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem hermitian_principal_shifted_eigenvalues_le {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : κ ↪ ι)
    (i : Fin (Fintype.card κ)) (j : Fin (Fintype.card ι))
    (hIndex : j.val = i.val + (Fintype.card ι - Fintype.card κ)) :
    hA.eigenvalues₀ j ≤ (hA.submatrix f).eigenvalues₀ i := by
  apply symmetric_shifted_eigenvalues_le_under_isometry
    (Matrix.isHermitian_iff_isSymmetric.mp (hA.submatrix f))
    (Matrix.isHermitian_iff_isSymmetric.mp hA)
    finrank_euclideanSpace finrank_euclideanSpace
    (Fintype.card_le_of_injective f f.injective) (euclideanCoordinateEmbedding f)
    _ i j hIndex
  intro v
  exact (congrArg Complex.re (principal_matrix_quadratic_embedding A f v)).le

theorem hermitian_principal_eigenvalues_interlace {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : κ ↪ ι)
    (i : Fin (Fintype.card κ)) (j k : Fin (Fintype.card ι))
    (hSame : i.val = j.val)
    (hShift : k.val = i.val + (Fintype.card ι - Fintype.card κ)) :
    hA.eigenvalues₀ k ≤ (hA.submatrix f).eigenvalues₀ i ∧
      (hA.submatrix f).eigenvalues₀ i ≤ hA.eigenvalues₀ j :=
  ⟨hermitian_principal_shifted_eigenvalues_le A hA f i k hShift,
    hermitian_principal_eigenvalues_le A hA f i j hSame⟩

end CircularLaw
