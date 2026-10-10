import CircularLaw.PrincipalEigenvalueComparison
import CircularLaw.SingularValueCounting

/-!
# Singular values under addition of actual retained rows

The smaller row Gram matrix is a principal submatrix of the larger one.
Principal eigenvalue comparison and monotonicity of the square root give
the manuscript's same-position comparison, including rank-deficient rows.
-/

noncomputable section
open Classical

namespace CircularLaw

def retainedRowIndexEmbedding {n : ℕ} {H T : Finset (Fin n)} (hHT : H ⊆ T) : H ↪ T :=
  ⟨fun i => ⟨i.val, hHT i.property⟩, by
    intro i j h
    exact Subtype.ext (congrArg (fun k : T => k.val) h)⟩

theorem retainedRowGram_principal_submatrix {n d : ℕ} {H T : Finset (Fin n)}
    (hHT : H ⊆ T) (ζ : ℂ) (rows : RowSliceMatrix n d) :
    (Matrix.gram ℂ (retainedConjugateRow T ζ rows)).submatrix
      (retainedRowIndexEmbedding hHT) (retainedRowIndexEmbedding hHT) =
        Matrix.gram ℂ (retainedConjugateRow H ζ rows) := rfl

theorem retained_row_singular_values_le_of_subset {n d : ℕ} {H T : Finset (Fin n)}
    (hHT : H ⊆ T) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (i : Fin (Fintype.card H)) (j : Fin (Fintype.card T)) (hIndex : i.val = j.val) :
    retainedRowSingularValues H ζ rows i ≤ retainedRowSingularValues T ζ rows j := by
  apply Real.sqrt_le_sqrt
  have h := hermitian_principal_eigenvalues_le
    (Matrix.gram ℂ (retainedConjugateRow T ζ rows))
    (Matrix.isHermitian_gram ℂ (retainedConjugateRow T ζ rows))
    (retainedRowIndexEmbedding hHT) i j hIndex
  simpa only [retainedRowGram_principal_submatrix] using h

theorem surviving_rows_ambient_singular_value_degree_bound {n d : ℕ}
    {H T : Finset (Fin n)} (hHT : H ⊆ T) (ζ : ℂ) (rows : RowSliceMatrix n d)
    {r : ℝ} (hr : 0 < r) (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i)
    (i : Fin (Fintype.card H)) (j : Fin (Fintype.card T)) (hIndex : i.val = j.val)
    (hd : 0 < d) (hTail : Fintype.card H ≤ (Fintype.card H - i.val) * d ^ 2) :
    r / d ≤ retainedRowSingularValues T ζ rows j :=
  (surviving_rows_singular_value_degree_bound H ζ rows hr hDistance i hd hTail).trans
    (retained_row_singular_values_le_of_subset hHT ζ rows i j hIndex)

end CircularLaw
