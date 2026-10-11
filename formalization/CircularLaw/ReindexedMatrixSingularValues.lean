import CircularLaw.RectangularAdjointSingularValues

/-!
# Ordered singular values under exact finite reindexing

Row and column permutations preserve the actual Gram characteristic
roots and hence every sorted singular position. The result allows a
disjoint-union inserted row or column to be moved to the last index of
the manuscript's finite principal-block exposure.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem reindexed_matrix_row_gram {ι τ κ ν : Type*}
    [Fintype ι] [Fintype τ] [Fintype κ] [Fintype ν]
    (A : Matrix ι τ ℂ) (eRow : ι ≃ κ) (eCol : τ ≃ ν) :
    Matrix.reindex eRow eCol A * (Matrix.reindex eRow eCol A).conjTranspose =
      Matrix.reindex eRow eRow (A * A.conjTranspose) := by
  rw [Matrix.conjTranspose_reindex]
  exact Matrix.submatrix_mul_equiv A A.conjTranspose eRow.symm eCol.symm eRow.symm

theorem reindexed_hermitian_ordered_eigenvalues {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Matrix ι ι ℂ) (hG : G.IsHermitian) (e : ι ≃ κ)
    (i : Fin (Fintype.card ι)) (j : Fin (Fintype.card κ)) (hIndex : i.val = j.val) :
    hG.eigenvalues₀ i = (hG.submatrix e.symm).eigenvalues₀ j := by
  have hList : List.ofFn hG.eigenvalues₀ = List.ofFn (hG.submatrix e.symm).eigenvalues₀ := by
    rw [← hG.sort_roots_charpoly_eq_eigenvalues₀,
      ← (hG.submatrix e.symm).sort_roots_charpoly_eq_eigenvalues₀]
    change _ = ((Matrix.reindex e e G).charpoly.roots.map RCLike.re).sort (· ≥ ·)
    rw [Matrix.charpoly_reindex]
  have hEntry := congrArg (fun l : List ℝ => l[i.val]?) hList
  dsimp only at hEntry
  have hVal : (⟨i.val, by omega⟩ : Fin (Fintype.card κ)) = j := Fin.ext hIndex
  simpa only [List.getElem?_ofFn, dif_pos i.isLt, dif_pos (by omega : i.val < Fintype.card κ),
    hVal, Option.some.injEq] using hEntry

theorem ordered_matrix_singular_values_reindex {ι τ κ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (A : Matrix ι τ ℂ) (eRow : ι ≃ κ) (eCol : τ ≃ ν)
    (i : Fin (Fintype.card ι)) (j : Fin (Fintype.card κ)) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues A i = orderedMatrixSingularValues (Matrix.reindex eRow eCol A) j := by
  unfold orderedMatrixSingularValues
  simp only [reindexed_matrix_row_gram]
  exact congrArg Real.sqrt (reindexed_hermitian_ordered_eigenvalues
    (A * A.conjTranspose) (Matrix.isHermitian_mul_conjTranspose_self A) eRow i j hIndex)

end CircularLaw
