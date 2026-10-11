import CircularLaw.MatrixSingularVolumes

/-!
# Ordered singular values of a rectangular matrix and its adjoint

The two Gram characteristic polynomials differ only by the required
power of X. Their actual root multisets therefore differ by zero roots.
Since the Gram eigenvalues are nonnegative, those zeros appear at the
end of the decreasingly sorted list. Every common singular position
agrees, including rank-deficient matrices and unequal dimensions.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

theorem hermitian_real_charpoly_roots (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    G.charpoly.roots.map RCLike.re = (List.ofFn hG.eigenvalues₀ : Multiset ℝ) := by
  simp only [hG.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe,
    List.map_ofFn, Function.comp_def, RCLike.ofReal_re]

theorem row_column_gram_real_roots (A : Matrix ι τ ℂ)
    (hCard : Fintype.card ι ≤ Fintype.card τ) :
    (A.conjTranspose * A).charpoly.roots.map RCLike.re =
      (List.ofFn (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ : Multiset ℝ) +
        Multiset.replicate (Fintype.card τ - Fintype.card ι) 0 := by
  rw [Matrix.charpoly_mul_comm_of_le A.conjTranspose A hCard,
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (A * A.conjTranspose).charpoly_monic.ne_zero), Polynomial.roots_X_pow,
    Multiset.map_add, hermitian_real_charpoly_roots]
  simp only [Multiset.map_nsmul, Multiset.map_singleton, map_zero]
  rw [Multiset.nsmul_singleton, add_comm]

theorem row_column_gram_ordered_eigenvalue_list (A : Matrix ι τ ℂ)
    (hCard : Fintype.card ι ≤ Fintype.card τ) :
    List.ofFn (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ =
      List.ofFn (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ ++
        List.replicate (Fintype.card τ - Fintype.card ι) 0 := by
  let L := Matrix.isHermitian_mul_conjTranspose_self A
  have hSorted : (List.ofFn L.eigenvalues₀ ++
      List.replicate (Fintype.card τ - Fintype.card ι) 0).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← List.sortedGE_iff_pairwise] using L.eigenvalues₀_antitone.sortedGE_ofFn
    · simp
    · intro a ha b hb
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      have hbZero : b = 0 := (List.mem_replicate.mp hb).2
      rw [hbZero]
      exact ordered_matrix_gram_eigenvalues_nonneg A j
  rw [← (Matrix.isHermitian_conjTranspose_mul_self A).sort_roots_charpoly_eq_eigenvalues₀,
    row_column_gram_real_roots A hCard]
  change ((List.ofFn L.eigenvalues₀ ++
    List.replicate (Fintype.card τ - Fintype.card ι) 0 : List ℝ) : Multiset ℝ).sort (· ≥ ·) = _
  rw [Multiset.coe_sort, List.mergeSort_eq_self _ hSorted]

theorem row_column_gram_ordered_eigenvalues_eq (A : Matrix ι τ ℂ)
    (hCard : Fintype.card ι ≤ Fintype.card τ)
    (i : Fin (Fintype.card ι)) (j : Fin (Fintype.card τ)) (hIndex : i.val = j.val) :
    (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ i =
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ j := by
  have hList := row_column_gram_ordered_eigenvalue_list A hCard
  have hEntry := congrArg (fun l : List ℝ => l[i.val]?) hList
  dsimp only at hEntry
  have hVal : (⟨i.val, by omega⟩ : Fin (Fintype.card τ)) = j := Fin.ext hIndex
  have hLeft : i.val < (List.ofFn (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀).length := by
    simpa only [List.length_ofFn] using i.isLt
  rw [List.getElem?_append_left hLeft] at hEntry
  simp only [List.getElem?_ofFn, dif_pos i.isLt, dif_pos (i.isLt.trans_le hCard),
    hVal, Option.some.injEq] at hEntry
  exact hEntry.symm

theorem ordered_matrix_singular_values_conjTranspose (A : Matrix ι τ ℂ)
    (i : Fin (Fintype.card ι)) (j : Fin (Fintype.card τ)) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues A i = orderedMatrixSingularValues A.conjTranspose j := by
  apply congrArg Real.sqrt
  simp only [Matrix.conjTranspose_conjTranspose]
  change (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ i =
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ j
  by_cases hCard : Fintype.card ι ≤ Fintype.card τ
  · exact row_column_gram_ordered_eigenvalues_eq A hCard i j hIndex
  · have h := row_column_gram_ordered_eigenvalues_eq A.conjTranspose (le_of_not_ge hCard) j i hIndex.symm
    simpa only [Matrix.conjTranspose_conjTranspose] using h.symm

end CircularLaw
