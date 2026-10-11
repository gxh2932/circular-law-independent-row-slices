import CircularLaw.UniqueNeighbourhoodGeometry

/-!
# Actual supports and row budgets for a shifted matrix

The rows touched by a middle coordinate set include both nonzero matrix
entries and the embedded diagonal. Their number is bounded by the sum of
the actual column degrees plus the number of middle coordinates.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def matrixColumnSupport {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (j : ι) : Finset ρ :=
  Finset.univ.filter (fun i => A i j ≠ 0)

def embeddedDiagonalPreimage {ρ ι : Type*} [Fintype ρ]
    (e : ρ ↪ ι) (j : ι) : Finset ρ :=
  Finset.univ.filter (fun i => e i = j)

def shiftedMiddleTouchedRows {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (T : Finset ι) : Finset ρ :=
  T.biUnion (fun j => matrixColumnSupport A j ∪ embeddedDiagonalPreimage e j)

def matrixRowL1Mass {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι ℂ) (i : ρ) : ℝ :=
  ∑ j, ‖A i j‖

def matrixHeavyRows {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (L : ℝ) : Finset ρ :=
  Finset.univ.filter (fun i => L < matrixRowL1Mass A i)

theorem matrix_column_support_mem {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (j : ι) (i : ρ) :
    i ∈ matrixColumnSupport A j ↔ A i j ≠ 0 := by
  simp only [matrixColumnSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem embedded_diagonal_preimage_mem {ρ ι : Type*} [Fintype ρ]
    (e : ρ ↪ ι) (j : ι) (i : ρ) :
    i ∈ embeddedDiagonalPreimage e j ↔ e i = j := by
  simp only [embeddedDiagonalPreimage, Finset.mem_filter, Finset.mem_univ, true_and]

theorem embedded_diagonal_preimage_card_le_one {ρ ι : Type*} [Fintype ρ]
    (e : ρ ↪ ι) (j : ι) : (embeddedDiagonalPreimage e j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply e.injective
  exact (embedded_diagonal_preimage_mem e j a).mp ha |>.trans
    ((embedded_diagonal_preimage_mem e j b).mp hb).symm

theorem shifted_middle_touched_rows_mem {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (T : Finset ι) (i : ρ) :
    i ∈ shiftedMiddleTouchedRows A e T ↔
      e i ∈ T ∨ ∃ j ∈ T, A i j ≠ 0 := by
  classical
  simp only [shiftedMiddleTouchedRows, Finset.mem_biUnion, Finset.mem_union,
    matrix_column_support_mem, embedded_diagonal_preimage_mem]
  constructor
  · rintro ⟨j, hj, hA | he⟩
    · exact Or.inr ⟨j, hj, hA⟩
    · exact Or.inl (he.symm ▸ hj)
  · rintro (he | ⟨j, hj, hA⟩)
    · exact ⟨e i, he, Or.inr rfl⟩
    · exact ⟨j, hj, Or.inl hA⟩

theorem shifted_middle_touched_rows_card_le {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (T : Finset ι) :
    (shiftedMiddleTouchedRows A e T).card ≤
      ∑ j ∈ T, ((matrixColumnSupport A j).card + 1) := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro j _
  exact (Finset.card_union_le (s := matrixColumnSupport A j)
    (t := embeddedDiagonalPreimage e j)).trans
    (Nat.add_le_add_left (embedded_diagonal_preimage_card_le_one e j) _)

theorem shifted_middle_untouched_entries {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (T : Finset ι) (i : ρ)
    (hi : i ∉ shiftedMiddleTouchedRows A e T) :
    e i ∉ T ∧ ∀ j ∈ T, A i j = 0 := by
  have hNot := mt (shifted_middle_touched_rows_mem A e T i).mpr hi
  refine ⟨fun h => hNot (Or.inl h), fun j hj => ?_⟩
  by_contra hA
  exact hNot (Or.inr ⟨j, hj, hA⟩)

theorem shifted_middle_restricted_image_zero {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (T : Finset ι) (i : ρ)
    (hi : i ∉ shiftedMiddleTouchedRows A e T) :
    (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v T) i = 0 := by
  obtain ⟨he, hA⟩ := shifted_middle_untouched_entries A e T i hi
  rw [shifted_restricted_vector_coordinate]
  apply Finset.sum_eq_zero
  intro j hj
  have hDiag : e i ≠ j := fun hEq => he (hEq ▸ hj)
  simp only [hA j hj, if_neg hDiag, sub_zero, zero_mul]

theorem matrix_row_l1_mass_nonneg {ρ ι : Type*} [Fintype ι]
    (A : Matrix ρ ι ℂ) (i : ρ) : 0 ≤ matrixRowL1Mass A i :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem matrix_heavy_rows_complement {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (L : ℝ) (i : ρ) (hi : i ∉ matrixHeavyRows A L) :
    matrixRowL1Mass A i ≤ L := by
  simpa only [matrixHeavyRows, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt] using hi

theorem shifted_matrix_row_l1_mass_le {ρ ι : Type*} [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ) (i : ρ) :
    matrixRowL1Mass (diagonalEmbeddedShift A e z) i ≤ matrixRowL1Mass A i + ‖z‖ := by
  classical
  have hPoint (j : ι) : ‖diagonalEmbeddedShift A e z i j‖ ≤
      ‖A i j‖ + if e i = j then ‖z‖ else 0 := by
    by_cases hj : e i = j
    · simpa [diagonalEmbeddedShift, hj] using norm_sub_le (A i j) z
    · simp [diagonalEmbeddedShift, hj]
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hPoint j)
  simpa only [matrixRowL1Mass, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using hSum

theorem shifted_restricted_image_norm_le {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (T : Finset ι) {b : ℝ} (hb : 0 ≤ b)
    (hTail : ∀ j ∈ T, ‖v j‖ ≤ b) (i : ρ) :
    ‖(diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v T) i‖ ≤
      (matrixRowL1Mass A i + ‖z‖) * b := by
  rw [shifted_restricted_vector_coordinate]
  calc
    ‖∑ j ∈ T, (A i j - if e i = j then z else 0) * v j‖ ≤
        ∑ j ∈ T, ‖(A i j - if e i = j then z else 0) * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ T, ‖diagonalEmbeddedShift A e z i j‖ * b := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      have hMul := mul_le_mul_of_nonneg_left (hTail j hj)
        (norm_nonneg (diagonalEmbeddedShift A e z i j))
      by_cases hjEq : e i = j <;> simpa [diagonalEmbeddedShift, hjEq] using hMul
    _ = (∑ j ∈ T, ‖diagonalEmbeddedShift A e z i j‖) * b := by
      rw [Finset.sum_mul]
    _ ≤ (matrixRowL1Mass A i + ‖z‖) * b := by
      apply mul_le_mul_of_nonneg_right _ hb
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun j _ _ => norm_nonneg (diagonalEmbeddedShift A e z i j))).trans
        (shifted_matrix_row_l1_mass_le A e z i)

end CircularLaw
