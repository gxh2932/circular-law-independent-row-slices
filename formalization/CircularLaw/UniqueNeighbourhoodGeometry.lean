import CircularLaw.UniformBasisSpread

/-!
# Unique-neighbourhood geometry for a shifted rectangular matrix

Rows outside a selected column set contribute a unique nonzero entry.
Rows whose diagonal column lies in the set contribute the scalar shift
when their selected matrix entries are zero. The restricted vector image
is bounded below on both kinds of rows.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def coordinateRestrictedVector {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (S : Finset ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun j => if j ∈ S then v j else 0)

def coordinateMiddleSet {ι : Type*} (S S' : Finset ι) : Finset ι := S' \ S

def diagonalEmbeddedShift {ρ ι : Type*} (A : Matrix ρ ι ℂ)
    (e : ρ ↪ ι) (z : ℂ) : Matrix ρ ι ℂ :=
  fun i j => A i j - if e i = j then z else 0

def matrixUniqueNeighbourhood {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β : ℝ) (S : Finset ι) : Finset ρ :=
  Finset.univ.filter (fun i =>
    (e i ∉ S ∧ ∃ j ∈ S, β ≤ ‖A i j‖ ∧ ∀ k ∈ S, k ≠ j → A i k = 0) ∨
    (e i ∈ S ∧ ∀ j ∈ S, A i j = 0))

theorem coordinate_restricted_vector_apply {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (S : Finset ι) (j : ι) :
    coordinateRestrictedVector v S j = if j ∈ S then v j else 0 := rfl

theorem coordinate_restricted_vector_add_compl {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (S : Finset ι) :
    coordinateRestrictedVector v S + coordinateRestrictedVector v Sᶜ = v := by
  classical
  ext j
  by_cases hj : j ∈ S <;> simp [coordinate_restricted_vector_apply, hj]

theorem matrix_unique_neighbourhood_mem {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β : ℝ) (S : Finset ι) (i : ρ) :
    i ∈ matrixUniqueNeighbourhood A e β S ↔
      (e i ∉ S ∧ ∃ j ∈ S, β ≤ ‖A i j‖ ∧ ∀ k ∈ S, k ≠ j → A i k = 0) ∨
      (e i ∈ S ∧ ∀ j ∈ S, A i j = 0) := by
  simp only [matrixUniqueNeighbourhood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem shifted_restricted_vector_coordinate {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (S : Finset ι) (i : ρ) :
    (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i =
      ∑ j ∈ S, (A i j - if e i = j then z else 0) * v j := by
  classical
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    coordinateRestrictedVector, diagonalEmbeddedShift, WithLp.ofLp_toLp]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  funext j
  by_cases hj : e i = j <;> simp [hj]

theorem shifted_restricted_vector_unique_outside {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (S : Finset ι) (i : ρ) (hOutside : e i ∉ S)
    {j : ι} (hj : j ∈ S) (hUnique : ∀ k ∈ S, k ≠ j → A i k = 0) :
    (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i =
      A i j * v j := by
  rw [shifted_restricted_vector_coordinate]
  have hDiag (k : ι) (hk : k ∈ S) : e i ≠ k := by
    intro hEq
    exact hOutside (hEq ▸ hk)
  rw [Finset.sum_eq_single j]
  · simp only [if_neg (hDiag j hj), sub_zero]
  · intro k hk hkj
    simp only [hUnique k hk hkj, if_neg (hDiag k hk), sub_zero, zero_mul]
  · exact fun hNot => (hNot hj).elim

theorem shifted_restricted_vector_zero_inside {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (S : Finset ι) (i : ρ) (hInside : e i ∈ S)
    (hZero : ∀ j ∈ S, A i j = 0) :
    (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i =
      -z * v (e i) := by
  rw [shifted_restricted_vector_coordinate, Finset.sum_eq_single (e i)]
  · simp only [hZero (e i) hInside, ite_true, zero_sub]
  · intro k hk hki
    simp only [hZero k hk, if_neg (Ne.symm hki), sub_zero, zero_mul]
  · exact fun hNot => (hNot hInside).elim

theorem unique_neighbourhood_restricted_image_lower {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ)
    (v : EuclideanSpace ℂ ι) (S : Finset ι) {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hz : β ≤ ‖z‖) (hHead : ∀ j ∈ S, a ≤ ‖v j‖)
    (i : ρ) (hi : i ∈ matrixUniqueNeighbourhood A e β S) :
    β * a ≤ ‖(diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i‖ := by
  rcases (matrix_unique_neighbourhood_mem A e β S i).mp hi with
    ⟨hOutside, j, hj, hEntry, hUnique⟩ | ⟨hInside, hZero⟩
  · rw [shifted_restricted_vector_unique_outside A e z v S i hOutside hj hUnique, norm_mul]
    exact mul_le_mul hEntry (hHead j hj) ha (hβ.trans hEntry)
  · rw [shifted_restricted_vector_zero_inside A e z v S i hInside hZero, norm_mul, norm_neg]
    exact mul_le_mul hz (hHead (e i) hInside) ha (hβ.trans hz)

end CircularLaw
