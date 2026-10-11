import CircularLaw.NormHeavySquare

/-!
# Literal zero-row padding for the rectangular norm argument

Padding embeds the original row coordinates into the ambient column
dimension. The source row preimage, all finite sums, squared vector
mass and row/column caps are checked exactly.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normPadVector {m n : ℕ} (x : Fin m → ℝ) : Fin n → ℝ :=
  fun i => if hi : i.val < m then x ⟨i.val, hi⟩ else 0

def normPadMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => normPadVector (fun r => M r j) i

def normPadActiveRows {m n : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Fin.castLE hm i ∈ S)

theorem normPadVector_cast {m n : ℕ} (hm : m ≤ n) (x : Fin m → ℝ) (i : Fin m) :
    normPadVector x (Fin.castLE hm i) = x i := by
  unfold normPadVector
  simp only [Fin.val_castLE, dif_pos i.isLt]

theorem normPadVector_outside {m n : ℕ} (x : Fin m → ℝ) (i : Fin n) (hi : ¬ i.val < m) :
    normPadVector x i = 0 := by
  unfold normPadVector
  rw [dif_neg hi]

theorem mem_normPadActiveRows {m n : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) (i : Fin m) :
    i ∈ normPadActiveRows hm S ↔ Fin.castLE hm i ∈ S := by
  simp only [normPadActiveRows, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normPadActiveRows_card_le {m n : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) :
    (normPadActiveRows hm S).card ≤ S.card := by
  exact Finset.card_le_card_of_injOn (Fin.castLE hm)
    (fun i hi => (mem_normPadActiveRows hm S i).mp hi) (Fin.castLE_injective hm).injOn

theorem normPadActiveRows_map_subset {m n : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) :
    (normPadActiveRows hm S).map (Fin.castLEEmb hm) ⊆ S := by
  intro i hi
  obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hi
  exact (mem_normPadActiveRows hm S r).mp hr

theorem normPadVector_sum_on {m n : ℕ} (hm : m ≤ n) (x : Fin m → ℝ) (S : Finset (Fin n)) :
    (∑ i ∈ S, normPadVector x i) = ∑ r ∈ normPadActiveRows hm S, x r := by
  have hSubset := normPadActiveRows_map_subset hm S
  have hZero : ∀ i ∈ S, i ∉ (normPadActiveRows hm S).map (Fin.castLEEmb hm) → normPadVector x i = 0 := by
    intro i hi hOutside
    apply normPadVector_outside
    intro hSmall
    let r : Fin m := ⟨i.val, hSmall⟩
    have hCast : Fin.castLE hm r = i := by apply Fin.ext; rfl
    apply hOutside
    apply Finset.mem_map.mpr
    exact ⟨r, (mem_normPadActiveRows hm S r).mpr (by rw [hCast]; exact hi), hCast⟩
  calc
    _ = ∑ i ∈ (normPadActiveRows hm S).map (Fin.castLEEmb hm), normPadVector x i :=
      (Finset.sum_subset hSubset hZero).symm
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro r _
      exact normPadVector_cast hm x r

theorem normPadVector_sum {m n : ℕ} (hm : m ≤ n) (x : Fin m → ℝ) :
    (∑ i : Fin n, normPadVector x i) = ∑ r : Fin m, x r := by
  have hActive : normPadActiveRows hm (Finset.univ : Finset (Fin n)) = Finset.univ := by
    ext r
    simp only [mem_normPadActiveRows, Finset.mem_univ]
  rw [normPadVector_sum_on hm x, hActive]

theorem normPadVector_square {m n : ℕ} (x : Fin m → ℝ) (i : Fin n) :
    (normPadVector x i) ^ 2 = normPadVector (fun r => (x r) ^ 2) i := by
  unfold normPadVector
  split_ifs <;> simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem normPadVector_squared_sum {m n : ℕ} (hm : m ≤ n) (x : Fin m → ℝ) :
    (∑ i : Fin n, (normPadVector x i) ^ 2) = ∑ r : Fin m, (x r) ^ 2 := by
  simp_rw [normPadVector_square]
  exact normPadVector_sum hm (fun r => (x r) ^ 2)

theorem normPadMatrix_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ i j, 0 ≤ normPadMatrix M i j := by
  intro i j
  unfold normPadMatrix normPadVector
  split_ifs
  · exact hM _ _
  · exact le_rfl

theorem normPadMatrix_row_sum {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (T : Finset (Fin n)) (i : Fin n) :
    (∑ j ∈ T, normPadMatrix M i j) = normPadVector (fun r => ∑ j ∈ T, M r j) i := by
  unfold normPadMatrix normPadVector
  by_cases hi : i.val < m
  · simp only [dif_pos hi]
  · simp only [dif_neg hi, Finset.sum_const_zero]

theorem normPadMatrix_edgeCount {m n : ℕ} (hm : m ≤ n) (M : Matrix (Fin m) (Fin n) ℝ)
    (S T : Finset (Fin n)) :
    matrixEdgeCount (normPadMatrix M) S T = matrixEdgeCount M (normPadActiveRows hm S) T := by
  unfold matrixEdgeCount
  simp_rw [normPadMatrix_row_sum]
  exact normPadVector_sum_on hm (fun r => ∑ j ∈ T, M r j) S

theorem normPadMatrix_column_sum {m n : ℕ} (hm : m ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (∑ i : Fin n, normPadMatrix M i j) = ∑ r : Fin m, M r j :=
  normPadVector_sum hm (fun r => M r j)

theorem normPadMatrix_rowColumnBound {m n : ℕ} (hm : m ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (M : Matrix (Fin m) (Fin n) ℝ) (hBound : MatrixRowColumnBound B M) :
    MatrixRowColumnBound B (normPadMatrix M) := by
  constructor
  · intro i
    rw [normPadMatrix_row_sum]
    unfold normPadVector
    split_ifs
    · exact hBound.1 _
    · exact hB
  · intro j
    rw [normPadMatrix_column_sum hm M j]
    exact hBound.2 j

end CircularLaw
