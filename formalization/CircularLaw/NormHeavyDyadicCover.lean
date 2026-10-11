import CircularLaw.NormDyadicMass
import CircularLaw.LightCoupleBounds

/-!
# Complete dyadic cover of the actual heavy bilinear sum

The complement of the light coefficients is bounded by the actual
nonnegative edge counts of the coordinate-level fibers. A heavy pair
forces its level product above the threshold. The cover includes level
zero and uses exact finite regrouping rather than an assumed partition.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def heavyMatrixWeights {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) (K : ℝ) : ι → Fin n → ℝ :=
  fun i j => if K < |Q i j| then Q i j else 0

theorem matrixWeights_light_add_heavy {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) (K : ℝ)
    (i : ι) (j : Fin n) : lightMatrixWeights Q K i j + heavyMatrixWeights Q K i j = Q i j := by
  by_cases h : |Q i j| ≤ K
  · simp only [lightMatrixWeights, heavyMatrixWeights, if_pos h, if_neg (not_lt.mpr h), add_zero]
  · simp only [lightMatrixWeights, heavyMatrixWeights, if_neg h, if_pos (lt_of_not_ge h), zero_add]

theorem heavyMatrixWeights_abs {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) (K : ℝ)
    (i : ι) (j : Fin n) :
    |heavyMatrixWeights Q K i j| = if K < |Q i j| then |Q i j| else 0 := by
  unfold heavyMatrixWeights
  split_ifs <;> simp only [abs_zero]

theorem normCoordinatePart_double_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (x : ι → ℝ) (y : κ → ℝ) (f : ι → κ → ℝ) :
    (∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
      ∑ i ∈ normCoordinatePart n x k, ∑ j ∈ normCoordinatePart n y l, f i j) =
      ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ k ∈ normCoordinateLevels n x, ∑ i ∈ normCoordinatePart n x k,
        ∑ l ∈ normCoordinateLevels n y, ∑ j ∈ normCoordinatePart n y l, f i j := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ k ∈ normCoordinateLevels n x, ∑ i ∈ normCoordinatePart n x k, ∑ j, f i j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact normCoordinatePart_sum n y (f i)
    _ = _ := normCoordinatePart_sum n x (fun i => ∑ j, f i j)

theorem normCoordinatePart_product_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (hn : 0 < n) (x : ι → ℝ) (y : κ → ℝ) {k l : ℕ} {i : ι} {j : κ}
    (hi : i ∈ normCoordinatePart n x k) (hj : j ∈ normCoordinatePart n y l) :
    |x i * y j| ≤ (2 : ℝ) ^ (k + l) / n := by
  have hx := normCoordinatePart_upper hn x hi
  have hy := normCoordinatePart_upper hn y hj
  have hRight : 0 ≤ (2 : ℝ) ^ k / Real.sqrt n := by positivity
  calc
    _ = |x i| * |y j| := abs_mul _ _
    _ ≤ ((2 : ℝ) ^ k / Real.sqrt n) * ((2 : ℝ) ^ l / Real.sqrt n) :=
      mul_le_mul hx hy (abs_nonneg _) hRight
    _ = _ := by
      rw [div_mul_div_comm, ← pow_add, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem normHeavy_pair_level_threshold {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (hn : 0 < n) (N : ℝ) (x : ι → ℝ) (y : κ → ℝ) {k l : ℕ} {i : ι} {j : κ}
    (hi : i ∈ normCoordinatePart n x k) (hj : j ∈ normCoordinatePart n y l)
    (hHeavy : Real.sqrt N / n < |x i * y j|) : Real.sqrt N < (2 : ℝ) ^ (k + l) := by
  have hPair := normCoordinatePart_product_bound hn x y hi hj
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hn : (0 : ℝ) < n)).mp
    (hHeavy.trans_le hPair)

def normHeavyDyadicCost {m n : ℕ} (N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : ℝ :=
  if Real.sqrt N ≤ (2 : ℝ) ^ (k + l) then
    ((2 : ℝ) ^ (k + l) / n) * matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l)
  else 0

theorem normHeavyDyadicCost_nonneg {m n : ℕ} (N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) :
    0 ≤ normHeavyDyadicCost N M x y k l := by
  unfold normHeavyDyadicCost
  split_ifs
  · exact mul_nonneg (by positivity) (matrixEdgeCount_nonneg M hM _ _)
  · exact le_rfl

theorem normHeavy_pair_cost_bound {m n : ℕ} (hn : 0 < n) (N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ} {i : Fin m} {j : Fin n}
    (hi : i ∈ normCoordinatePart n x k) (hj : j ∈ normCoordinatePart n y l) :
    M i j * |heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| ≤
      if Real.sqrt N ≤ (2 : ℝ) ^ (k + l) then ((2 : ℝ) ^ (k + l) / n) * M i j else 0 := by
  rw [heavyMatrixWeights_abs]
  by_cases hHeavy : Real.sqrt N / n < |x i * y j|
  · have hLevel := normHeavy_pair_level_threshold hn N x y hi hj hHeavy
    rw [if_pos hHeavy, if_pos hLevel.le]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (normCoordinatePart_product_bound hn x y hi hj) (hM i j)
  · rw [if_neg hHeavy, mul_zero]
    split_ifs
    · exact mul_nonneg (by positivity) (hM i j)
    · exact le_rfl

theorem normHeavy_level_cost_bound {m n : ℕ} (hn : 0 < n) (N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) :
    (∑ i ∈ normCoordinatePart n x k, ∑ j ∈ normCoordinatePart n y l,
      M i j * |heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j|) ≤
        normHeavyDyadicCost N M x y k l := by
  calc
    _ ≤ ∑ i ∈ normCoordinatePart n x k, ∑ j ∈ normCoordinatePart n y l,
        if Real.sqrt N ≤ (2 : ℝ) ^ (k + l) then ((2 : ℝ) ^ (k + l) / n) * M i j else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact normHeavy_pair_cost_bound hn N M hM x y hi hj
    _ = _ := by
      unfold normHeavyDyadicCost matrixEdgeCount
      by_cases hLevel : Real.sqrt N ≤ (2 : ℝ) ^ (k + l)
      · simp only [if_pos hLevel, Finset.mul_sum]
      · simp only [if_neg hLevel, Finset.sum_const_zero]

theorem normHeavy_bilinear_dyadic_cover {m n : ℕ} (hn : 0 < n) (N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    |∑ i, ∑ j, M i j * heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| ≤
      ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
        normHeavyDyadicCost N M x y k l := by
  calc
    _ ≤ ∑ i, ∑ j, |M i j * heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| :=
      abs_matrix_coefficient_sum_le _
    _ = ∑ i, ∑ j, M i j * |heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hM i j)]
    _ = ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
        ∑ i ∈ normCoordinatePart n x k, ∑ j ∈ normCoordinatePart n y l,
          M i j * |heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| :=
      (normCoordinatePart_double_sum n x y _).symm
    _ ≤ _ := Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ =>
      normHeavy_level_cost_bound hn N M hM x y k l))

end CircularLaw
