import CircularLaw.NormHeavyCaseAssembly

/-!
# Full heavy bilinear bound for square matrices

The matrix and its literal transpose cover both orderings of the
coordinate-fiber sizes. The checked five-case budgets therefore bound
every heavy pair. The resulting constant is independent of dimension;
it is our own constant for the complete base-zero coordinate partition.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normHeavyBudget (C cap kappa₂ : ℝ) : ℝ :=
  25 * cap + 10 / C + 40 * kappa₂ / C + 80 * kappa₂ / (C * cap * Real.log cap) + 10

def normHeavySquareConstant (C cap kappa₂ : ℝ) : ℝ := 2 * C * normHeavyBudget C cap kappa₂

def normHeavyOrientedCost {m n : ℕ} (N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : ℝ :=
  if normHeavyOrientedPair n N x y k l then normHeavyDyadicCost N M x y k l else 0

theorem matrixEdgeCount_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (T : Finset (Fin m)) :
    matrixEdgeCount M.transpose S T = matrixEdgeCount M T S := by
  unfold matrixEdgeCount
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem matrixDiscrepancy_square_transpose {n : ℕ} {density cap kappa₂ : ℝ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hDP : MatrixDiscrepancy density cap kappa₂ M) :
    MatrixDiscrepancy density cap kappa₂ M.transpose := by
  intro S T hS hT
  have h := hDP T S hT hS
  simpa only [matrixEdgeCount_transpose, mul_comm, max_comm] using h

theorem matrixRowColumnBound_transpose {m n : ℕ} {B : ℝ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hBound : MatrixRowColumnBound B M) : MatrixRowColumnBound B M.transpose := by
  constructor
  · intro j
    simpa only [Matrix.transpose_apply] using hBound.2 j
  · intro i
    simpa only [Matrix.transpose_apply] using hBound.1 i

theorem normHeavyOrientedCost_nonneg {m n : ℕ} (N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) :
    0 ≤ normHeavyOrientedCost N M x y k l := by
  unfold normHeavyOrientedCost
  split_ifs
  · exact normHeavyDyadicCost_nonneg N M hM x y k l
  · exact le_rfl

theorem normHeavyDyadicCost_square_transpose {n : ℕ} (N : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) (k l : ℕ) :
    normHeavyDyadicCost N M.transpose y x l k = normHeavyDyadicCost N M x y k l := by
  unfold normHeavyDyadicCost
  rw [Nat.add_comm l k, matrixEdgeCount_transpose]

theorem normHeavyDyadicCost_square_order_cover {n : ℕ} (N : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x y : Fin n → ℝ) (k l : ℕ) :
    normHeavyDyadicCost N M x y k l ≤
      normHeavyOrientedCost N M x y k l + normHeavyOrientedCost N M.transpose y x l k := by
  have hMT : ∀ i j, 0 ≤ M.transpose i j := fun i j => hM j i
  by_cases hHeavy : Real.sqrt N ≤ (2 : ℝ) ^ (k + l)
  · by_cases hSizes : (normCoordinatePart n y l).card ≤ (normCoordinatePart n x k).card
    · have hLeft : normHeavyOrientedCost N M x y k l = normHeavyDyadicCost N M x y k l := by
        unfold normHeavyOrientedCost
        rw [if_pos (show normHeavyOrientedPair n N x y k l from ⟨hHeavy, hSizes⟩)]
      rw [hLeft]
      exact le_add_of_nonneg_right (normHeavyOrientedCost_nonneg N M.transpose hMT y x l k)
    · have hReverse : normHeavyOrientedPair n N y x l k :=
        ⟨by simpa only [Nat.add_comm] using hHeavy, (lt_of_not_ge hSizes).le⟩
      have hRight : normHeavyOrientedCost N M.transpose y x l k = normHeavyDyadicCost N M x y k l := by
        unfold normHeavyOrientedCost
        rw [if_pos hReverse, normHeavyDyadicCost_square_transpose]
      rw [hRight]
      exact le_add_of_nonneg_left (normHeavyOrientedCost_nonneg N M hM x y k l)
  · have hZero : normHeavyDyadicCost N M x y k l = 0 := by
      unfold normHeavyDyadicCost
      rw [if_neg hHeavy]
    rw [hZero]
    exact add_nonneg (normHeavyOrientedCost_nonneg N M hM x y k l)
      (normHeavyOrientedCost_nonneg N M.transpose hMT y x l k)

theorem normHeavy_oriented_cost_normalization {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    normHeavyOrientedCost N M x y k l = C * Real.sqrt N *
      (if normHeavyOrientedPair n N x y k l then normHeavyLevelWeight C N M x y k l else 0) := by
  unfold normHeavyOrientedCost
  by_cases hO : normHeavyOrientedPair n N x y k l
  · rw [if_pos hO, if_pos hO]
    unfold normHeavyDyadicCost
    rw [if_pos hO.1]
    exact normHeavy_level_normalization hn hC hN M x y hk hl
  · rw [if_neg hO, if_neg hO, mul_zero]

theorem normHeavy_oriented_cost_sum_bound {m n : ℕ} (hn : 0 < n) (hm : m ≤ n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hColumn : ∀ j, (∑ i, M i j) ≤ N) (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1) :
    (∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y, normHeavyOrientedCost N M x y k l) ≤
      C * Real.sqrt N * normHeavyBudget C cap kappa₂ := by
  have hBudget := normHeavy_oriented_sum_bound hn hm hC hN hCap hKappa M hM hColumn hDP x y hx hy
  calc
    _ = ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y, C * Real.sqrt N *
        (if normHeavyOrientedPair n N x y k l then normHeavyLevelWeight C N M x y k l else 0) :=
      Finset.sum_congr rfl (fun _ hk => Finset.sum_congr rfl (fun _ hl =>
        normHeavy_oriented_cost_normalization hn hC hN M x y hk hl))
    _ = C * Real.sqrt N * normHeavySelectedSum C N M x y (normHeavyOrientedPair n N x y) := by
      unfold normHeavySelectedSum
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hBudget (by positivity)

theorem normHeavy_square_level_sum_bound {n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hBound : MatrixRowColumnBound N M) (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1) :
    (∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y, normHeavyDyadicCost N M x y k l) ≤
      normHeavySquareConstant C cap kappa₂ * Real.sqrt N := by
  have hMT : ∀ i j, 0 ≤ M.transpose i j := fun i j => hM j i
  have hOriginal := normHeavy_oriented_cost_sum_bound hn le_rfl hC hN hCap hKappa M hM hBound.2 hDP x y hx hy
  have hTransposed := normHeavy_oriented_cost_sum_bound hn le_rfl hC hN hCap hKappa M.transpose hMT
    (matrixRowColumnBound_transpose M hBound).2 (matrixDiscrepancy_square_transpose M hDP) y x hy hx
  calc
    _ ≤ ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
        (normHeavyOrientedCost N M x y k l + normHeavyOrientedCost N M.transpose y x l k) :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => normHeavyDyadicCost_square_order_cover N M hM x y k l))
    _ = (∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y, normHeavyOrientedCost N M x y k l) +
        ∑ l ∈ normCoordinateLevels n y, ∑ k ∈ normCoordinateLevels n x, normHeavyOrientedCost N M.transpose y x l k := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ C * Real.sqrt N * normHeavyBudget C cap kappa₂ + C * Real.sqrt N * normHeavyBudget C cap kappa₂ :=
      add_le_add hOriginal hTransposed
    _ = _ := by unfold normHeavySquareConstant; ring

theorem normHeavy_square_bilinear_bound {n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hBound : MatrixRowColumnBound N M) (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1) :
    |∑ i, ∑ j, M i j * heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| ≤
      normHeavySquareConstant C cap kappa₂ * Real.sqrt N :=
  (normHeavy_bilinear_dyadic_cover hn N M hM x y).trans
    (normHeavy_square_level_sum_bound hn hC hN hCap hKappa M hM hBound hDP x y hx hy)

end CircularLaw
