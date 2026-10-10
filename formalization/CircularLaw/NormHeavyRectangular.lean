import CircularLaw.NormPaddingDiscrepancy

/-!
# Full rectangular heavy bilinear estimate

Literal zero-row padding preserves the original heavy bilinear sum,
squared vector mass, degree caps and discrepancy alternatives. Applying
the checked square estimate therefore gives the same dimension-independent
constant for every rectangular matrix with at most as many rows as columns.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem normPadMatrix_heavy_bilinear {m n : ℕ} (hm : m ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) (K : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, normPadMatrix M i j *
      heavyMatrixWeights (fun i j => normPadVector x i * y j) K i j) =
      ∑ r : Fin m, ∑ j : Fin n, M r j * heavyMatrixWeights (fun r j => x r * y j) K r j := by
  calc
    _ = ∑ i : Fin n, normPadVector
        (fun r => ∑ j : Fin n, M r j * heavyMatrixWeights (fun r j => x r * y j) K r j) i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold normPadMatrix normPadVector heavyMatrixWeights
      by_cases hi : i.val < m
      · simp only [dif_pos hi]
      · simp only [dif_neg hi, zero_mul, Finset.sum_const_zero]
    _ = _ := normPadVector_sum hm _

theorem normHeavy_rectangular_bilinear_bound {m n : ℕ} (hn : 0 < n) (hm : m ≤ n)
    {C N cap kappa₂ : ℝ} (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hBound : MatrixRowColumnBound N M) (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1) :
    |∑ i, ∑ j, M i j * heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n) i j| ≤
      normHeavySquareConstant C cap kappa₂ * Real.sqrt N := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hDensity : 0 < C * N / n := div_pos (mul_pos hC hN) hnReal
  have hCapNonneg : 0 ≤ cap := (lt_trans (by norm_num : (0 : ℝ) < 1) hCap).le
  have hPadDP := normPadMatrix_discrepancy hm hDensity hCapNonneg hKappa M hM hDP
  have hPadBound := normPadMatrix_rowColumnBound hm hN.le M hBound
  have hPadMass : (∑ i : Fin n, (normPadVector x i) ^ 2) ≤ 1 := by
    rw [normPadVector_squared_sum hm x]
    exact hx
  have hSquare := normHeavy_square_bilinear_bound hn hC hN hCap hKappa
    (normPadMatrix M) (normPadMatrix_nonneg M hM) hPadBound hPadDP (normPadVector x) y hPadMass hy
  rw [normPadMatrix_heavy_bilinear hm M x y] at hSquare
  exact hSquare

end CircularLaw
