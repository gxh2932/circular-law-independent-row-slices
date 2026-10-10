import CircularLaw.SourceGraphGap

/-!
# Heavy rows from the column-degree budget

For matrices with entry norms at most one, the uniform column-degree
budget bounds the total row mass. The source fifth-power threshold then
gives the actual heavy-row budget when the degree is sufficiently large.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem matrix_total_row_mass_le_column_supports {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (A : Matrix ρ ι ℂ)
    (hNorm : ∀ i j, ‖A i j‖ ≤ 1) :
    (∑ i, matrixRowL1Mass A i) ≤ ∑ j, ((matrixColumnSupport A j).card : ℝ) := by
  simp only [matrixRowL1Mass]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  simp only [matrixColumnSupport, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hEntry : A i j = 0
  · simp [hEntry]
  · simpa only [if_pos hEntry, Nat.cast_one] using hNorm i j

theorem matrix_column_degree_total_row_mass_le {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (A : Matrix ρ ι ℂ) {K n d : ℝ}
    (hK : 0 ≤ K) (hn : 0 < n) (hd : 1 ≤ d)
    (hCols : (Fintype.card ι : ℝ) ≤ n) (hNorm : ∀ i j, ‖A i j‖ ≤ 1)
    (hA : MatrixColumnDegreeBudget A K n d) :
    (∑ i, matrixRowL1Mass A i) ≤ K * n * d := by
  let m : ℝ := Fintype.card ι
  have hDegree : (∑ j, ((matrixColumnSupport A j).card : ℝ)) ≤
      K * m * (d + Real.log (n / m)) := by
    simpa only [Finset.card_univ] using hA Finset.univ
  apply (matrix_total_row_mass_le_column_supports A hNorm).trans (hDegree.trans ?_)
  by_cases hm : m = 0
  · rw [hm]
    simp only [mul_zero, zero_mul]
    positivity
  have hmPos : 0 < m := lt_of_le_of_ne (by dsimp [m]; positivity) (Ne.symm hm)
  have hMono := logarithmic_degree_budget_mono hn (sub_nonneg.mpr hd) hmPos hn hCols
    (by simp only [div_self hn.ne', Real.log_one]; rfl)
  have hScalar : m * (d + Real.log (n / m)) ≤ n * d := by
    rw [div_self hn.ne', Real.log_one] at hMono
    linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hScalar hK

theorem matrix_heavy_rows_threshold_mass_le {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (A : Matrix ρ ι ℂ) (L : ℝ) :
    ((matrixHeavyRows A L).card : ℝ) * L ≤ ∑ i, matrixRowL1Mass A i := by
  calc
    _ = ∑ i ∈ matrixHeavyRows A L, L := by simp
    _ ≤ ∑ i ∈ matrixHeavyRows A L, matrixRowL1Mass A i := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((Finset.mem_filter.mp hi).2).le
    _ ≤ ∑ i, matrixRowL1Mass A i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => matrix_row_l1_mass_nonneg A i)

theorem source_heavy_threshold_log_budget {K d x β : ℝ}
    (hK : 0 ≤ K) (hd : 1 ≤ d) (hDegree : 4 * K ≤ d)
    (hx : 1 ≤ x) (hβ : 0 < β) (hβOne : β ≤ 1) :
    4 * K * x * Real.log x ^ 2 ≤ (d * x / β) ^ 5 / β := by
  have hxPos : 0 < x := by linarith
  have hdPos : 0 < d := by linarith
  have hLog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxPos).trans (by linarith)
  have hSquare := pow_le_pow_left₀ (Real.log_nonneg hx) hLog 2
  have hDiv : d * x ≤ d * x / β := by
    apply (le_div_iff₀ hβ).mpr
    exact mul_le_of_le_one_right (mul_nonneg hdPos.le hxPos.le) hβOne
  calc
    _ ≤ 4 * K * x * x ^ 2 := mul_le_mul_of_nonneg_left hSquare (by positivity)
    _ = 4 * K * x ^ 3 := by ring
    _ ≤ d * x ^ 3 := mul_le_mul_of_nonneg_right hDegree (by positivity)
    _ ≤ d ^ 5 * x ^ 5 := mul_le_mul (le_self_pow₀ hd (by norm_num : (5 : ℕ) ≠ 0))
      (pow_le_pow_right₀ hx (by norm_num : (3 : ℕ) ≤ 5)) (by positivity) (by positivity)
    _ = (d * x) ^ 5 := by ring
    _ ≤ (d * x / β) ^ 5 := pow_le_pow_left₀ (by positivity) hDiv 5
    _ ≤ _ := by
      apply (le_div_iff₀ hβ).mpr
      exact mul_le_of_le_one_right (by positivity) hβOne

theorem matrix_heavy_row_budget_of_column_degree {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] (A : Matrix ρ ι ℂ) {K n d β : ℝ}
    (hK : 0 ≤ K) (hn : 0 < n) (hd : 1 ≤ d) (hDegree : 4 * K ≤ d)
    (hCols : (Fintype.card ι : ℝ) ≤ n) (hNorm : ∀ i j, ‖A i j‖ ≤ 1)
    (hβ : 0 < β) (hβOne : β ≤ 1) (hA : MatrixColumnDegreeBudget A K n d) :
    MatrixHeavyRowBudget A β n d := by
  intro ell hell hLog
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hdPos : 0 < d := by linarith
  have hx : 1 ≤ n / ell := by
    have hLogBound := Real.log_le_sub_one_of_pos (div_pos hn he)
    linarith
  let L := (d * n / (β * ell)) ^ 5 / β
  have hL : 0 < L := by dsimp [L]; positivity
  have hThreshold : 4 * K * (n / ell) * Real.log (n / ell) ^ 2 ≤ L := by
    have h := source_heavy_threshold_log_budget hK hd hDegree hx hβ hβOne
    have hEq : d * (n / ell) / β = d * n / (β * ell) := by ring
    simpa only [hEq] using h
  have hTotal := matrix_column_degree_total_row_mass_le A hK hn hd hCols hNorm hA
  have hMass := (matrix_heavy_rows_threshold_mass_le A L).trans hTotal
  have hScale : 4 * (K * n * d) * Real.log (n / ell) ^ 2 ≤ d * ell * L := by
    have h := mul_le_mul_of_nonneg_left hThreshold (mul_nonneg hdPos.le he.le)
    have hEq : (d * ell) * (4 * K * (n / ell) * Real.log (n / ell) ^ 2) =
        4 * (K * n * d) * Real.log (n / ell) ^ 2 := by field_simp
    rwa [hEq] at h
  change ((matrixHeavyRows A L).card : ℝ) ≤ (d * ell / Real.log (n / ell) ^ 2) / 4
  rw [div_div]
  apply (le_div_iff₀ (by positivity : 0 < Real.log (n / ell) ^ 2 * 4)).mpr
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    _ = (((matrixHeavyRows A L).card : ℝ) * L) * (Real.log (n / ell) ^ 2 * 4) := by ring
    _ ≤ (K * n * d) * (Real.log (n / ell) ^ 2 * 4) :=
      mul_le_mul_of_nonneg_right hMass (by positivity)
    _ ≤ _ := by nlinarith [hScale]

end CircularLaw
