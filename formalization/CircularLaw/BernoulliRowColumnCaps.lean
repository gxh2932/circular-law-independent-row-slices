import CircularLaw.BernoulliDiscrepancyUnion

/-!
# Simultaneous row and column caps for the actual Bernoulli matrix

Both coordinate directions have mean degree d. Their literal product-law
tails give a joint cap of 9d outside probability 2n exp(-9d).
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_subset_count_nine_mean_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) {D : ℝ}
    (hMean : (S.card : ℝ) * p = D) :
    (bernoulliCubeLaw ι p hp).real {x | 9 * D ≤ bernoulliSubsetCount S x} ≤
      Real.exp (-9 * D) := by
  have hD : 0 ≤ D := by rw [← hMean]; positivity
  apply (bernoulli_subset_count_upper_tail p hp S (by norm_num : (0 : ℝ) ≤ 2)
    (9 * D)).trans
  rw [hMean]
  apply Real.exp_le_exp.mpr
  have hExp := mul_le_mul_of_nonneg_right real_exp_two_lt_nine.le hD
  nlinarith only [hExp, hD]

theorem bernoulli_square_row_sum_eq_count {n : ℕ} (sample : BernoulliSquareSample n)
    (i : Fin n) :
    (∑ j, bernoulliSquareMatrixReal sample i j) =
      bernoulliSubsetCount (({i} : Finset (Fin n)).product Finset.univ) sample := by
  rw [← bernoulli_square_matrix_real_edge_count]
  simp [matrixEdgeCount]

theorem bernoulli_square_column_sum_eq_count {n : ℕ} (sample : BernoulliSquareSample n)
    (j : Fin n) :
    (∑ i, bernoulliSquareMatrixReal sample i j) =
      bernoulliSubsetCount ((Finset.univ : Finset (Fin n)).product {j}) sample := by
  rw [← bernoulli_square_matrix_real_edge_count]
  simp [matrixEdgeCount]

theorem sparse_bernoulli_row_sum_nine_tail {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (i : Fin n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      9 * (d : ℝ) ≤ ∑ j, bernoulliSquareMatrixReal sample i j} ≤ Real.exp (-9 * d) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  simp_rw [bernoulli_square_row_sum_eq_count]
  apply bernoulli_subset_count_nine_mean_tail
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, one_mul, rowBernoulliParameter_coe]
  field_simp

theorem sparse_bernoulli_column_sum_nine_tail {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (j : Fin n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      9 * (d : ℝ) ≤ ∑ i, bernoulliSquareMatrixReal sample i j} ≤ Real.exp (-9 * d) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  simp_rw [bernoulli_square_column_sum_eq_count]
  apply bernoulli_subset_count_nine_mean_tail
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, mul_one, rowBernoulliParameter_coe]
  field_simp

theorem sparse_bernoulli_row_column_cap_failure {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬MatrixRowColumnBound (9 * d) (bernoulliSquareMatrixReal sample)} ≤
        2 * (n : ℝ) * Real.exp (-9 * d) := by
  let μ := sparseBernoulliMatrixLaw n d
  let R := fun i : Fin n => {sample : BernoulliSquareSample n |
    9 * (d : ℝ) ≤ ∑ j, bernoulliSquareMatrixReal sample i j}
  let C := fun j : Fin n => {sample : BernoulliSquareSample n |
    9 * (d : ℝ) ≤ ∑ i, bernoulliSquareMatrixReal sample i j}
  have hCover : {sample : BernoulliSquareSample n |
      ¬MatrixRowColumnBound (9 * d) (bernoulliSquareMatrixReal sample)} ⊆
        (⋃ i, R i) ∪ (⋃ j, C j) := by
    intro sample hFail
    simp only [Set.mem_setOf_eq] at hFail
    unfold MatrixRowColumnBound at hFail
    rw [not_and_or] at hFail
    rcases hFail with hRow | hColumn
    · obtain ⟨i, hi⟩ := not_forall.mp hRow
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, (lt_of_not_ge hi).le⟩)
    · obtain ⟨j, hj⟩ := not_forall.mp hColumn
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, (lt_of_not_ge hj).le⟩)
  apply (measureReal_mono (μ := μ) hCover (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (measureReal_iUnion_fintype_le R) (measureReal_iUnion_fintype_le C)).trans
  have hRows := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sparse_bernoulli_row_sum_nine_tail hn hdn i)
  have hColumns := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => sparse_bernoulli_column_sum_nine_tail hn hdn j)
  apply (add_le_add hRows hColumns).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def BernoulliDegreeDiscrepancy {n : ℕ} (d : ℕ) (beta : ℝ)
    (sample : BernoulliSquareSample n) : Prop :=
  MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (bernoulliSquareMatrixReal sample) ∧
    MatrixRowColumnBound (9 * d) (bernoulliSquareMatrixReal sample)

theorem bernoulli_degree_discrepancy_failure_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) {beta : ℝ} (hBeta : 0 ≤ beta) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliDegreeDiscrepancy d beta sample} ≤
      (n : ℝ) ^ (-beta) + 2 * n * Real.exp (-9 * d) := by
  have hCover : {sample : BernoulliSquareSample n | ¬BernoulliDegreeDiscrepancy d beta sample} ⊆
      {sample | ¬MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4))
        (bernoulliSquareMatrixReal sample)} ∪
      {sample | ¬MatrixRowColumnBound (9 * d) (bernoulliSquareMatrixReal sample)} := by
    intro sample hFail
    exact not_and_or.mp hFail
  apply (measureReal_mono hCover (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (bernoulli_matrix_discrepancy_failure_probability hn hd hdn hBeta)
    (sparse_bernoulli_row_column_cap_failure hn hdn)

end CircularLaw
