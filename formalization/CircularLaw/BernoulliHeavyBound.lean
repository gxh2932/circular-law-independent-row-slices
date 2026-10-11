import CircularLaw.BernoulliRowColumnCaps
import CircularLaw.BernoulliLightConcentration
import CircularLaw.RowSliceRealNorm

/-!
# The complete centered Bernoulli heavy estimate

Actual discrepancy and both degree caps supply the deterministic heavy
bound. The omitted coefficient mass controls the centering term without
a zero-sum condition on either vector.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem heavyMatrixWeights_sum_abs_le {ι : Type*} [Fintype ι] {n : ℕ}
    (Q : ι → Fin n → ℝ) {K : ℝ} (hK : 0 < K)
    (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    |∑ i, ∑ j, heavyMatrixWeights Q K i j| ≤ 1 / K := by
  have hPoint (i : ι) (j : Fin n) : heavyMatrixWeights Q K i j = Q i j - lightMatrixWeights Q K i j := by
    have h := matrixWeights_light_add_heavy Q K i j
    linarith only [h]
  simp_rw [hPoint]
  apply (abs_matrix_coefficient_sum_le (fun i j => Q i j - lightMatrixWeights Q K i j)).trans
  calc
    _ ≤ ∑ i, ∑ j, Q i j ^ 2 / K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact omitted_light_weight_abs_le_square_div hK
    _ = (∑ i, ∑ j, Q i j ^ 2) / K := by simp_rw [Finset.sum_div]
    _ ≤ 1 / K := div_le_div_of_nonneg_right hSquare hK.le

theorem bernoulli_heavy_centering_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (Q : Fin n → Fin n → ℝ) (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    |((d : ℝ) / n) * ∑ i, ∑ j, heavyMatrixWeights Q (Real.sqrt (9 * (d : ℝ)) / n) i j| ≤
      Real.sqrt d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt (9 * (d : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hMean : |((d : ℝ) / n) * ∑ i, ∑ j,
      heavyMatrixWeights Q (Real.sqrt (9 * (d : ℝ)) / n) i j| ≤
      (d : ℝ) / Real.sqrt (9 * (d : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)]
    apply (mul_le_mul_of_nonneg_left (heavyMatrixWeights_sum_abs_le Q (div_pos hRoot hnR) hSquare)
      (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)).trans_eq
    field_simp
  apply hMean.trans
  simpa only [rowSliceLightThreshold, zero_mul, add_zero, mul_zero, zero_add, one_mul] using
    rowSliceLightThreshold_le hd (0 : ℝ)

def BernoulliHeavyBound {n : ℕ} (d : ℕ) (beta : ℝ) (sample : BernoulliSquareSample n) : Prop :=
  ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2) ≤ 1 → (∑ j, (y j) ^ 2) ≤ 1 →
    |centeredBernoulliMatrixSum d (heavyMatrixWeights (fun i j => x i * y j)
      (Real.sqrt (9 * (d : ℝ)) / n)) sample| ≤
        (1 + rowSliceHeavyConstant beta) * Real.sqrt d

theorem bernoulli_degree_discrepancy_heavy_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {beta : ℝ} (hBeta : 0 ≤ beta) (sample : BernoulliSquareSample n)
    (hGood : BernoulliDegreeDiscrepancy d beta sample) : BernoulliHeavyBound d beta sample := by
  intro x y hx hy
  have hN : 0 < 9 * (d : ℝ) := by positivity
  have hCap : 1 < Real.exp (2 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hKappa : 0 ≤ 2 * (beta + 4) := by linarith only [hBeta]
  have hDensity : ((1 / 9 : ℝ) * (9 * (d : ℝ))) / n = (d : ℝ) / n := by ring
  have hDP : MatrixDiscrepancy (((1 / 9 : ℝ) * (9 * (d : ℝ))) / n)
      (Real.exp 2) (2 * (beta + 4)) (bernoulliSquareMatrixReal sample) := by
    rw [hDensity]
    exact hGood.1
  have hHeavy := normHeavy_square_bilinear_bound hn (by norm_num : (0 : ℝ) < 1 / 9)
    hN hCap hKappa (bernoulliSquareMatrixReal sample) (bernoulli_square_matrix_real_nonneg sample)
    hGood.2 hDP x y hx hy
  have hRoot : Real.sqrt (9 * (d : ℝ)) = 3 * Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
    norm_num
  have hRaw : |∑ i, ∑ j, bernoulliSquareMatrixReal sample i j *
      heavyMatrixWeights (fun i j => x i * y j) (Real.sqrt (9 * (d : ℝ)) / n) i j| ≤
      rowSliceHeavyConstant beta * Real.sqrt d := by
    convert hHeavy using 1
    rw [hRoot]
    unfold rowSliceHeavyConstant
    ring
  have hMass : (∑ i, ∑ j, (x i * y j) ^ 2) ≤ 1 := by
    rw [rankOneWeights_squared_sum]
    have hyNonneg : 0 ≤ ∑ j, (y j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa only [one_mul] using mul_le_mul hx hy hyNonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hMean := bernoulli_heavy_centering_bound hn hd (fun i j => x i * y j) hMass
  have hIdentity (Q : Fin n → Fin n → ℝ) : centeredBernoulliMatrixSum d Q sample =
      (∑ i, ∑ j, bernoulliSquareMatrixReal sample i j * Q i j) - ((d : ℝ) / n) * ∑ i, ∑ j, Q i j := by
    simp only [centeredBernoulliMatrixSum, centeredBernoulliMatrixReal, sub_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hIdentity]
  apply (abs_sub _ _).trans
  apply (add_le_add hRaw hMean).trans_eq
  ring

theorem bernoulli_heavy_bound_failure_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) {beta : ℝ} (hBeta : 0 ≤ beta) :
    (sparseBernoulliMatrixLaw n d).real {sample | ¬BernoulliHeavyBound d beta sample} ≤
      (n : ℝ) ^ (-beta) + 2 * n * Real.exp (-9 * d) := by
  have hCover : {sample : BernoulliSquareSample n | ¬BernoulliHeavyBound d beta sample} ⊆
      {sample | ¬BernoulliDegreeDiscrepancy d beta sample} := by
    intro sample hFail hGood
    exact hFail (bernoulli_degree_discrepancy_heavy_bound hn hd hBeta sample hGood)
  exact (measureReal_mono hCover (h₂ := by finiteness)).trans
    (bernoulli_degree_discrepancy_failure_probability hn hd hdn hBeta)

end CircularLaw
