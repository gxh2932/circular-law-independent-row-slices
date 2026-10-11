import CircularLaw.BernoulliHeavyBound
import CircularLaw.BernoulliLightNet
import CircularLaw.NormRealComplexTransfer

/-!
# Actual centered Bernoulli operator norm with arbitrary polynomial error

Both real nets are full unit-ball nets. The checked light and heavy
estimates therefore bound the real operator, and the real/imaginary
decomposition transfers it to the complex operator used in the paper.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem centered_bernoulli_matrix_sum_light_heavy {n : ℕ} (d : ℕ)
    (Q : Fin n → Fin n → ℝ) (K : ℝ) (sample : BernoulliSquareSample n) :
    centeredBernoulliMatrixSum d Q sample =
      centeredBernoulliMatrixSum d (lightMatrixWeights Q K) sample +
      centeredBernoulliMatrixSum d (heavyMatrixWeights Q K) sample := by
  unfold centeredBernoulliMatrixSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add, matrixWeights_light_add_heavy]

theorem bernoulli_real_norm_on_light_heavy {n d : ℕ} (hn : 0 < n)
    {B beta : ℝ} (hB : 0 ≤ B) (hBeta : 0 ≤ beta) (sample : BernoulliSquareSample n)
    (hLight : BernoulliLightNetBound d B sample) (hHeavy : BernoulliHeavyBound d beta sample) :
    ‖normRealMatrixOperator (centeredBernoulliMatrixReal d sample)‖ ≤
      rowSliceRealNormConstant B beta * Real.sqrt d := by
  let T := (1 + 3 * B + rowSliceHeavyConstant beta) * Real.sqrt d
  have hT : 0 ≤ T := by
    have hHeavyNonneg := rowSliceHeavyConstant_nonneg hBeta
    positivity
  have hNet : ∀ x ∈ normLatticeNet n, ∀ y ∈ normLatticeNet n,
      |⟪x, normRealMatrixOperator (centeredBernoulliMatrixReal d sample) y⟫_ℝ| ≤ T := by
    intro x hx y hy
    have hxNorm := normLatticeNet_norm_bound hn hx
    have hyNorm := normLatticeNet_norm_bound hn hy
    have hxMass : (∑ i, (x i) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg x]
    have hyMass : (∑ j, (y j) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg y]
    rw [normRealMatrixOperator_inner]
    change |centeredBernoulliMatrixSum d (fun i j => x i * y j) sample| ≤ T
    rw [centered_bernoulli_matrix_sum_light_heavy d _ (Real.sqrt (9 * (d : ℝ)) / n)]
    apply (abs_add_le _ _).trans
    have hPair := add_le_add (hLight x hx y hy) (hHeavy (fun i => x i) (fun j => y j) hxMass hyMass)
    apply hPair.trans_eq
    have hRoot : Real.sqrt (9 * (d : ℝ)) = 3 * Real.sqrt d := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
      norm_num
    rw [hRoot]
    dsimp [T]
    ring
  have hBound := norm_operator_bound_of_quarter_nets (normLatticeNet n) (normLatticeNet n)
    (normLatticeNet_unit_ball_cover hn) (normLatticeNet_unit_ball_cover hn) hT
    (normRealMatrixOperator (centeredBernoulliMatrixReal d sample)) hNet
  convert hBound using 1
  unfold rowSliceRealNormConstant T
  ring

theorem inverse_dimension_four_term_budget {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    4 * (n : ℝ) ^ (-(A + 2)) ≤ (n : ℝ) ^ (-A) := by
  have hFirst := inverse_dimension_two_term_budget hn (A + 1)
  have hSecond := inverse_dimension_two_term_budget hn A
  have hExponent : A + 1 + 1 = A + 2 := by ring
  rw [hExponent] at hFirst
  linarith only [hFirst, hSecond]

theorem bernoulli_real_norm_failure_polynomial {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredBernoulliMatrixReal d sample)‖} ≤ (n : ℝ) ^ (-A) := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hCover : {sample : BernoulliSquareSample n |
      rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredBernoulliMatrixReal d sample)‖} ⊆
      {sample | ¬BernoulliLightNetBound d (32 * (A + 21)) sample} ∪
      {sample | ¬BernoulliHeavyBound d (A + 2) sample} := by
    intro sample hFail
    by_cases hLight : BernoulliLightNetBound d (32 * (A + 21)) sample
    · right
      intro hHeavy
      exact (not_lt_of_ge (bernoulli_real_norm_on_light_heavy hnPos
        (by linarith only [hA]) (by linarith only [hA]) sample hLight hHeavy)) hFail
    · exact Or.inl hLight
  have hLight : (sparseBernoulliMatrixLaw n d).real {sample |
      ¬BernoulliLightNetBound d (32 * (A + 21)) sample} ≤ (n : ℝ) ^ (-(A + 2)) := by
    have h := bernoulli_light_net_failure_polynomial hn hd hdn (by linarith only [hA] : 0 ≤ A + 1)
    have hB : 32 * (A + 1 + 20) = 32 * (A + 21) := by ring
    have hExp : A + 1 + 1 = A + 2 := by ring
    rw [hB, hExp] at h
    exact h
  have hCap : (n : ℝ) * Real.exp (-9 * d) ≤ (n : ℝ) ^ (-(A + 2)) := by
    calc
      _ ≤ (n : ℝ) * Real.exp (-(A + 3) * Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hnR.le
        apply Real.exp_le_exp.mpr
        linarith only [hDegree]
      _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-(A + 3) * Real.log (n : ℝ)) := by
        rw [Real.exp_log hnR]
      _ = _ := by rw [← Real.exp_add, Real.rpow_def_of_pos hnR]; congr 1; ring
  have hHeavy := bernoulli_heavy_bound_failure_probability hnPos hd hdn
    (by linarith only [hA] : 0 ≤ A + 2)
  apply (measureReal_mono hCover (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  apply (add_le_add hLight hHeavy).trans
  apply le_trans _ (inverse_dimension_four_term_budget hn A)
  linarith only [hCap]

def bernoulliComplexNormConstant (A : ℝ) : ℝ :=
  2 * rowSliceRealNormConstant (32 * (A + 21)) (A + 2)

theorem bernoulli_complex_norm_constant_nonneg {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ bernoulliComplexNormConstant A := by
  unfold bernoulliComplexNormConstant
  exact mul_nonneg (by norm_num) (rowSliceRealNormConstant_nonneg
    (by linarith only [hA]) (by linarith only [hA]))

theorem bernoulli_complex_norm_failure_polynomial {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      bernoulliComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample)‖} ≤ (n : ℝ) ^ (-A) := by
  have hCover : {sample : BernoulliSquareSample n |
      bernoulliComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample)‖} ⊆
      {sample | rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredBernoulliMatrixReal d sample)‖} := by
    intro sample hFail
    by_contra hNot
    have hReal : ‖normRealMatrixOperator (centeredBernoulliMatrixReal d sample)‖ ≤
        rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d := le_of_not_gt hNot
    have hB : 0 ≤ rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d :=
      mul_nonneg (rowSliceRealNormConstant_nonneg (by linarith only [hA]) (by linarith only [hA]))
        (Real.sqrt_nonneg _)
    have hComplex := normComplexMatrixOperatorReal_norm_bound (centeredBernoulliMatrixReal d sample) hB hReal
    have hConstant : bernoulliComplexNormConstant A * Real.sqrt d =
        2 * (rowSliceRealNormConstant (32 * (A + 21)) (A + 2) * Real.sqrt d) := by
      unfold bernoulliComplexNormConstant
      ring
    rw [hConstant] at hFail
    exact not_lt_of_ge hComplex hFail
  exact (measureReal_mono hCover (h₂ := by finiteness)).trans
    (bernoulli_real_norm_failure_polynomial hn hd hdn hA hDegree)

end CircularLaw
