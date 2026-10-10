import CircularLaw.BernoulliWeightedLaplace
import CircularLaw.BernoulliMatrixDiscrepancy
import CircularLaw.LightCoupleBounds

/-!
# Light coefficients of the actual centered Bernoulli matrix

Unlike fixed-degree rows, the right vector need not have zero sum. The
product-law signed moment controls the centered light sum directly.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def centeredBernoulliMatrixReal {n : ℕ} (d : ℕ) (sample : BernoulliSquareSample n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => bernoulliSquareMatrixReal sample i j - (d : ℝ) / n

def centeredBernoulliMatrixSum {n : ℕ} (d : ℕ) (Q : Fin n → Fin n → ℝ)
    (sample : BernoulliSquareSample n) : ℝ :=
  ∑ i, ∑ j, centeredBernoulliMatrixReal d sample i j * Q i j

theorem centered_bernoulli_matrix_sum_eq_product_sum {n d : ℕ}
    (Q : Fin n → Fin n → ℝ) (sample : BernoulliSquareSample n) :
    centeredBernoulliMatrixSum d Q sample =
      bernoulliWeightedCenteredSum (rowBernoulliParameter n d) (fun a => Q a.1 a.2) sample := by
  simp only [centeredBernoulliMatrixSum, centeredBernoulliMatrixReal,
    bernoulliSquareMatrixReal, bernoulliWeightedCenteredSum, bernoulliCenteredValue,
    rowBernoulliParameter_coe, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bernoulli_light_tilt_rate {n d : ℕ} (hn : 0 < n) {N B : ℝ}
    (hN : 0 < N) (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B) :
    (n / (4 * Real.sqrt N)) ^ 2 * ((d : ℝ) / n) -
      (n / (4 * Real.sqrt N)) * (B * Real.sqrt N) ≤ -B * n / 8 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hVariance : (n / (4 * Real.sqrt N)) ^ 2 * ((d : ℝ) / n) =
      ((n : ℝ) * d) / (16 * N) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hN.le]
    field_simp
    ring
  have hLinear : (n / (4 * Real.sqrt N)) * (B * Real.sqrt N) = B * n / 4 := by
    field_simp
  rw [hVariance, hLinear]
  have hProxy : ((n : ℝ) * d) / (16 * N) ≤ n / 16 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * N)).mpr
    have hScaled := mul_le_mul_of_nonneg_left hdN hnR.le
    nlinarith only [hScaled]
  have hBScaled := mul_le_mul_of_nonneg_right hB hnR.le
  linarith only [hProxy, hBScaled]

theorem bernoulli_source_light_centered_probability {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) {N B : ℝ} (hN : 0 < N)
    (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B) (Q : Fin n → Fin n → ℝ)
    (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      B * Real.sqrt N ≤ |centeredBernoulliMatrixSum d (lightMatrixWeights Q (Real.sqrt N / n)) sample|} ≤
        4 * Real.exp (-B * n / 32) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  let t : ℝ := n / (4 * Real.sqrt N)
  let K : ℝ := Real.sqrt N / n
  let w : (Fin n × Fin n) → ℝ := fun a => lightMatrixWeights Q K a.1 a.2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hCap : ∀ a, |w a| ≤ K := fun a => lightMatrixWeights_cap Q (by dsimp [K]; positivity) a.1 a.2
  have hScale : |t| * K ≤ 1 := by
    rw [abs_of_nonneg ht]
    dsimp [t, K]
    have hIdentity : (n / (4 * Real.sqrt N)) * (Real.sqrt N / n) = (1 : ℝ) / 4 := by
      field_simp
    rw [hIdentity]
    norm_num
  have hMass : (∑ a, w a ^ 2) ≤ 1 := by
    simpa only [w, Fintype.sum_prod_type] using (lightMatrixWeights_squared_sum_le Q K).trans hSquare
  have hVariance : (rowBernoulliParameter n d : ℝ) * (∑ a, w a ^ 2) ≤ (d : ℝ) / n := by
    rw [rowBernoulliParameter_coe]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hMass (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  simp_rw [centered_bernoulli_matrix_sum_eq_product_sum]
  have hTail := bernoulli_weighted_centered_abs_tail (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one hn hdn) w ht hCap hScale (B * Real.sqrt N)
  apply hTail.trans
  have hRate : t ^ 2 * ((rowBernoulliParameter n d : ℝ) * ∑ a, w a ^ 2) - t * (B * Real.sqrt N) ≤
      -B * n / 8 := by
    apply (sub_le_sub_right (mul_le_mul_of_nonneg_left hVariance (sq_nonneg t)) _).trans
    exact bernoulli_light_tilt_rate hn hN hdN hB
  calc
    _ ≤ 2 * Real.exp (-B * n / 8) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hRate) (by norm_num)
    _ ≤ 4 * Real.exp (-B * n / 32) := by
      have hBNonneg : 0 ≤ B := by linarith only [hB]
      apply mul_le_mul (by norm_num : (2 : ℝ) ≤ 4) _ (Real.exp_nonneg _) (by norm_num)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hBNonneg hnR.le]

end CircularLaw
