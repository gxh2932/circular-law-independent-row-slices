import CircularLaw.HermitizationReplacementRates

/-!
# The two manuscript regularization cutoffs satisfy degree budgets

These deterministic estimates discharge the logarithmic ratio premise
of the replacement-rate theorem for tau=n^(-C_L*log(log(n))) and
tau=n^(-B). A logarithmic lower degree bound is sufficient for both.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def lowerHermitizationCutoff (n : ℕ) (CL : ℝ) : ℝ :=
  Real.rpow (n : ℝ) (-(CL * Real.log (Real.log n)))

def polynomialHermitizationCutoff (n : ℕ) (B : ℝ) : ℝ := Real.rpow (n : ℝ) (-B)

theorem shifted_replacement_variable_power_degree_budget {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (z : ℂ)
    {K L B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hLogN : Real.log n ≤ K * d) (hBcap : B ≤ L * d) :
    Real.log (rowReplacementUpperBound n (Real.rpow (n : ℝ) (-B) / n)
      (‖z‖ * Real.sqrt d) / (Real.rpow (n : ℝ) (-B) / n)) ≤
      (Real.log (2 * (1 + ‖z‖)) + L * K + (3 / 2 : ℝ) * K) * Real.rpow (d : ℝ) 2 := by
  have hCap : 0 ≤ Real.log (2 * (1 + ‖z‖)) :=
    Real.log_nonneg (by nlinarith [norm_nonneg z])
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdSqOne : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hdSqD : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have h := shifted_replacement_power_cutoff_log_bound hn hdn z hB
  have hCost : (B + 3 / 2) * Real.log n ≤ (L * d + 3 / 2) * (K * d) := by
    exact (mul_le_mul_of_nonneg_left hLogN (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith : B + 3 / 2 ≤ L * d + 3 / 2) (by positivity))
  have hCapSq := mul_le_mul_of_nonneg_left hdSqOne hCap
  have hLinearSq := mul_le_mul_of_nonneg_left hdSqD (show 0 ≤ (3 / 2 : ℝ) * K by positivity)
  simp only [Real.rpow_eq_pow, Real.rpow_two] at h ⊢
  nlinarith only [h, hCost, hCapSq, hLinearSq]

theorem lower_cutoff_replacement_degree_budget {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (z : ℂ)
    {K CL : ℝ} (hK : 0 ≤ K) (hCL : 0 ≤ CL)
    (hLogOne : 1 ≤ Real.log n) (hLogN : Real.log n ≤ K * d) :
    Real.log (rowReplacementUpperBound n (lowerHermitizationCutoff n CL / n)
      (‖z‖ * Real.sqrt d) / (lowerHermitizationCutoff n CL / n)) ≤
      (Real.log (2 * (1 + ‖z‖)) + (CL * K) * K + (3 / 2 : ℝ) * K) * Real.rpow (d : ℝ) 2 := by
  have hLL : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hLogOne
  have hLLcap : Real.log (Real.log n) ≤ Real.log n := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith)
    linarith
  have hBcap : CL * Real.log (Real.log n) ≤ (CL * K) * d := by
    have h := mul_le_mul_of_nonneg_left (hLLcap.trans hLogN) hCL
    nlinarith only [h]
  exact shifted_replacement_variable_power_degree_budget hn hd hdn z hK
    (mul_nonneg hCL hLL) hLogN hBcap

theorem polynomial_cutoff_replacement_degree_budget {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (z : ℂ)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hLogN : Real.log n ≤ K * d) :
    Real.log (rowReplacementUpperBound n (polynomialHermitizationCutoff n B / n)
      (‖z‖ * Real.sqrt d) / (polynomialHermitizationCutoff n B / n)) ≤
      (Real.log (2 * (1 + ‖z‖)) + B * K + (3 / 2 : ℝ) * K) * Real.rpow (d : ℝ) 2 := by
  have hBcap : B ≤ B * (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ d by exact_mod_cast hd) hB
    simpa only [mul_one] using h
  exact shifted_replacement_variable_power_degree_budget hn hd hdn z hK hB hLogN hBcap

theorem lower_cutoff_replacement_error_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    {K CL a : ℝ} (hK : 0 ≤ K) (hCL : 0 ≤ CL) (ha : 0 < a) (haOne : a < 1)
    (hLogN : ∀ᶠ n : ℕ in atTop, Real.log n ≤ K * d n) :
    Tendsto (fun n => rowReplacementErrorBound n (d n)
      (n - hermitizationDeletionCount n (d n) a) (lowerHermitizationCutoff n CL / n)
      (‖z‖ * Real.sqrt (d n))) atTop (𝓝 0) := by
  let C := Real.log (2 * (1 + ‖z‖)) + (CL * K) * K + (3 / 2 : ℝ) * K
  have hC : 0 ≤ C := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (1 + ‖z‖) by nlinarith [norm_nonneg z])
    dsimp [C]
    positivity
  apply hermitization_replacement_error_tendsto_zero d hDegree hSparse ha haOne hC
    (fun n => lowerHermitizationCutoff n CL / n) (fun n => ‖z‖ * Real.sqrt (d n)) (b := 2)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (Real.rpow_pos_of_pos hnR _) hnR
  · have hLog := (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 1
    filter_upwards [hLogN, hLog, eventually_valid_bernoulli_degrees hDegree hSparse] with n hLn hL hd
    exact lower_cutoff_replacement_degree_budget (lt_of_lt_of_le hd.1 hd.2) hd.1 hd.2 z hK hCL hL hLn

theorem polynomial_cutoff_replacement_error_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    {K B a : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (ha : 0 < a) (haOne : a < 1)
    (hLogN : ∀ᶠ n : ℕ in atTop, Real.log n ≤ K * d n) :
    Tendsto (fun n => rowReplacementErrorBound n (d n)
      (n - hermitizationDeletionCount n (d n) a) (polynomialHermitizationCutoff n B / n)
      (‖z‖ * Real.sqrt (d n))) atTop (𝓝 0) := by
  let C := Real.log (2 * (1 + ‖z‖)) + B * K + (3 / 2 : ℝ) * K
  have hC : 0 ≤ C := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (1 + ‖z‖) by nlinarith [norm_nonneg z])
    dsimp [C]
    positivity
  apply hermitization_replacement_error_tendsto_zero d hDegree hSparse ha haOne hC
    (fun n => polynomialHermitizationCutoff n B / n) (fun n => ‖z‖ * Real.sqrt (d n)) (b := 2)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (Real.rpow_pos_of_pos hnR _) hnR
  · filter_upwards [hLogN, eventually_valid_bernoulli_degrees hDegree hSparse] with n hLn hd
    exact polynomial_cutoff_replacement_degree_budget (lt_of_lt_of_le hd.1 hd.2) hd.1 hd.2 z hK hB hLn

end CircularLaw
