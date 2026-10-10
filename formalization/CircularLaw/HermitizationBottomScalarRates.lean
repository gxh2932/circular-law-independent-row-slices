import CircularLaw.HermitizationCutoffBudgets
import CircularLaw.SingularBottomLogBounds
import CircularLaw.IntermediateDeletionBudget

/-!
# Deterministic bottom-tail costs at the two source cutoffs

The exact rounded deletion count is retained. The intermediate contribution
vanishes when its degree exponent is less than the deletion exponent. The
lower cutoff's logarithmic cost has a sharper degree budget than the
polynomial envelope used for row replacement.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem polynomial_cutoff_negative_log_eq {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) :
    max (-Real.log (polynomialHermitizationCutoff n B)) 0 = B * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  simp only [polynomialHermitizationCutoff, Real.rpow_eq_pow]
  rw [Real.log_rpow hnR]
  have hCost : 0 ≤ B * Real.log n := mul_nonneg hB hLog
  have hNeg : -((-B) * Real.log n) = B * Real.log n := by ring
  rw [hNeg, max_eq_left hCost]

theorem lower_cutoff_negative_log_eq {n : ℕ} (hn : 0 < n) {CL : ℝ} (hCL : 0 ≤ CL)
    (hLog : 1 ≤ Real.log n) :
    max (-Real.log (lowerHermitizationCutoff n CL)) 0 =
      CL * Real.log (Real.log n) * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLL := Real.log_nonneg hLog
  simp only [lowerHermitizationCutoff, Real.rpow_eq_pow]
  rw [Real.log_rpow hnR]
  have hCost : 0 ≤ CL * Real.log (Real.log n) * Real.log n := by positivity
  have hNeg : -(-(CL * Real.log (Real.log n)) * Real.log n) =
      CL * Real.log (Real.log n) * Real.log n := by ring
  rw [hNeg, max_eq_left hCost]

theorem hermitization_deletion_fraction_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) {a : ℝ} (haOne : a ≤ 1) :
    (hermitizationDeletionCount n d a : ℝ) / n ≤ 2 / Real.rpow (d : ℝ) a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPower : Real.rpow (d : ℝ) a ≤ n := by
    calc
      _ ≤ (d : ℝ) := by
        simpa only [Real.rpow_one, Real.rpow_eq_pow] using
          Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ d by exact_mod_cast hd) haOne
      _ ≤ n := by exact_mod_cast hdn
  have h := div_le_div_of_nonneg_right (hermitizationDeletionCount_upper hd a hPower) hnR.le
  have hCancel : (2 * (n : ℝ) / Real.rpow (d : ℝ) a) / n = 2 / Real.rpow (d : ℝ) a := by
    field_simp
  exact hCancel ▸ h

theorem hermitization_deletion_power_cost_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) {a κ R : ℝ} (haOne : a ≤ 1) (hR : 0 ≤ R) :
    (hermitizationDeletionCount n d a : ℝ) * R * Real.rpow (d : ℝ) κ / n ≤
      2 * R / Real.rpow (d : ℝ) (a - κ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := mul_le_mul_of_nonneg_right (hermitization_deletion_fraction_bound hn hd hdn haOne)
    (mul_nonneg hR (Real.rpow_nonneg hdR.le κ))
  have hIdentity : Real.rpow (d : ℝ) (a - κ) = Real.rpow (d : ℝ) a / Real.rpow (d : ℝ) κ := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_sub hdR a κ
  rw [hIdentity, div_div_eq_mul_div]
  simp only [Real.rpow_eq_pow] at h ⊢
  convert h using 1 <;> ring

theorem hermitization_deletion_power_cost_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a κ R : ℝ} (haOne : a ≤ 1) (hκ : κ < a) (hR : 0 ≤ R) :
    Tendsto (fun n => (hermitizationDeletionCount n (d n) a : ℝ) * R *
      Real.rpow (d n : ℝ) κ / n) atTop (𝓝 0) := by
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hInv := ((tendsto_rpow_atTop (sub_pos.mpr hκ)).comp hCast).inv_tendsto_atTop
  have hUpper : Tendsto (fun n => 2 * R / Real.rpow (d n : ℝ) (a - κ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hInv.const_mul (2 * R)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun n => div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR) (Real.rpow_nonneg (Nat.cast_nonneg _) κ))
      (Nat.cast_nonneg n)))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact hermitization_deletion_power_cost_bound (lt_of_lt_of_le hd.1 hd.2) hd.1 hd.2 haOne hR

theorem lower_cutoff_negative_log_degree_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {K CL : ℝ} (hK : 0 < K) (hCL : 0 ≤ CL)
    (hLog : 1 ≤ Real.log n) (hLogN : Real.log n ≤ K * d) :
    max (-Real.log (lowerHermitizationCutoff n CL)) 0 ≤
      CL * K * d * (|Real.log K| + Real.log d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLLcap := Real.log_le_log (show 0 < Real.log n by linarith) hLogN
  rw [Real.log_mul hK.ne' hdR.ne'] at hLLcap
  have hLL : Real.log (Real.log n) ≤ |Real.log K| + Real.log d :=
    hLLcap.trans (add_le_add_left (le_abs_self _) _)
  have hLLnonneg := Real.log_nonneg hLog
  rw [lower_cutoff_negative_log_eq hn hCL hLog]
  have hProduct := mul_le_mul hLL hLogN (by linarith : 0 ≤ Real.log n)
    (show 0 ≤ |Real.log K| + Real.log d from hLLnonneg.trans hLL)
  have h := mul_le_mul_of_nonneg_left hProduct hCL
  nlinarith only [h]

theorem lower_intermediate_minimum_cost_bound {n d : ℕ} (hd : 4 ≤ d) (hn : 4 * d ^ 3 ≤ n)
    {K CL : ℝ} (hK : 0 < K) (hCL : 0 ≤ CL)
    (hLog : 1 ≤ Real.log n) (hLogN : Real.log n ≤ K * d) :
    (intermediateDeletionCount n d : ℝ) * max (-Real.log (lowerHermitizationCutoff n CL)) 0 / n ≤
      (5 * CL * K) * (|Real.log K| + Real.log d) / d := by
  have hdPos : 0 < d := by omega
  have hnPos : 0 < n := (mul_pos (by decide) (pow_pos hdPos 3)).trans_le hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hScale : (intermediateDeletionCount n d : ℝ) * (d : ℝ) ^ 2 ≤ 5 * n := by
    apply (le_div_iff₀ (pow_pos hdR 2)).mp
    simpa only [mul_div_assoc] using intermediateDeletionCount_scale_bound hdPos hn
  have hRatio : (intermediateDeletionCount n d : ℝ) / n ≤ 5 / (d : ℝ) ^ 2 :=
    (div_le_div_iff₀ hnR (pow_pos hdR 2)).mpr (by simpa only [mul_comm] using hScale)
  have hA : 0 ≤ |Real.log K| + Real.log d := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hdPos)
    positivity
  have hCost := lower_cutoff_negative_log_degree_bound hnPos hdPos hK hCL hLog hLogN
  calc
    _ = ((intermediateDeletionCount n d : ℝ) / n) * max (-Real.log (lowerHermitizationCutoff n CL)) 0 := by ring
    _ ≤ (5 / (d : ℝ) ^ 2) * (CL * K * d * (|Real.log K| + Real.log d)) :=
      mul_le_mul hRatio hCost (le_max_right _ _) (by positivity)
    _ = _ := by field_simp

end CircularLaw
