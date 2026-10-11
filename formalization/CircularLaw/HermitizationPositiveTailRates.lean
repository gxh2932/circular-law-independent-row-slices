import CircularLaw.HermitizationDeletionParameters
import CircularLaw.SingularPositiveLogEnergy
import CircularLaw.MatrixEnergyShift
import CircularLaw.FixedShiftIntermediateTheorem

/-!
# The actual row-slice positive tail at both deletion scales

The rounded cutoff and exact row-slice energy give a deterministic
vanishing upper bound. This closes the positive-tail estimate for every
fixed shift and every fixed exponent 0<a<=1.
-/

noncomputable section
open Classical Filter
open scoped Matrix BigOperators Topology

namespace CircularLaw

theorem log_one_add_energy_power_bound {t C b : ℝ} (ht : 1 ≤ t)
    (hC : 0 ≤ C) (hb : 0 ≤ b) :
    Real.log (1 + C * Real.rpow t b) ≤ Real.log (1 + C) + b * Real.log t := by
  have htPos : 0 < t := zero_lt_one.trans_le ht
  have hPower : (1 : ℝ) ≤ Real.rpow t b := Real.one_le_rpow ht hb
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < 1 + C * Real.rpow t b)
    (show 1 + C * Real.rpow t b ≤ (1 + C) * Real.rpow t b by nlinarith)
  simp only [Real.rpow_eq_pow] at hLog ⊢
  rw [Real.log_mul (by positivity : (1 + C : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos htPos b).ne', Real.log_rpow htPos] at hLog
  exact hLog

theorem square_positive_log_hermitization_deletion_bound {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    {a C : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hC : 0 ≤ C)
    (hEnergy : squareMatrixEnergy A ≤ C * n * d) :
    (∑ j : Fin (hermitizationDeletionCount n d a),
      max (Real.log (orderedSquareSingularValues A
        (Fin.castLE (hermitizationDeletionCount_le_dimension (by omega) ha.le) j))) 0) / n ≤
      (Real.log (1 + C) + (1 + a) * Real.log d) / Real.rpow (d : ℝ) a := by
  let r := hermitizationDeletionCount n d a
  have hrn : r ≤ n := hermitizationDeletionCount_le_dimension (by omega) ha.le
  have hr : (0 : ℝ) < r := by exact_mod_cast hermitizationDeletionCount_pos hn hd a
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPowerPos : 0 < Real.rpow (d : ℝ) a := Real.rpow_pos_of_pos hdR a
  have hPowerDimension : Real.rpow (d : ℝ) a ≤ n :=
    (show Real.rpow (d : ℝ) a ≤ (d : ℝ) from by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hdOne haOne).trans
      (by exact_mod_cast hdn)
  have hCount := hermitizationDeletionCount_lower n d a
  have hNScale : (n : ℝ) ≤ (r : ℝ) * Real.rpow (d : ℝ) a :=
    (div_le_iff₀ hPowerPos).mp hCount
  have hEnergyScale : squareMatrixEnergy A / r ≤ C * ((d : ℝ) * Real.rpow (d : ℝ) a) := by
    apply (div_le_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_left hNScale (mul_nonneg hC (Nat.cast_nonneg d))
    nlinarith only [hEnergy, h]
  have hProduct : (d : ℝ) * Real.rpow (d : ℝ) a = Real.rpow (d : ℝ) (1 + a) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_add hdR, Real.rpow_one]
  rw [hProduct] at hEnergyScale
  have hEnergyNonneg := squareMatrixEnergy_nonneg A
  have hLogUpper := (Real.log_le_log (by positivity : 0 < 1 + squareMatrixEnergy A / r)
    (add_le_add_right hEnergyScale 1)).trans
    (log_one_add_energy_power_bound hdOne hC (by linarith : 0 ≤ 1 + a))
  have hRateNonneg : 0 ≤ Real.log (1 + C) + (1 + a) * Real.log d := by
    have hLogC := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + C)
    have hLogD := Real.log_nonneg hdOne
    positivity
  have hFraction : (r : ℝ) / (2 * n) ≤ 1 / Real.rpow (d : ℝ) a := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n) hPowerPos).mpr
    have hUpper := (le_div_iff₀ hPowerPos).mp (hermitizationDeletionCount_upper hd a hPowerDimension)
    simpa only [one_mul] using hUpper
  calc
    _ ≤ ((r : ℝ) / (2 * n)) * Real.log (1 + squareMatrixEnergy A / r) :=
      square_positive_log_prefix_energy_bound A hrn
    _ ≤ ((r : ℝ) / (2 * n)) * (Real.log (1 + C) + (1 + a) * Real.log d) :=
      mul_le_mul_of_nonneg_left hLogUpper (by positivity)
    _ ≤ (1 / Real.rpow (d : ℝ) a) * (Real.log (1 + C) + (1 + a) * Real.log d) :=
      mul_le_mul_of_nonneg_right hFraction hRateNonneg
    _ = _ := by ring

theorem hermitization_positive_log_budget_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) {a : ℝ} (ha : 0 < a) (C : ℝ) :
    Tendsto (fun n => (Real.log (1 + C) + (1 + a) * Real.log (d n : ℝ)) /
      Real.rpow (d n : ℝ) a) atTop (𝓝 0) := by
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hInv := ((tendsto_rpow_atTop ha).comp hCast).inv_tendsto_atTop
  have hLog : Tendsto (fun n => Real.log (d n : ℝ) / Real.rpow (d n : ℝ) a) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp hCast
  have hLimit := (hInv.const_mul (Real.log (1 + C))).add (hLog.const_mul (1 + a))
  simp only [mul_zero, add_zero] at hLimit
  apply hLimit.congr'
  exact Eventually.of_forall (fun n => by
    simp only [Pi.inv_apply, Function.comp_apply, Real.rpow_eq_pow]
    ring)

theorem row_slice_shifted_energy_degree_bound {n d : ℕ} (rows : RowSliceMatrix n d) (z : ℂ) :
    squareMatrixEnergy (fullShiftedSliceMatrix (z * (Real.sqrt (d : ℝ) : ℂ)) rows) ≤
      (2 + 2 * ‖z‖ ^ 2) * n * d := by
  have h := squareMatrixEnergy_shift_le (sliceMatrix rows) (z * (Real.sqrt (d : ℝ) : ℂ))
  rw [shifted_sqrt_degree_norm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
    show squareMatrixEnergy (sliceMatrix rows) = (n : ℝ) * d from frobenius_sq rows] at h
  exact h.trans_eq (by ring)

theorem row_slice_positive_log_tail_eventually_small (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ rows : RowSliceMatrix n (d n),
      ∀ hrn : hermitizationDeletionCount n (d n) a ≤ n,
        (∑ j : Fin (hermitizationDeletionCount n (d n) a),
          max (Real.log (orderedSquareSingularValues
            (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (Fin.castLE hrn j))) 0) / n < ε := by
  have hSmall := (hermitization_positive_log_budget_tendsto_zero d hDegree ha (2 + 2 * ‖z‖ ^ 2)).eventually
    (gt_mem_nhds hε)
  filter_upwards [hSmall, eventually_valid_bernoulli_degrees hDegree hSparse] with n hs hd rows hrn
  have hn : 0 < n := lt_of_lt_of_le hd.1 hd.2
  exact (square_positive_log_hermitization_deletion_bound _ hn hd.1 hd.2 ha haOne
    (by positivity : (0 : ℝ) ≤ 2 + 2 * ‖z‖ ^ 2) (row_slice_shifted_energy_degree_bound rows z)).trans_lt hs

end CircularLaw
