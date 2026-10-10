import CircularLaw.ProfileExceptionCost

/-!
# The profile exception after all discretization scales

This retains the actual approximation cardinality at each exponent.
The full scale sum and the displayed scalar-grid prefactor still have
an exponential `n*d^(2/3)` decay.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def structuralProfileExceptionSum (n d L : ℕ) (R : ℝ)
    (X : ℕ → Set (Fin n → ℂ)) : ℝ :=
  ∑ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
    fixedNetSplitCost n d (n - L) R *
      ((Nat.card (canonicalApproxFamily (d ^ u) (X u)) : ℝ) *
        Real.exp (-averagedProfileRate * ((n - L : ℕ) : ℝ) * Real.rpow (d : ℝ) (2 / 3)))

theorem structuralTerminalExponent_linear_bound {n d L : ℕ} (hd : 1 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) (hLog : 1 ≤ Real.log d) :
    (structuralTerminalExponent n d L : ℝ) ≤ 2 * d := by
  have hRoot : Real.rpow (d : ℝ) (1 / 96) ≤ d := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ d))
        (by norm_num : (1 / 96 : ℝ) ≤ 1)
  calc
    _ ≤ (structuralTerminalExponent n d L : ℝ) * Real.log d :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hLog
    _ ≤ structuralGrowth n L := structuralTerminalExponent_log_bound hd
    _ ≤ 2 * Real.rpow (d : ℝ) (1 / 96) := (structuralGrowth_degree_bounds (by omega) hn hL).2
    _ ≤ _ := mul_le_mul_of_nonneg_left hRoot (by norm_num)

theorem eventually_structuralProfileExceptionSum_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ,
      ∀ X : ℕ → Set (Fin n → ℂ), (∀ u, X u ⊆ sourceGradual n d L a₃) →
      structuralProfileExceptionSum n d L R X ≤
        (structuralTerminalExponent n d L : ℝ) *
          Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  filter_upwards [eventually_structural_profileException_uniform hC σ R] with n hException
  intro d hBand L hL a₃ X hX
  have hIndex : (Finset.Icc 4 (structuralTerminalExponent n d L)).card ≤
      structuralTerminalExponent n d L := by rw [Nat.card_Icc]; omega
  unfold structuralProfileExceptionSum
  calc
    _ ≤ ∑ _u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) :=
      Finset.sum_le_sum (fun u hu => hException d hBand L hL a₃ u
        (Finset.mem_Icc.mp hu).2 (X u) (hX u))
    _ = ((Finset.Icc 4 (structuralTerminalExponent n d L)).card : ℝ) *
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hIndex) (Real.exp_nonneg _)

theorem eventually_profileException_polynomial_prefactor (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, Real.log B + 3 * Real.log d ≤
      (averagedProfileRate / 8) * Real.rpow (d : ℝ) (2 / 3) := by
  have hc := averagedProfileRate_pos
  have hLimit : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) (2 / 3))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < averagedProfileRate / 48)),
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 2 / 3)
      (16 * Real.log B / averagedProfileRate)] with d hd hLogSmall hPowerLarge
  have hPower : 0 < Real.rpow (d : ℝ) (2 / 3) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hLog := (div_lt_iff₀ hPower).mp hLogSmall
  have hConstant := (div_le_iff₀ hc).mp hPowerLarge
  nlinarith only [hLog, hConstant]

theorem structural_profileException_prefactor_absorbed {n d v : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hv : (v : ℝ) ≤ 2 * d)
    (hDegree : Real.log 4 + 3 * Real.log d ≤
      (averagedProfileRate / 8) * Real.rpow (d : ℝ) (2 / 3)) :
    2 * (d : ℝ) ^ 2 * v *
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) ≤
      Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hc := averagedProfileRate_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPrefactor : 2 * (d : ℝ) ^ 2 * v ≤ 4 * (d : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg (d : ℝ))]
  have hExpD : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 3
  have hExponent : Real.log 4 + 3 * Real.log d ≤
      (averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3) := by
    apply hDegree.trans
    have h := mul_le_mul_of_nonneg_right hnR
      (mul_nonneg (by positivity : 0 ≤ averagedProfileRate / 8)
        (Real.rpow_nonneg hdR.le (2 / 3)))
    simp only [Real.rpow_eq_pow] at ⊢
    nlinarith only [h]
  calc
    _ ≤ (4 * (d : ℝ) ^ 3) *
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) :=
      mul_le_mul_of_nonneg_right hPrefactor (Real.exp_nonneg _)
    _ = Real.exp (Real.log 4 + 3 * Real.log d) *
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), hExpD]
    _ ≤ Real.exp ((averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) *
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hExponent) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_structuralProfileException_all_scales_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ,
      ∀ X : ℕ → Set (Fin n → ℂ), (∀ u, X u ⊆ sourceGradual n d L a₃) →
      2 * (d : ℝ) ^ 2 * structuralProfileExceptionSum n d L R X ≤
        Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_structuralProfileExceptionSum_uniform hC σ R,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos hLog,
    eventually_degree_property_uniform hCPos (eventually_profileException_polynomial_prefactor 4)]
    with n hSum hConditions hLogDegree hDegree
  intro d hBand L hL a₃ X hX
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  apply (mul_le_mul_of_nonneg_left (hSum d hBand L hL a₃ X hX) (by positivity :
    0 ≤ 2 * (d : ℝ) ^ 2)).trans
  have h := structural_profileException_prefactor_absorbed hFinite.1 hFinite.2.1
    (structuralTerminalExponent_linear_bound hd hCubic hL (hLogDegree d hBand.1))
    (hDegree d hBand.1)
  simpa only [mul_assoc] using h

end CircularLaw
