import CircularLaw.StructuralNetUnion
import CircularLaw.FixedNetSplit
import CircularLaw.SourceClassRowEnergy

/-!
# Absorbing the profile-exception term

The actual conditioning and row factors are bounded first. The crude
net entropy then costs order `n*d^(1/3)`, while the exceptional decay
has order `n*d^(2/3)`. Every bound is uniform in the retained rows.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def fixedNetDegreeFactor (R : ℝ) : ℝ :=
  16 * Real.exp 1 * rowSmallBallConstant * R ^ 2 + 1

theorem fixedNetDegreeFactor_ge_one (R : ℝ) : 1 ≤ fixedNetDegreeFactor R := by
  have hC : 0 ≤ rowSmallBallConstant := by linarith [rowSmallBallConstant_ge_one]
  unfold fixedNetDegreeFactor
  have h : 0 ≤ 16 * Real.exp 1 * rowSmallBallConstant * R ^ 2 := by positivity
  linarith

theorem fixedNetSplitCost_exp_bound {n d K : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hK : (n : ℝ) / 2 ≤ K) (hKn : K ≤ n) (R : ℝ) :
    fixedNetSplitCost n d K R ≤
      Real.exp (2 * (d : ℝ) ^ 2 +
        (n : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log d)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hKR : (0 : ℝ) < K := by linarith
  have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
  have hRatio : (n : ℝ) / K ≤ 2 := (div_le_iff₀ hKR).mpr (by linarith)
  have hC : 0 ≤ rowSmallBallConstant := by linarith [rowSmallBallConstant_ge_one]
  have hLogD : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hLogUpper : Real.log d ≤ (d : ℝ) :=
    (Real.log_le_sub_one_of_pos hdR).trans (by linarith)
  have hSquare : Real.log d ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ hLogD hLogUpper 2
  have hA : 0 ≤ 8 * Real.exp 1 * rowSmallBallConstant * R ^ 2 := by positivity
  have hRow : 2 * fixedNetRowFactor n d K R ≤ fixedNetDegreeFactor R * (d : ℝ) ^ 2 := by
    calc
      _ = (8 * Real.exp 1 * rowSmallBallConstant * R ^ 2) * ((n : ℝ) / K) *
          Real.log d ^ 2 := by unfold fixedNetRowFactor; ring
      _ ≤ ((8 * Real.exp 1 * rowSmallBallConstant * R ^ 2) * 2) * (d : ℝ) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hRatio hA) hSquare (sq_nonneg _)
          (mul_nonneg hA (by norm_num))
      _ ≤ _ := by unfold fixedNetDegreeFactor; nlinarith [sq_nonneg (d : ℝ)]
  have hFactorPos : 0 < fixedNetDegreeFactor R := lt_of_lt_of_le zero_lt_one (fixedNetDegreeFactor_ge_one R)
  have hLogFactor : 0 ≤ Real.log (fixedNetDegreeFactor R) :=
    Real.log_nonneg (fixedNetDegreeFactor_ge_one R)
  have hLogCap : 0 ≤ Real.log (fixedNetDegreeFactor R) + 2 * Real.log d := by linarith
  have hExpD : Real.exp (2 * Real.log d) = (d : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 2
  have hPower : (fixedNetDegreeFactor R * (d : ℝ) ^ 2) ^ K =
      Real.exp ((K : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log d)) := by
    rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log hFactorPos, hExpD]
  have hConditioning : 2 * (K : ℝ) * (d : ℝ) ^ 2 / n ≤ 2 * (d : ℝ) ^ 2 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hKnR (sq_nonneg (d : ℝ))]
  unfold fixedNetSplitCost
  calc
    _ ≤ Real.exp (2 * (d : ℝ) ^ 2) *
        (fixedNetDegreeFactor R * (d : ℝ) ^ 2) ^ K :=
      mul_le_mul (Real.exp_le_exp.mpr hConditioning)
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (fixedNetRowFactor_nonneg n d K R)) hRow K)
        (pow_nonneg (mul_nonneg (by norm_num) (fixedNetRowFactor_nonneg n d K R)) K)
        (Real.exp_nonneg _)
    _ ≤ Real.exp (2 * (d : ℝ) ^ 2) *
        Real.exp ((n : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log d)) := by
      rw [hPower]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hKnR hLogCap)) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem eventually_profileException_degree_budget (R : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      Real.log (fixedNetDegreeFactor R) + 2 * Real.log d +
        128 * Real.rpow (d : ℝ) (1 / 3) ≤
          (averagedProfileRate / 8) * Real.rpow (d : ℝ) (2 / 3) := by
  have hc := averagedProfileRate_pos
  have hLimit : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) (2 / 3))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < averagedProfileRate / 64)),
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 3) (4096 / averagedProfileRate),
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 2 / 3)
      (32 * Real.log (fixedNetDegreeFactor R) / averagedProfileRate)]
    with d hd hLogSmall hRootLarge hPowerLarge
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdR _
  have hRoot : 0 ≤ Real.rpow (d : ℝ) (1 / 3) := Real.rpow_nonneg hdR.le _
  have hSquare : Real.rpow (d : ℝ) (1 / 3) ^ 2 = Real.rpow (d : ℝ) (2 / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hdR.le]
    norm_num
  have hLog := (div_lt_iff₀ hPower).mp hLogSmall
  have hRootScaled := (div_le_iff₀ hc).mp hRootLarge
  have hRootBudget := mul_nonneg hRoot (show 0 ≤
      averagedProfileRate * Real.rpow (d : ℝ) (1 / 3) - 4096 by linarith)
  have hConstant := (div_le_iff₀ hc).mp hPowerLarge
  rw [← hSquare]
  nlinarith only [hLog, hRootBudget, hConstant, hSquare, hc]

theorem profileException_absorbed {n d K : ℕ} {A : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hK : (n : ℝ) / 2 ≤ K) (hKn : K ≤ n) (R : ℝ)
    (hCount : A ≤ Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)))
    (hConditioning : 2 * (d : ℝ) ^ 2 ≤ (averagedProfileRate / 8) * n)
    (hDegree : Real.log (fixedNetDegreeFactor R) + 2 * Real.log d +
      128 * Real.rpow (d : ℝ) (1 / 3) ≤
        (averagedProfileRate / 8) * Real.rpow (d : ℝ) (2 / 3)) :
    fixedNetSplitCost n d K R *
      (A * Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3))) ≤
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hc := averagedProfileRate_pos
  have hPower : 1 ≤ Real.rpow (d : ℝ) (2 / 3) := Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  have hConditioning' : 2 * (d : ℝ) ^ 2 ≤
      (averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3) :=
    hConditioning.trans (le_mul_of_one_le_right (by positivity) hPower)
  have hDegree' := mul_le_mul_of_nonneg_left hDegree (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hDecay := mul_le_mul_of_nonneg_right hK
    (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg d) (2 / 3)))
  calc
    _ ≤ fixedNetSplitCost n d K R *
        (Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) *
          Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCount (Real.exp_nonneg _))
        (fixedNetSplitCost_nonneg n d K R)
    _ ≤ Real.exp (2 * (d : ℝ) ^ 2 +
        (n : ℝ) * (Real.log (fixedNetDegreeFactor R) + 2 * Real.log d)) *
        (Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) *
          Real.exp (-averagedProfileRate * (K : ℝ) * Real.rpow (d : ℝ) (2 / 3))) :=
      mul_le_mul_of_nonneg_right (fixedNetSplitCost_exp_bound hn hd hK hKn R) (by positivity)
    _ ≤ _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Real.rpow_eq_pow] at hConditioning' hDegree' ⊢
      nlinarith only [hConditioning', hDegree', hDecay]

theorem eventually_structural_profileException_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ, ∀ u : ℕ,
      u ≤ structuralTerminalExponent n d L →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
      fixedNetSplitCost n d (n - L) R *
        ((Nat.card (canonicalApproxFamily (d ^ u) X) : ℝ) *
          Real.exp (-averagedProfileRate * ((n - L : ℕ) : ℝ) * Real.rpow (d : ℝ) (2 / 3))) ≤
        Real.exp (-(averagedProfileRate / 4) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  have hc := averagedProfileRate_pos
  filter_upwards [eventually_structuralGradualNet_count_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos (eventually_profileException_degree_budget R),
    eventually_polylog_power_dimension (1 + σ) 2 (by positivity : (0 : ℝ) < 16 / averagedProfileRate)]
    with n hCount hConditions hDegree hDimension
  intro d hBand L hL a₃ u hu X hX
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  have hRows := source_kernel_retained_rows_count hCon hL
  apply profileException_absorbed hFinite.1 hFinite.2.1 hRows.2.2.2 hRows.2.1 R
    (hCount d hBand L hL a₃ u hu X hX).2
  · have h := hDimension d hBand.2
    have hScaled := mul_le_mul_of_nonneg_left h hc.le
    field_simp at hScaled
    nlinarith
  · exact hDegree d hBand.1

end CircularLaw
