import CircularLaw.MissingRowCost
import CircularLaw.LogarithmicNetCost
import CircularLaw.SourceTerminalProbability

/-!
# The source K1 and K2 decay rates after all fixed-scale costs

The source constants, class count and missing-row factor are kept in
the exponent. The K1 decay absorbs the logarithmic row cost, and the
K2 decay absorbs every fixed multiple of the degree logarithm.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceK1DecayExponent (a₃ : ℝ) : ℝ := (1 / 4608) * a₃ / 32

def sourceK2DispersionExponent (a₃ : ℝ) : ℝ := (1 / 4608) * a₃ / 16

def sourceK2DispersionCoefficient (a₃ : ℝ) : ℝ :=
  2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)

def sourceK2DecayRate (a₃ : ℝ) : ℝ := averagedProfileRate * sourceK2DispersionCoefficient a₃ / 8

theorem sourceK1DecayExponent_pos {a₃ : ℝ} (ha : 0 < a₃) : 0 < sourceK1DecayExponent a₃ := by
  unfold sourceK1DecayExponent
  positivity

theorem sourceK2DispersionExponent_pos {a₃ : ℝ} (ha : 0 < a₃) : 0 < sourceK2DispersionExponent a₃ := by
  unfold sourceK2DispersionExponent
  positivity

theorem sourceK2DispersionCoefficient_pos {a₃ : ℝ} (ha : 0 < a₃) :
    0 < sourceK2DispersionCoefficient a₃ := by
  unfold sourceK2DispersionCoefficient
  positivity

theorem sourceK2DecayRate_pos {a₃ : ℝ} (ha : 0 < a₃) : 0 < sourceK2DecayRate a₃ :=
  div_pos (mul_pos averagedProfileRate_pos (sourceK2DispersionCoefficient_pos ha)) (by norm_num)

def structuralMainTerm (n d L : ℕ) (R E : ℝ) : ℝ :=
  fixedNetSplitCost n d (n - L) R * ((4 : ℝ) ^ (n - L) * (Real.exp n * E))

theorem structuralMainTerm_exp_bound {n d L : ℕ} (R E X Y : ℝ)
    (hCost : fixedNetSplitCost n d (n - L) R ≤ Real.exp X) (hEnergy : E ≤ Real.exp Y) :
    structuralMainTerm n d L R E ≤ Real.exp (X + (n : ℝ) * Real.log 4 + n + Y) := by
  have hRows : ((n - L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n L
  have hLog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hPow : (4 : ℝ) ^ (n - L) ≤ Real.exp ((n : ℝ) * Real.log 4) := by
    calc
      _ = Real.exp (((n - L : ℕ) : ℝ) * Real.log 4) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hRows hLog4)
  unfold structuralMainTerm
  calc
    _ ≤ fixedNetSplitCost n d (n - L) R * ((4 : ℝ) ^ (n - L) * (Real.exp n * Real.exp Y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hEnergy (Real.exp_nonneg _)) (by positivity))
        (fixedNetSplitCost_nonneg n d (n - L) R)
    _ ≤ Real.exp X * (Real.exp ((n : ℝ) * Real.log 4) * (Real.exp n * Real.exp Y)) :=
      mul_le_mul hCost (mul_le_mul_of_nonneg_right hPow (by positivity))
        (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem sourceK1ClassEnergyUpper_exp_bound {n d L : ℕ} {a₃ : ℝ}
    (hd : 0 < d) (hMissing : ((n : ℝ) * Real.sqrt d) ^ L ≤ Real.exp n) :
    sourceK1ClassEnergyUpper n d L a₃ ≤
      Real.exp ((4097 + entropyPenaltyConstant (averagedProfileRate / 2)) * n -
        sourceK1DecayExponent a₃ * n * Real.log d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sourceK1ClassEnergyUpper
  calc
    _ ≤ Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 2)) * n) *
        Real.rpow (d : ℝ) (-((1 / 4608) * a₃ / 32) * n) * Real.exp n :=
      mul_le_mul_of_nonneg_left hMissing (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg hdR.le _))
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_def_of_pos hdR, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold sourceK1DecayExponent
      ring

theorem sourceK2ClassEnergyUpper_exp_bound {n d L : ℕ} {a₃ : ℝ}
    (hd : 0 < d) (hMissing : ((n : ℝ) * Real.sqrt d) ^ L ≤ Real.exp n) :
    sourceK2ClassEnergyUpper n d L a₃ ≤
      Real.exp ((4097 + entropyPenaltyConstant (averagedProfileRate / 4)) * n +
        (n : ℝ) * Real.log d - (averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
          (sourceK2DispersionCoefficient a₃ * Real.rpow (d : ℝ) (sourceK2DispersionExponent a₃))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sourceK2ClassEnergyUpper
  calc
    _ ≤ (Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) *
        (d : ℝ) ^ n * Real.exp n) * Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
          ((2 * ((1 / 65536) * a₃ / 4) ^ 2 * ((1 / 4608) * a₃ / 16384)) *
            Real.rpow (d : ℝ) ((1 / 4608) * a₃ / 16))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMissing (by positivity)) (Real.exp_nonneg _)
    _ = _ := by
      rw [show (d : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log d) by
        rw [Real.exp_nat_mul, Real.exp_log hdR]]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold sourceK2DispersionCoefficient sourceK2DispersionExponent
      ring

theorem sourceK1_mainTerm_absorbed {n d L : ℕ} {a₃ : ℝ}
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hLower : Real.log n ≤ (d : ℝ)) (hLog : 1 ≤ Real.log d)
    (hConditioning : 2 * (d : ℝ) ^ 2 ≤ n) (R : ℝ)
    (hDegree : Real.log (fixedNetDegreeFactor R) + Real.log 4 +
      4099 + entropyPenaltyConstant (averagedProfileRate / 2) + 2 * Real.log (Real.log d) ≤
        (sourceK1DecayExponent a₃ / 2) * Real.log d) :
    structuralMainTerm n d L R (sourceK1ClassEnergyUpper n d L a₃) ≤
      Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  have hRows := source_kernel_retained_rows_count hConditions hL
  have hMissing := source_missingRowFactor_exp_bound hConditions hL (le_refl (1 : ℝ))
    (by simpa only [one_mul] using hLower)
  have h := structuralMainTerm_exp_bound R (sourceK1ClassEnergyUpper n d L a₃) _ _
    (fixedNetSplitCost_loglog_bound hFinite.1 hLog hRows.2.2.2 hRows.2.1 R)
    (sourceK1ClassEnergyUpper_exp_bound hFinite.2.1 hMissing)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hScaled := mul_le_mul_of_nonneg_left hDegree (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hConditioning, hScaled]

theorem sourceK2_mainTerm_absorbed {n d L : ℕ} {a₃ : ℝ} (ha : 0 < a₃)
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hLower : Real.log n ≤ (d : ℝ)) (hConditioning : 2 * (d : ℝ) ^ 2 ≤ n) (R : ℝ)
    (hDegree : Real.log (fixedNetDegreeFactor R) + Real.log 4 +
      4099 + entropyPenaltyConstant (averagedProfileRate / 4) + 3 * Real.log d ≤
        sourceK2DecayRate a₃ * Real.rpow (d : ℝ) (sourceK2DispersionExponent a₃)) :
    structuralMainTerm n d L R (sourceK2ClassEnergyUpper n d L a₃) ≤
      Real.exp (-sourceK2DecayRate a₃ * n * Real.rpow (d : ℝ) (sourceK2DispersionExponent a₃)) := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  have hRows := source_kernel_retained_rows_count hConditions hL
  have hMissing := source_missingRowFactor_exp_bound hConditions hL (le_refl (1 : ℝ))
    (by simpa only [one_mul] using hLower)
  have h := structuralMainTerm_exp_bound R (sourceK2ClassEnergyUpper n d L a₃) _ _
    (fixedNetSplitCost_exp_bound hFinite.1 hFinite.2.1 hRows.2.2.2 hRows.2.1 R)
    (sourceK2ClassEnergyUpper_exp_bound hFinite.2.1 hMissing)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hScaled := mul_le_mul_of_nonneg_left hDegree (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hDecay := mul_le_mul_of_nonneg_right hRows.2.2.2
    (mul_nonneg (sourceK2DispersionCoefficient_pos ha).le
      (Real.rpow_nonneg (Nat.cast_nonneg d) (sourceK2DispersionExponent a₃)))
  have hDecay' := mul_le_mul_of_nonneg_left hDecay averagedProfileRate_pos.le
  unfold sourceK2DecayRate at hScaled ⊢
  simp only [Real.rpow_eq_pow] at hScaled ⊢
  nlinarith only [hConditioning, hScaled, hDecay']

theorem eventually_sourceK1_mainTerm_absorbed_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (hC : 1 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      structuralMainTerm n d L R (sourceK1ClassEnergyUpper n d L a₃) ≤
        Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d) := by
  have hCPos : 0 < C := by linarith
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos hLog,
    eventually_degree_property_uniform hCPos (eventually_loglog_degree_budget
      (by exact div_pos (sourceK1DecayExponent_pos ha) (by norm_num) :
        0 < sourceK1DecayExponent a₃ / 2)
        (Real.log (fixedNetDegreeFactor R) + Real.log 4 + 4099 +
          entropyPenaltyConstant (averagedProfileRate / 2))),
    eventually_polylog_power_dimension (1 + σ) 2 (by norm_num : (0 : ℝ) < 2)]
    with n hConditions hLogDegree hDegree hDimension
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  apply sourceK1_mainTerm_absorbed hCon hL ?_ (hLogDegree d hBand.1) (hDimension d hBand.2) R
    (hDegree d hBand.1)
  have hFinite := source_kernel_dimension_twice_degree hCon
  exact (le_mul_of_one_le_left (Real.log_nonneg (by exact_mod_cast hFinite.1)) hC).trans hBand.1

theorem eventually_sourceK2_mainTerm_absorbed_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (hC : 1 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      structuralMainTerm n d L R (sourceK2ClassEnergyUpper n d L a₃) ≤
        Real.exp (-sourceK2DecayRate a₃ * n * Real.rpow (d : ℝ) (sourceK2DispersionExponent a₃)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos (eventually_log_power_degree_budget
      (sourceK2DispersionExponent_pos ha) (sourceK2DecayRate_pos ha)
        (Real.log (fixedNetDegreeFactor R) + Real.log 4 + 4099 +
          entropyPenaltyConstant (averagedProfileRate / 4)) 3 (by norm_num)),
    eventually_polylog_power_dimension (1 + σ) 2 (by norm_num : (0 : ℝ) < 2)]
    with n hConditions hDegree hDimension
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  apply sourceK2_mainTerm_absorbed ha hCon hL ?_ (hDimension d hBand.2) R (hDegree d hBand.1)
  have hFinite := source_kernel_dimension_twice_degree hCon
  exact (le_mul_of_one_le_left (Real.log_nonneg (by exact_mod_cast hFinite.1)) hC).trans hBand.1

end CircularLaw
