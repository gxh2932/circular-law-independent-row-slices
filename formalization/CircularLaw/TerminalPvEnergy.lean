import CircularLaw.TerminalPvHypotheses

/-!
# Clustered terminal energy after the fixed-net costs

The literal missing-row factor and class entropy are retained until the
terminal cluster budget absorbs them. The final rate is positive for
every positive source parameter and multiplies `n * delta_L * v_L`.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourcePvDecayRate (a₃ : ℝ) : ℝ :=
  averagedProfileRate * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 288

theorem sourcePvDecayRate_pos {a₃ : ℝ} (ha : 0 < a₃) : 0 < sourcePvDecayRate a₃ := by
  unfold sourcePvDecayRate
  have hc := averagedProfileRate_pos
  positivity

theorem sourcePvClassEnergyUpper_exp_bound {n d L v : ℕ} (a₃ δ : ℝ)
    (hd : 0 < d) (hMissing : ((n : ℝ) * Real.sqrt d) ^ L ≤ Real.exp n) :
    sourcePvClassEnergyUpper n d L v a₃ δ ≤
      Real.exp ((4097 + entropyPenaltyConstant (averagedProfileRate / 4)) * n +
        (n : ℝ) * Real.log d - (averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
          ((δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sourcePvClassEnergyUpper
  calc
    _ ≤ (Real.exp ((4096 + entropyPenaltyConstant (averagedProfileRate / 4)) * n) *
        (d : ℝ) ^ n * Real.exp n) * Real.exp (-(averagedProfileRate / 2) * ((n - L : ℕ) : ℝ) *
          ((δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMissing (by positivity))
        (Real.exp_nonneg _)
    _ = _ := by
      rw [show (d : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log d) by
        rw [Real.exp_nat_mul, Real.exp_log hdR]]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem sourcePv_mainTerm_absorbed {n d L v : ℕ} {a₃ δ : ℝ}
    (ha : 0 < a₃) (hδ : 0 ≤ δ) (hv : 4 ≤ v)
    (hConditions : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hLower : Real.log n ≤ (d : ℝ)) (hConditioning : 2 * (d : ℝ) ^ 2 ≤ n) (R : ℝ)
    (hDegree : Real.log (fixedNetDegreeFactor R) + Real.log 4 +
      4099 + entropyPenaltyConstant (averagedProfileRate / 4) + 3 * Real.log d ≤
        sourcePvDecayRate a₃ * δ * ((v : ℝ) - 4)) :
    structuralMainTerm n d L R (sourcePvClassEnergyUpper n d L v a₃ δ) ≤
      Real.exp (-sourcePvDecayRate a₃ * n * δ * ((v : ℝ) - 4)) := by
  have hFinite := source_kernel_dimension_twice_degree hConditions
  have hRows := source_kernel_retained_rows_count hConditions hL
  have hMissing := source_missingRowFactor_exp_bound hConditions hL (le_refl (1 : ℝ))
    (by simpa only [one_mul] using hLower)
  have h := structuralMainTerm_exp_bound R (sourcePvClassEnergyUpper n d L v a₃ δ) _ _
    (fixedNetSplitCost_exp_bound hFinite.1 hFinite.2.1 hRows.2.2.2 hRows.2.1 R)
    (sourcePvClassEnergyUpper_exp_bound a₃ δ hFinite.2.1 hMissing)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hScaled := mul_le_mul_of_nonneg_left hDegree (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hMargin : 0 ≤ (v : ℝ) - 4 := by
    have hvR : (4 : ℝ) ≤ v := by exact_mod_cast hv
    linarith
  have hCoefficient : 0 ≤
      (δ * ((1 / 65536) * a₃ / 4) * ((1 / 65536) * a₃) / 36) * ((v : ℝ) - 4) :=
    mul_nonneg (by positivity) hMargin
  have hDecay := mul_le_mul_of_nonneg_right hRows.2.2.2 hCoefficient
  have hDecay' := mul_le_mul_of_nonneg_left hDecay averagedProfileRate_pos.le
  unfold sourcePvDecayRate at hScaled ⊢
  nlinarith only [hConditioning, hScaled, hDecay']

theorem sourcePv_margin_decay_to_terminal {n v : ℕ} {a₃ δ : ℝ}
    (ha : 0 < a₃) (hδ : 0 ≤ δ) (hv : 8 ≤ v) :
    Real.exp (-sourcePvDecayRate a₃ * n * δ * ((v : ℝ) - 4)) ≤
      Real.exp (-(sourcePvDecayRate a₃ / 2) * n * δ * v) := by
  have hvR : (8 : ℝ) ≤ v := by exact_mod_cast hv
  have hMargin : (v : ℝ) / 2 ≤ (v : ℝ) - 4 := by linarith
  have h := mul_le_mul_of_nonneg_left hMargin
    (mul_nonneg (mul_nonneg (sourcePvDecayRate_pos ha).le (Nat.cast_nonneg n)) hδ)
  apply Real.exp_le_exp.mpr
  nlinarith only [h]

theorem eventually_sourcePv_mainTerm_absorbed_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (hC : 1 ≤ C) (σ R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      structuralMainTerm n d L R (sourcePvClassEnergyUpper n d L
        (structuralTerminalExponent n d L) a₃ (structuralClusterFraction n L)) ≤
        Real.exp (-(sourcePvDecayRate a₃ / 2) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_structuralCluster_log_cost_uniform hCPos σ
      (Real.log (fixedNetDegreeFactor R) + Real.log 4 + 4099 +
        entropyPenaltyConstant (averagedProfileRate / 4)) 3 (sourcePvDecayRate_pos ha),
    eventually_polylog_power_dimension (1 + σ) 2 (by norm_num : (0 : ℝ) < 2)]
    with n hConditions hBudget hDimension
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hδ := structuralClusterFraction_pos hFinite.2.1 hCubic hL
  have hDegree := hBudget d hBand L hL
  have hLower : Real.log n ≤ (d : ℝ) :=
    (le_mul_of_one_le_left (Real.log_nonneg (by exact_mod_cast hFinite.1)) hC).trans hBand.1
  exact (sourcePv_mainTerm_absorbed ha hδ.le (by omega : 4 ≤ structuralTerminalExponent n d L)
    hCon hL hLower (hDimension d hBand.2) R hDegree.2).trans
      (sourcePv_margin_decay_to_terminal ha hδ.le hDegree.1)

end CircularLaw
