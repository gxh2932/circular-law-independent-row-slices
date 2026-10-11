import CircularLaw.TerminalPvProbability

/-!
# Clustered terminal probability including the scalar-grid prefactor

The actual sum of fixed-vector shift suprema retains its two source
decays after multiplication by `2 * d^2`. Restricted-norm covering of
continuous kernel vectors remains a separate proof obligation.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem terminalPv_prefactor_absorbed {n d v : ℕ} {r δ : ℝ} (hd : 0 < d)
    (hLog : Real.log 2 + 2 * Real.log d ≤ (r / 4) * n * δ * v) :
    2 * (d : ℝ) ^ 2 * Real.exp (-(r / 2) * n * δ * v) ≤
      Real.exp (-(r / 4) * n * δ * v) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hExpD : Real.exp (2 * Real.log d) = (d : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 2
  calc
    _ = Real.exp (Real.log 2 + 2 * Real.log d) * Real.exp (-(r / 2) * n * δ * v) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), hExpD]
    _ ≤ Real.exp ((r / 4) * n * δ * v) * Real.exp (-(r / 2) * n * δ * v) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hLog) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_sourceTerminalClustered_prefactor_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      ∃ hA : (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
        (sourceTerminalClusteredFamily n d L a₃)).Finite,
      letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
        (sourceTerminalClusteredFamily n d L a₃)) := hA.fintype
      ∀ I : Finset (Fin n), I.card = n - L →
      2 * (d : ℝ) ^ 2 * canonicalFamilySupProbabilitySum
        (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
          (sourceTerminalClusteredFamily n d L a₃)) I (d ^ structuralTerminalExponent n d L) d R ≤
        Real.exp (-(sourcePvDecayRate a₃ / 4) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) +
        Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) := by
  have hCPos : 0 < C := by linarith
  have hRate : 0 < sourcePvDecayRate a₃ / 4 := div_pos (sourcePvDecayRate_pos ha) (by norm_num)
  filter_upwards [eventually_sourceTerminalClustered_probability_uniform ha hSmall hC hσ R hR,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_structuralCluster_log_cost_uniform hCPos σ (Real.log 2) 2 hRate,
    eventually_degree_property_uniform hCPos (eventually_profileException_polynomial_prefactor 4)]
    with n hSum hConditions hBudget hException
  intro d hBand L hL
  obtain ⟨hA, hBound⟩ := hSum d hBand L hL
  refine ⟨hA, ?_⟩
  letI : Fintype (canonicalApproxFamily (d ^ structuralTerminalExponent n d L)
    (sourceTerminalClusteredFamily n d L a₃)) := hA.fintype
  intro I hI
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFinite.2.1
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hδ := structuralClusterFraction_pos hFinite.2.1 hCubic hL
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hFinite.1
  have hLog : Real.log 2 + 2 * Real.log d ≤ (sourcePvDecayRate a₃ / 4) * n *
      structuralClusterFraction n L * structuralTerminalExponent n d L := by
    apply (hBudget d hBand L hL).2.trans
    have hMargin : (structuralTerminalExponent n d L : ℝ) - 4 ≤
        structuralTerminalExponent n d L := by linarith
    have hAtOne := mul_le_mul_of_nonneg_left hMargin (mul_nonneg hRate.le hδ.le)
    have hDimension := mul_le_mul_of_nonneg_right hnR
      (mul_nonneg (mul_nonneg hRate.le hδ.le) (Nat.cast_nonneg (structuralTerminalExponent n d L)))
    nlinarith only [hAtOne, hDimension]
  have hMain := terminalPv_prefactor_absorbed hFinite.2.1 hLog
  have hDegree : (1 : ℝ) ≤ 2 * d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hFinite.2.1
    linarith
  have hError := structural_profileException_prefactor_absorbed (v := 1)
    hFinite.1 hFinite.2.1 (by simpa only [Nat.cast_one] using hDegree) (hException d hBand.1)
  apply (mul_le_mul_of_nonneg_left (hBound I hI) (by positivity : 0 ≤ 2 * (d : ℝ) ^ 2)).trans
  rw [mul_add]
  exact add_le_add hMain (by simpa only [Nat.cast_one, mul_one] using hError)

end CircularLaw
