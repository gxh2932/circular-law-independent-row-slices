import CircularLaw.StructuralKernelAlternatives

/-!
# Absorbing the three structural decay terms

Each checked terminal decay is uniformly at most `n^-2`. The assembled
failure therefore reduces to `4/n + 3/n^2` plus twice the actual norm
failure. Its reusable conditional theorem takes the actual norm tail
as a premise. `StructuralKernelTheorem` supplies that checked tail and
closes the source structural conclusion with explicit failure `5/n`.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem exp_negative_twice_dimension_le_inverse_square {n : ℕ} (hn : 0 < n) :
    Real.exp (-2 * (n : ℝ)) ≤ 1 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLog : Real.log n ≤ (n : ℝ) := (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
  have hExp : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnR] using Real.exp_nat_mul (Real.log n) 2
  calc
    _ ≤ Real.exp (-(2 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, hExp, one_div]

theorem eventually_structural_decay_terms_uniform {a₃ C : ℝ}
    (ha₃ : 0 < a₃) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
        Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) ≤ 1 / (n : ℝ) ^ 2 ∧
        Real.exp (-(sourcePvDecayRate a₃ / 4) * n * structuralClusterFraction n L *
          structuralTerminalExponent n d L) ≤ 1 / (n : ℝ) ^ 2 ∧
        Real.exp (-(averagedProfileRate / 8) * n * Real.rpow (d : ℝ) (2 / 3)) ≤
          1 / (n : ℝ) ^ 2 := by
  have hK := sourceK1DecayExponent_pos ha₃
  have hP := sourcePvDecayRate_pos ha₃
  have hProfile := averagedProfileRate_pos
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop
      (8 / sourceK1DecayExponent a₃)
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_property_uniform hC hLog,
    eventually_degree_property_uniform hC (eventually_degree_real_power_lower
      (by norm_num : (0 : ℝ) < 2 / 3) (16 / averagedProfileRate)),
    eventually_structuralCluster_log_cost_uniform hC σ 2 0 (by positivity : 0 < sourcePvDecayRate a₃ / 4),
    eventually_source_kernel_conditions_uniform hC (1 + σ)]
    with n hn hKDegree hProfileDegree hPDegree hConditions
  intro d hBand L hL
  have hnPos : 0 < n := by omega
  have hCon := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have h := hCon.degree_large; omega
  have hCubicDimension : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hKScaled := (div_le_iff₀ hK).mp (hKDegree d hBand.1)
  dsimp only [Function.comp_apply] at hKScaled
  have hProfileScaled := (div_le_iff₀ hProfile).mp (hProfileDegree d hBand.1)
  have hPScaled := (hPDegree d hBand L hL).2
  simp only [zero_mul, add_zero] at hPScaled
  have hFraction := (structuralClusterFraction_pos hd hCubicDimension hL).le
  have hPProduct := mul_nonneg (div_nonneg hP.le (by norm_num : (0 : ℝ) ≤ 4)) hFraction
  have hKCost : 2 ≤ (sourceK1DecayExponent a₃ / 4) * Real.log d := by nlinarith only [hKScaled]
  have hPCost : 2 ≤ (sourcePvDecayRate a₃ / 4) * structuralClusterFraction n L *
      (structuralTerminalExponent n d L : ℝ) := by nlinarith only [hPScaled, hPProduct]
  have hProfileCost : 2 ≤ (averagedProfileRate / 8) * Real.rpow (d : ℝ) (2 / 3) := by
    nlinarith only [hProfileScaled]
  have hKN := mul_le_mul_of_nonneg_right hKCost (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hPN := mul_le_mul_of_nonneg_right hPCost (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hProfileN := mul_le_mul_of_nonneg_right hProfileCost (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr (by nlinarith only [hKN])).trans
      (exp_negative_twice_dimension_le_inverse_square hnPos)
  · exact (Real.exp_le_exp.mpr (by nlinarith only [hPN])).trans
      (exp_negative_twice_dimension_le_inverse_square hnPos)
  · exact (Real.exp_le_exp.mpr (by nlinarith only [hProfileN])).trans
      (exp_negative_twice_dimension_le_inverse_square hnPos)

theorem source_structural_failure_budget {n d L : ℕ} {a B : ℝ}
    (hn : 5 ≤ n) (I : Finset (Fin n)) (ζ : ℂ)
    (hFailure : uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralKernel L a I ζ rows) ≤
      4 / (n : ℝ) + 3 / (n : ℝ) ^ 2 +
        2 * uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B))
    (hNorm : uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) ≤
      1 / (n : ℝ) ^ 100) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralKernel L a I ζ rows) ≤
      5 / (n : ℝ) := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hPower := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ n) (by decide : 2 ≤ 100)
  have hInverse : 1 / (n : ℝ) ^ 100 ≤ 1 / (n : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hnPos 2) hPower
  have hMass := hNorm.trans hInverse
  have hBudget : 4 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 2 ≤ 5 / (n : ℝ) := by
    apply (le_div_iff₀ hnPos).mpr
    field_simp
    nlinarith
  exact hFailure.trans ((by
    simp only [div_eq_mul_inv, one_mul] at hMass ⊢
    linarith only [hMass] :
    4 / (n : ℝ) + 3 / (n : ℝ) ^ 2 +
      2 * uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) ≤
        4 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 2).trans hBudget)

theorem eventually_source_structural_kernel_failure_reduced_uniform {a a₃ C σ : ℝ}
    (hC : sourceKernelLowerConstant ≤ C) (hC96 : 96 ≤ C)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 65536)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (ha₃Net : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800)
    (ha : 0 < a) (haOne : a ≤ 1) (hσ : σ ≤ 1)
    (B Z₀ : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceStructuralKernel L a I ζ rows) ≤
            4 / (n : ℝ) + 3 / (n : ℝ) ^ 2 +
            2 * uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_structural_kernel_probability_uniform hC hC96 ha₃ ha₃Small
      hEntropy ha₃Net ha haOne hσ B Z₀ 1 hB hZ le_rfl,
    eventually_structural_decay_terms_uniform ha₃ hCPos σ] with n hFailure hDecay
  intro d hBand L hL I hI ζ hShift
  have h := hFailure d hBand L hL I hI ζ hShift
  obtain ⟨hK, hP, hProfile⟩ := hDecay d hBand L hL
  simp only [div_eq_mul_inv, one_mul] at h hK hP hProfile ⊢
  linarith only [h, hK, hP, hProfile]

theorem eventually_source_structural_kernel_good_of_norm_tail_uniform {a a₃ C σ : ℝ}
    (hC : sourceKernelLowerConstant ≤ C) (hC96 : 96 ≤ C)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 65536)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (ha₃Net : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800)
    (ha : 0 < a) (haOne : a ≤ 1) (hσ : σ ≤ 1)
    (B Z₀ : ℝ) (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hNormTail : ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d => ¬RetainedCenteredNormBound I rows B) ≤
          1 / (n : ℝ) ^ 100) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          1 - 5 / (n : ℝ) ≤ uniformProbability (SourceStructuralKernel (d := d) L a I ζ) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 5, hNormTail,
    eventually_source_structural_kernel_failure_reduced_uniform hC hC96 ha₃ ha₃Small
      hEntropy ha₃Net ha haOne hσ B Z₀ hB hZ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hn hNorm hFailure hConditions
  intro d hBand L hL I hI ζ hShift
  have hCon := hConditions d hBand.1 hBand.2
  have hdn : d ≤ n := by have h := (source_kernel_dimension_twice_degree hCon).2.2; omega
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hBound := source_structural_failure_budget hn I ζ (hFailure d hBand L hL I hI ζ hShift)
    (hNorm d hBand L hL I hI)
  rw [uniformProbability_not] at hBound
  linarith only [hBound]

end CircularLaw
