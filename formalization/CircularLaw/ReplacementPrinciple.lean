import CircularLaw.BLProbabilityConvergence

/-!
# The replacement principle in probability

The actual energy and almost-everywhere shifted-log-determinant
hypotheses imply convergence of the full bounded-Lipschitz distance.
The combined Hilbert--Schmidt hypothesis and the classical sqrt(n)
normalization are included. No circular-law or test-convergence result
is supplied as an assumption.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology ENNReal

namespace CircularLaw

theorem matrix_replacement_principle {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))}) atTop (𝓝 0) := by
  intro ε hε
  apply bounded_lipschitz_convergence_of_compact_C2_tests μ A B hEnergyA hEnergyB _ hε
  intro φ hφ hSupport
  exact replacement_compact_C2_test_convergence μ A B hA hB hEnergyA hEnergyB hLog φ hφ hSupport

theorem matrix_replacement_principle_combined_energy {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergy : VaryingBoundedInProbability μ
      (fun n ω => (squareMatrixEnergy (A n ω) + squareMatrixEnergy (B n ω)) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))}) atTop (𝓝 0) := by
  have hEA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n) := by
    apply varying_bounded_probability_of_abs_le μ hEnergy
    apply Eventually.of_forall
    intro n ω
    have hA0 := div_nonneg (squareMatrixEnergy_nonneg (A n ω)) (Nat.cast_nonneg n)
    have hB0 := div_nonneg (squareMatrixEnergy_nonneg (B n ω)) (Nat.cast_nonneg n)
    rw [add_div, abs_of_nonneg hA0, abs_of_nonneg (add_nonneg hA0 hB0)]
    linarith
  have hEB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n) := by
    apply varying_bounded_probability_of_abs_le μ hEnergy
    apply Eventually.of_forall
    intro n ω
    have hA0 := div_nonneg (squareMatrixEnergy_nonneg (A n ω)) (Nat.cast_nonneg n)
    have hB0 := div_nonneg (squareMatrixEnergy_nonneg (B n ω)) (Nat.cast_nonneg n)
    rw [add_div, abs_of_nonneg hB0, abs_of_nonneg (add_nonneg hA0 hB0)]
    linarith
  exact matrix_replacement_principle μ A B hA hB hEA hEB hLog

def entryNormalizedComplexMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (↑(Real.sqrt n) : ℂ)⁻¹ • A

theorem entry_normalized_matrix_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    squareMatrixEnergy (entryNormalizedComplexMatrix A) / n = squareMatrixEnergy A / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [entryNormalizedComplexMatrix, squareMatrixEnergy_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp

theorem classical_matrix_replacement_principle {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergy : VaryingBoundedInProbability μ
      (fun n ω => (squareMatrixEnergy (A n ω) + squareMatrixEnergy (B n ω)) / (n : ℝ) ^ 2))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (entryNormalizedComplexMatrix (A n ω)) z -
        normalizedLogDeterminant (entryNormalizedComplexMatrix (B n ω)) z) 0) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (entryNormalizedComplexMatrix (A n ω)))
        (empiricalSpectralMeasure (entryNormalizedComplexMatrix (B n ω)))}) atTop (𝓝 0) := by
  apply matrix_replacement_principle_combined_energy μ
    (fun n ω => entryNormalizedComplexMatrix (A n ω))
    (fun n ω => entryNormalizedComplexMatrix (B n ω))
  · intro n
    simpa only [entryNormalizedComplexMatrix] using
      (hA n).const_smul ((↑(Real.sqrt n) : ℂ)⁻¹)
  · intro n
    simpa only [entryNormalizedComplexMatrix] using
      (hB n).const_smul ((↑(Real.sqrt n) : ℂ)⁻¹)
  · have hEq : (fun n ω => (squareMatrixEnergy (entryNormalizedComplexMatrix (A n ω)) +
        squareMatrixEnergy (entryNormalizedComplexMatrix (B n ω))) / n) =
        (fun n ω => (squareMatrixEnergy (A n ω) + squareMatrixEnergy (B n ω)) / (n : ℝ) ^ 2) := by
      funext n ω
      rw [add_div, entry_normalized_matrix_energy, entry_normalized_matrix_energy, add_div]
    rw [hEq]
    exact hEnergy
  · exact hLog

end CircularLaw
