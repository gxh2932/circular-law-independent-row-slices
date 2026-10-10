import CircularLaw.HermitizationCutoffBudgets
import CircularLaw.RowRestrictionVolumeProbability

/-!
# Actual prefix comparison in probability at both manuscript cutoffs

The retained rows are the first n-ceil(n/d^a) rows of each independently
sampled shifted square matrix. The regularized comparison limit is
proved. Removing regularization requires the literal joint minimum
failure probability, which remains explicit.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

def hermitizationPrefixEmbedding (n d : ℕ) (a : ℝ) :
    Fin (n - hermitizationDeletionCount n d a) ↪ Fin n :=
  Fin.castLEEmb (Nat.sub_le n _)

def independentPrefixPotentialDifference (n d : ℕ) (a : ℝ) (ζ : ℂ) (η : ℝ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) : ℝ :=
  (regularizedRowPotential
      (matrixRowRestriction (fullShiftedSliceMatrix ζ samples.1) (hermitizationPrefixEmbedding n d a)) η -
    regularizedRowPotential
      (matrixRowRestriction (bernoulliSquareMatrix samples.2 - ζ • 1) (hermitizationPrefixEmbedding n d a)) η) / n

def independentPrefixVolumeDifference (n d : ℕ) (a : ℝ) (ζ : ℂ)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) : ℝ :=
  (matrixRowLogVolume
      (matrixRowRestriction (fullShiftedSliceMatrix ζ samples.1) (hermitizationPrefixEmbedding n d a)) -
    matrixRowLogVolume
      (matrixRowRestriction (bernoulliSquareMatrix samples.2 - ζ • 1) (hermitizationPrefixEmbedding n d a))) / n

def independentSquareMinimumFailure (n d : ℕ) (ζ : ℂ) (τ : ℝ) :
    Set (RowSliceMatrix n d × BernoulliSquareSample n) :=
  {samples | ¬((∀ j, τ ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ samples.1) j) ∧
    (∀ j, τ ≤ orderedSquareSingularValues (bernoulliSquareMatrix samples.2 - ζ • 1) j))}

theorem independent_prefix_potential_comparison_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) (ζ : ℕ → ℂ) (η : ℕ → ℝ)
    (hη : ∀ᶠ n in atTop, 0 < η n)
    (hError : Tendsto (fun n => rowReplacementErrorBound n (d n)
      (n - hermitizationDeletionCount n (d n) a) (η n) ‖ζ n‖) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) a (ζ n) (η n)) 0 := by
  intro ε hε
  have hUpper := hError.div_const ε
  simp only [zero_div] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hη, eventually_valid_bernoulli_degrees hDegree hSparse,
    eventually_hermitization_deletion_valid d hDegree hSparse ha haOne.le,
    eventually_hermitization_row_comparison_Q_ge_one d hDegree hSparse ha haOne] with n hηn hd hr hQ
  have hkn : n - hermitizationDeletionCount n (d n) a < n := by omega
  have h := independent_square_prefix_probability_comparison hd.1 hd.2 hr.2.2 hkn
    (hermitizationPrefixEmbedding n (d n) a) (ζ n) hηn hQ hε
  have hnReal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simpa only [independentPrefixPotentialDifference, sub_zero, abs_div,
    abs_of_nonneg hnReal] using h

theorem lower_cutoff_prefix_potential_comparison (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {C CL : ℝ} (hC : 0 < C) (hCL : 0 ≤ CL) (hLower : LogLowerBound C d) (z : ℂ) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) (1 / 2)
        (z * (Real.sqrt (d n : ℝ) : ℂ)) (lowerHermitizationCutoff n CL / n)) 0 := by
  have hDegree : Tendsto d atTop atTop :=
    tendsto_natCast_atTop_iff.mp (degree_tendsto_atTop_of_log_lower_bound hC d hLower)
  have hLogN : ∀ᶠ n : ℕ in atTop, Real.log n ≤ C⁻¹ * d n := by
    filter_upwards [hLower] with n hn
    have h : Real.log n ≤ (d n : ℝ) / C := (le_div_iff₀ hC).mpr (by nlinarith only [hn])
    simpa only [div_eq_mul_inv, mul_comm] using h
  apply independent_prefix_potential_comparison_converges d hDegree hSparse
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) (fun n => lowerHermitizationCutoff n CL / n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (Real.rpow_pos_of_pos hnR _) hnR
  · simpa only [shifted_sqrt_degree_norm] using
      lower_cutoff_replacement_error_tendsto_zero d hDegree hSparse z (inv_nonneg.mpr hC.le) hCL
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hLogN

theorem polynomial_cutoff_prefix_potential_comparison (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {C B ε : ℝ} (hC : 0 < C) (hB : 0 ≤ B) (hε : 0 < ε) (hLower : LogLowerBound C d) (z : ℂ) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) (superlogHermitizationExponent ε)
        (z * (Real.sqrt (d n : ℝ) : ℂ)) (polynomialHermitizationCutoff n B / n)) 0 := by
  have hDegree : Tendsto d atTop atTop :=
    tendsto_natCast_atTop_iff.mp (degree_tendsto_atTop_of_log_lower_bound hC d hLower)
  have hLogN : ∀ᶠ n : ℕ in atTop, Real.log n ≤ C⁻¹ * d n := by
    filter_upwards [hLower] with n hn
    have h : Real.log n ≤ (d n : ℝ) / C := (le_div_iff₀ hC).mpr (by nlinarith only [hn])
    simpa only [div_eq_mul_inv, mul_comm] using h
  obtain ⟨ha, haOne⟩ := superlog_hermitization_exponent_range hε
  apply independent_prefix_potential_comparison_converges d hDegree hSparse ha haOne
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) (fun n => polynomialHermitizationCutoff n B / n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (Real.rpow_pos_of_pos hnR _) hnR
  · simpa only [shifted_sqrt_degree_norm] using
      polynomial_cutoff_replacement_error_tendsto_zero d hDegree hSparse z (inv_nonneg.mpr hC.le) hB
        ha haOne hLogN

theorem log_lower_bound_of_superlog_degree (d : ℕ → ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) :
    LogLowerBound 1 d := by
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [hLower, hLog] with n hd hn
  have hPower : Real.log n ≤ Real.rpow (Real.log n) (1 + ε) := by
    simpa only [Real.rpow_one, Real.rpow_eq_pow] using
      Real.rpow_le_rpow_of_exponent_le hn (show (1 : ℝ) ≤ 1 + ε by linarith)
  simpa only [one_mul] using hPower.trans hd

theorem superlog_cutoff_prefix_potential_comparison (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) (z : ℂ) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) (superlogHermitizationExponent ε)
        (z * (Real.sqrt (d n : ℝ) : ℂ)) (polynomialHermitizationCutoff n B / n)) 0 := by
  exact polynomial_cutoff_prefix_potential_comparison d hSparse zero_lt_one hB hε
    (log_lower_bound_of_superlog_degree d hε.le hLower) z

theorem independent_prefix_volume_comparison_of_minimum_failure (d : ℕ → ℕ)
    (a : ℝ) (ζ : ℕ → ℂ) (τ : ℕ → ℝ) (hτ : ∀ᶠ n in atTop, 0 < τ n)
    (hRegularized : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) a (ζ n) (τ n / n)) 0)
    (hBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (ζ n) (τ n))) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixVolumeDifference n (d n) a (ζ n)) 0 := by
  exact row_restriction_volume_comparison_converges
    (fun n => independentSquareComparisonLaw n (d n))
    (fun n => n - hermitizationDeletionCount n (d n) a)
    (fun n samples => fullShiftedSliceMatrix (ζ n) samples.1)
    (fun n samples => bernoulliSquareMatrix samples.2 - ζ n • 1)
    (fun n => hermitizationPrefixEmbedding n (d n) a) τ hτ hRegularized hBad

theorem lower_hermitization_deletion_count (n d : ℕ) :
    hermitizationDeletionCount n d (1 / 2) = ⌈(n : ℝ) / Real.sqrt d⌉₊ := by
  simp only [hermitizationDeletionCount, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]

end CircularLaw
