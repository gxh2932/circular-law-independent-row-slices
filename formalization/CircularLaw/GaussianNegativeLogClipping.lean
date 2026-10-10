import CircularLaw.GaussianGoodLogBounds
import CircularLaw.GaussianBottomLogRates
import CircularLaw.NegativeLogBottomClipping

/-!
# Gaussian negative logarithms are uniformly approximated by clipping

The exceptional smallest-value and simultaneous-quantile probabilities
vanish. The bottom entropy budget gives, for every tolerance, a fixed
cutoff whose negative-log clipping error tends to zero in probability.
Zero singular values are included in every error event.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem exists_gaussian_small_bottom_fraction {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 3 ∧ eta * (Real.log (16 / eta) + 1) < epsilon := by
  have hSmall := gaussian_bottom_entropy_small_fraction.eventually (gt_mem_nhds hEpsilon)
  have hUpper : ∀ᶠ eta : ℝ in 𝓝[>] 0, eta < 1 / 3 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3)).filter_mono nhdsWithin_le_nhds
  obtain ⟨eta, hPos, hUpper, hSmall⟩ :=
    (eventually_mem_nhdsWithin.and (hUpper.and hSmall)).exists
  exact ⟨eta, hPos, hUpper, hSmall⟩

theorem gaussian_good_negative_log_prefix_bound {n R : ℕ}
    (hn : 2 ≤ Nat.sqrt n) (hR : 2 * Nat.sqrt n < R)
    {eta : ℝ} (hEta : 0 < eta) (hEtaUpper : eta < 1 / 3)
    (hRatio : eta / 2 ≤ (R : ℝ) / n) (z : ℂ) (x : GaussianSquareSample n)
    (hGood : x ∉ gaussianUniformQuantileBad z n) (j : Fin n)
    (hj : j ∉ bottomLogIndices n R) :
    hermitizationNegativeLog
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j) ≤ Real.log (32 / eta) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le j.val).trans_lt j.isLt
  have hRank : R < n - j.val := by
    have hjN := j.isLt
    have hjPrefix : j.val < n - R := by
      simpa only [bottomLogIndices, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj
    omega
  have hLower : eta / 32 ≤
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j := by
    apply le_trans ?_ (gaussian_good_uniform_quantile_rank_lower hn z x hGood j (hR.trans hRank))
    have hRankR : (R : ℝ) ≤ ((n - j.val : ℕ) : ℝ) := by exact_mod_cast hRank.le
    have h := hRatio.trans (div_le_div_of_nonneg_right hRankR hnR.le)
    convert (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 16)) using 1 <;> ring
  have hLog := Real.log_le_log (div_pos hEta (by norm_num)) hLower
  rw [Real.log_div hEta.ne' (by norm_num : (32 : ℝ) ≠ 0)] at hLog
  change max (-Real.log (orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j)) 0 ≤ _
  apply max_le
  · rw [Real.log_div (by norm_num : (32 : ℝ) ≠ 0) hEta.ne']
    linarith
  · exact Real.log_nonneg ((le_div_iff₀ hEta).mpr (by linarith))

theorem gaussian_negative_log_clipping_error_threshold (z : ℂ)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ T0 : ℝ, 0 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      Tendsto (fun n => (gaussianSquareMatrixLaw n).real
        {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ∨
          epsilon < empiricalNonnegativeMean
            (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog -
            empiricalNonnegativeMean
              (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (clippedNegativeLog T)})
        atTop (𝓝 0) := by
  obtain ⟨eta, hEta, hEtaUpper, hEtaBudget⟩ := exists_gaussian_small_bottom_fraction hEpsilon
  let T0 := Real.log (32 / eta)
  have hT0 : 0 ≤ T0 := Real.log_nonneg ((le_div_iff₀ hEta).mpr (by linarith))
  refine ⟨T0, hT0, ?_⟩
  intro T hT
  have hBudget := (gaussian_bottom_log_budget_tendsto hEta).eventually (gt_mem_nhds hEtaBudget)
  have hRatio := (gaussian_quantile_deletion_ratio_tendsto hEta.le).eventually
    (lt_mem_nhds (by linarith : eta / 2 < eta))
  have hBad := (gaussian_smallest_polynomial_bad_probability_tendsto z).add
    (gaussian_uniform_quantile_bad_probability_tendsto z)
  simp only [add_zero] at hBad
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBad
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hBudget, hRatio, gaussian_sqrt_smaller_than_fixed_fraction hEta,
    gaussian_quantile_parameters_eventually hEta hEtaUpper,
    natural_sqrt_tendsto.eventually (eventually_ge_atTop 2)] with n hnBudget hnRatio hnRank hnParam hnSqrt
  have hn : 0 < n := by omega
  have hSubset : {x : GaussianSquareSample n |
        empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ∨
        epsilon < empiricalNonnegativeMean
          (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog -
          empiricalNonnegativeMean
            (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (clippedNegativeLog T)} ⊆
      gaussianSmallestPolynomialBad z n ∪ gaussianUniformQuantileBad z n := by
    intro x hx
    by_cases hMin : x ∈ gaussianSmallestPolynomialBad z n
    · exact Or.inl hMin
    by_cases hQuantile : x ∈ gaussianUniformQuantileBad z n
    · exact Or.inr hQuantile
    have hPos (j : Fin n) :
        0 < squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j := by
      exact_mod_cast gaussian_good_polynomial_singular_pos hn z x hMin j
    rcases hx with ⟨j, hj⟩ | hError
    · exact False.elim ((hPos j).ne' hj)
    · have hClip := empirical_negative_log_clipping_le_bottom
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hPos (hT0.trans hT)
        (fun j hj => (gaussian_good_negative_log_prefix_bound hnSqrt hnRank hEta hEtaUpper
          hnRatio.le z x hQuantile j hj).trans hT)
      have hBottom := gaussian_good_bottom_negative_log_bound hnSqrt
        (by omega : gaussianQuantileDeletion eta n ≤ n) z x hMin hQuantile
      change empiricalBottomNegativeLog
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
          (gaussianQuantileDeletion eta n) ≤ gaussianBottomLogBudget eta n at hBottom
      exact False.elim (not_lt_of_ge ((hClip.trans hBottom).trans hnBudget.le) hError)
  exact (measureReal_mono (μ := gaussianSquareMatrixLaw n) hSubset).trans (measureReal_union_le _ _)

end CircularLaw
