import CircularLaw.BernoulliSteepUnitProbability
import CircularLaw.LLYSecondSourcePolynomial
import CircularLaw.LLYThirdSourceKernelProbability

/-!
# Later Bernoulli steep classes at the literal manuscript parameters

The rounded source ranks, approximation grids, scalar nets and spectral
window discharge every deterministic input to the two Bernoulli estimates.
The retained-set quantifier includes the full matrix and every one-row
deletion. Reversed second-class ranks are handled by their actual emptiness.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem eventually_bernoulli_second_source_retained_probability {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
          llyThirdNetError d * Real.sqrt n →
            ∀ I : Finset (Fin n), (4 / 5 : ℝ) * n ≤ I.card →
              ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
                (sparseBernoulliMatrixLaw n d).real {sample |
                  BernoulliSecondUnitRetainedFailure (d := d) I ζ sample
                    (llySourceStride n d) (llySourceScale n d a₁)
                    (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
                    ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤
                      (n : ℝ) ^ (-A) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 3600,
    eventually_lly_second_source_grid_adjoint_error_small hCPos
      (bernoulli_complex_norm_constant_nonneg hA) ha₁,
    eventually_lly_second_source_net_count_absorbed hC ha₁ ha₂,
    eventually_degree_property_uniform hCPos
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) (4096 * a₂)),
    eventually_lly_source_second_rank_size_uniform ha₂]
      with n hn hApproximations hCounts hPowers hSizes
  intro d hLower hDegree ρ hρ hRadius I hRows ζ hShift
  have hnTwo : 2 ≤ n := by omega
  have hdn : d ≤ n := by omega
  obtain ⟨hd, hδSmall, hErrors⟩ := hApproximations d hLower hdn
  have hk₁ := lly_source_first_rank_pos hnTwo hd ha₁
  have hk₁n := lly_source_first_rank_le_dimension hnTwo hd ha₁.le ha₁One (by linarith) hLower
  have hSecondSize := hSizes d hd hdn
  have hk₂ : 0 < llySourceSecondRank n d a₂ := by
    have hLowerSecond := lly_source_second_rank_density_lower hSecondSize
    have hReal : (0 : ℝ) < llySourceSecondRank n d a₂ := by linarith
    exact_mod_cast hReal
  have hSecondHalf := lly_source_second_rank_small_density (n := n) hd ha₂.le (hPowers d hLower)
  by_cases hRanks : llySourceFirstRank n d a₁ ≤ llySourceSecondRank n d a₂
  · have hRare := lly_source_first_rank_rare_density hnTwo hd hDegree hC hLower ha₁ ha₁One
    have hFirstDegree : (llySourceFirstRank n d a₁ : ℝ) * d ≤ (n : ℝ) / 2 := by
      rw [← mul_div_assoc] at hRare
      have h := (div_le_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mp hRare
      linarith
    have hFirstHalf : (llySourceFirstRank n d a₁ : ℝ) ≤ (n : ℝ) / 2 := by
      have h := mul_le_mul_of_nonneg_left (by exact_mod_cast hd : (1 : ℝ) ≤ d)
        (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁))
      linarith
    have hRanksFit : llySourceSecondRank n d a₂ + llySourceFirstRank n d a₁ ≤ n := by
      have hReal : (llySourceSecondRank n d a₂ : ℝ) + llySourceFirstRank n d a₁ ≤ n := by
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact_mod_cast hReal
    have hSecondRadius : llySecondSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
        llyThirdNetError d * Real.sqrt n :=
      (mul_le_mul_of_nonneg_right (lly_second_norm_constant_le_third hd) hρ).trans hRadius
    have hUnitBudget := lly_second_radius_unit_image_budget hn hd hk₁ hρ
      (by linarith : llyThirdNetError d ≤ 1) hSecondRadius
    have hErrorBudget := hErrors ζ hShift
    have hBudget : llySecondSteepNormConstant n d (llySourceScale n d a₁) *
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n) +
          ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
            (2 * Real.sqrt n * llyThirdNetError d) +
              (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
                (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤
                  Real.sqrt ((llySourceFirstRank n d a₁ : ℝ) * d) / 30 := by linarith
    have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
      have hScaled := mul_le_mul_of_nonneg_right hNormCost (Real.log_natCast_nonneg n)
      nlinarith
    exact bernoulli_second_unit_retained_probability_absorbed hnTwo hd hdn
      (by have h := lly_source_stride_ge_two hnTwo hd hC hLower; omega)
      (llyThirdNetResolution_pos hd) hk₁ hRanks hRanksFit
      (lly_source_scale_ranks hnTwo hd hC hLower ha₁).2 hRare
      hA hDegreeLog (by unfold llyThirdNetError; positivity)
      (by linarith : llyThirdNetError d < 1 / 3) (llyThirdNetResolution_error hd) le_rfl
      (by positivity : 0 ≤ (ρ / Real.sqrt n) * ρ / Real.sqrt n) I hRows ζ hBudget (hCounts d hLower)
  · have hEvent : {sample : BernoulliSquareSample n |
        BernoulliSecondUnitRetainedFailure (d := d) I ζ sample
          (llySourceStride n d) (llySourceScale n d a₁)
          (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
          ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hFail
      obtain ⟨x, _, hx, _⟩ := hFail
      exact lly_second_steep_empty_of_reversed_ranks hd hk₂ (by omega) hk₁n _ hx
    rw [hEvent, measureReal_empty]
    positivity

theorem eventually_bernoulli_third_source_retained_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
          llyThirdNetError d * Real.sqrt n →
            ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
              ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
                (sparseBernoulliMatrixLaw n d).real {sample |
                  BernoulliThirdUnitRetainedFailure (d := d) I ζ sample
                    (llySourceStride n d) (llySourceScale n d a₁)
                    (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
                    (llySourceThirdRank n a₃) α ρ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤
                      (n : ℝ) ^ (-A) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 12,
    eventually_lly_source_rank_validity hC ha₁ ha₁One ha₂ ha₃ (by linarith : a₃ ≤ 1 / 2),
    eventually_lly_third_source_retained_net_probability_cost hC ha₁.le ha₁One ha₂ ha₃.le ha₃Small hFirstCost,
    eventually_degree_property_uniform hCPos
      (eventually_lly_third_unit_net_approximation_budget (bernoulli_complex_norm_constant_nonneg hA)),
    eventually_lly_source_third_rank_density ha₃ hα]
      with n hn hRanks hCosts hBudgets hDensity
  intro d hLower hDegree ρ hρ hRadius I hRows ζ hShift
  have hdn : d ≤ n := by omega
  obtain ⟨hd, _, hk₁, hk₁n, hk₂, hk₃, hRanks, hHalf⟩ := hRanks d hLower hdn
  obtain ⟨hScaleLower, hScaleFit⟩ := lly_source_scale_ranks (by omega : 2 ≤ n) hd hC hLower ha₁
  obtain ⟨_, hδSmall, hBudgets⟩ := hBudgets d hLower
  have hδ : 0 ≤ llyThirdNetError d := by unfold llyThirdNetError; positivity
  have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
    have hScaled := mul_le_mul_of_nonneg_right hNormCost
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))
    nlinarith
  have hProbability := bernoulli_third_unit_retained_probability (by omega : 2 ≤ n) hd hDegree
    (llyThirdNetResolution_pos hd) hk₁ hk₂ hk₃ hk₁n hRanks hHalf
    (by omega : llySourceThirdRank n a₃ + llySourceSecondRank n d a₂ ≤ n) hScaleFit hA hDegreeLog
    hρ (by positivity : 0 ≤ (ρ / Real.sqrt n) * ρ / Real.sqrt n) hDensity hRadius
    hδ hδSmall (llyThirdNetResolution_error hd) I hRows ζ
    (hBudgets n (llySourceScale n d a₁) hn ρ hρ hRadius ζ hShift)
  exact hProbability.trans (add_le_add le_rfl (hCosts d (llySourceScale n d a₁) hLower hdn hScaleLower I hRows))

end CircularLaw
