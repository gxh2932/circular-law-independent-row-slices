import CircularLaw.LLYSecondApproximationBudgets
import CircularLaw.LLYSourceRadius

/-!
# The actual second steep adjoint probability at the source parameters

The rounded source ranks discharge rare density, row conditioning,
finite-net entropy and centered approximation. If their order does not
permit the second class, that class is empty. The checked third-class
radius also supplies the second-class unit residual budget.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_second_steep_empty_of_reversed_ranks {n d ℓ r k₁ k₂ : ℕ}
    (hd : 0 < d) (hk₂ : 0 < k₂) (hRanks : k₂ ≤ k₁) (hk₁n : k₁ ≤ n)
    (x : Fin n → ℂ) : x ∉ llySecondSteep d ℓ r k₁ k₂ := by
  intro hx
  have hOrder := orderedNormAt_antitone x hk₂ hRanks hk₁n
  have hPow : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_right hPow (orderedNormAt_nonneg x k₂)
  have hGap := hx.2
  nlinarith only [hOrder, hScaled, hGap]

theorem eventually_lly_second_source_adjoint_probability {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
          llyThirdNetError d * Real.sqrt n →
            ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
              uniformProbability (fun rows : RowSliceMatrix n d =>
                llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
                  (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
                  ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
                    (n : ℝ) ^ (-A) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 3600,
    eventually_lly_second_source_grid_adjoint_error_small hCPos
      (rowSliceComplexNormConstant_nonneg hA) ha₁,
    eventually_lly_second_source_net_count_absorbed hC ha₁ ha₂,
    eventually_degree_property_uniform hCPos eventually_rare_row_slice_conditioning_cost,
    eventually_degree_property_uniform hCPos
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) (4096 * a₂)),
    eventually_lly_source_second_rank_size_uniform ha₂]
      with n hn hApproximations hCounts hConditioning hPowers hSizes
  intro d hLower hDegree ρ hρ hRadius ζ hShift
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
  have hk₂n : llySourceSecondRank n d a₂ ≤ n := by
    have hReal : (llySourceSecondRank n d a₂ : ℝ) ≤ n := by
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hReal
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
          ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
            (2 * Real.sqrt n * llyThirdNetError d) +
              (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
                (Real.sqrt 2 / ((llyThirdNetResolution d : ℝ) * d))) ≤
                  Real.sqrt ((llySourceFirstRank n d a₁ : ℝ) * d) / 30 := by linarith
    have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
      have hScaled := mul_le_mul_of_nonneg_right hNormCost (Real.log_natCast_nonneg n)
      nlinarith
    exact lly_second_unit_adjoint_probability_absorbed hnTwo hd hDegree
      (by have h := lly_source_stride_ge_two hnTwo hd hC hLower; omega)
      (llyThirdNetResolution_pos hd) hk₁ hRanks hRanksFit
      (lly_source_scale_ranks hnTwo hd hC hLower ha₁).2 hRare (hConditioning d hLower).2
      hA hDegreeLog (by unfold llyThirdNetError; positivity)
      (by linarith : llyThirdNetError d < 1 / 3) (llyThirdNetResolution_error hd) le_rfl
      (by positivity : 0 ≤ (ρ / Real.sqrt n) * ρ / Real.sqrt n) ζ hBudget (hCounts d hLower)
  · have hEmpty : ∀ rows : RowSliceMatrix n d,
        ¬llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
          (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
          ((ρ / Real.sqrt n) * ρ / Real.sqrt n) := by
      intro rows hFail
      obtain ⟨x, _, hx, _⟩ := hFail
      exact lly_second_steep_empty_of_reversed_ranks hd hk₂ (by omega) hk₁n _ hx
    letI : IsEmpty {rows : RowSliceMatrix n d //
      llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
        (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} := ⟨fun rows => hEmpty rows.val rows.property⟩
    have hZero : uniformProbability (fun rows : RowSliceMatrix n d =>
        llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
          (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
          ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) = 0 := by simp [uniformProbability]
    rw [hZero]
    positivity

theorem eventually_lly_second_source_radius_probability {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)) ≤
                (n : ℝ) ^ (-A) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_lly_second_source_adjoint_probability hC hA hNormCost ha₁ ha₁One ha₂]
      with n hn hDegrees hProbability
  intro d hLower hDegree ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  exact hProbability d hLower hDegree (llySourceAlmostRadius n d a₁)
    (lly_source_almost_radius_pos hn hd a₁).le (lly_source_almost_radius_third hn hd a₁) ζ hShift

end CircularLaw
