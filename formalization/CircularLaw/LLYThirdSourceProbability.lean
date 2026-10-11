import CircularLaw.LLYSourceRankValidity
import CircularLaw.LLYSourceScale
import CircularLaw.LLYThirdApproximationBudgets

/-!
# Third steep almost-constant adjoint bound at the literal source parameters

The actual rounded ranks and integer scale discharge the net entropy,
conditioning cost, rank validity and approximation budgets uniformly.
The only remaining radius condition is the explicit normalization radius
needed by the unit-vector event, handled by the subsequent radius choice.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_lly_source_third_rank_density {a α : ℝ}
    (ha : 0 < a) (hα : α ≤ a / 2) :
    ∀ᶠ n : ℕ in atTop, α * n ≤ llySourceThirdRank n a := by
  filter_upwards [(tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (2 / a)] with n hn
  have hSize : 2 ≤ a * n := by
    have h := (div_le_iff₀ ha).mp hn
    nlinarith
  have hLower := lly_source_third_rank_density_lower hSize
  have hScaled := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem eventually_lly_third_source_adjoint_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
          llyThirdNetError d * Real.sqrt n →
            ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
              uniformProbability (fun rows : RowSliceMatrix n d =>
                llyThirdAlmostUnitAdjointFailure ζ rows (llySourceStride n d)
                  (llySourceScale n d a₁) (llySourceFirstRank n d a₁)
                  (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) α ρ
                  ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
                    (n : ℝ) ^ (-A) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 12,
    eventually_lly_source_rank_validity hC ha₁ ha₁One ha₂ ha₃ (by linarith : a₃ ≤ 1 / 2),
    eventually_lly_third_source_net_probability_cost hC ha₁.le ha₁One ha₂ ha₃.le ha₃Small hFirstCost,
    eventually_degree_property_uniform hCPos
      (eventually_lly_third_unit_net_approximation_budget (rowSliceComplexNormConstant_nonneg hA)),
    eventually_lly_source_third_rank_density ha₃ hα]
      with n hn hRanks hCosts hBudgets hDensity
  intro d hLower hDegree ρ hρ hRadius ζ hShift
  have hdn : d ≤ n := by omega
  obtain ⟨hd, _, hk₁, hk₁n, hk₂, hk₃, hRanks, hHalf⟩ := hRanks d hLower hdn
  obtain ⟨hScaleLower, hScaleFit⟩ := lly_source_scale_ranks (by omega : 2 ≤ n) hd hC hLower ha₁
  obtain ⟨_, hδSmall, hBudgets⟩ := hBudgets d hLower
  have hδ : 0 ≤ llyThirdNetError d := by unfold llyThirdNetError; positivity
  have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
    have hScaled := mul_le_mul_of_nonneg_right hNormCost
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))
    nlinarith
  have hProbability := lly_third_almost_unit_adjoint_probability (by omega : 2 ≤ n) hd hDegree
    (llyThirdNetResolution_pos hd) hk₁ hk₂ hk₃ hk₁n hRanks hHalf hScaleFit hA hDegreeLog
    hρ hDensity hRadius hδ hδSmall (llyThirdNetResolution_error hd)
    (by positivity : 0 ≤ (ρ / Real.sqrt n) * ρ / Real.sqrt n) ζ
    (hBudgets n (llySourceScale n d a₁) hn ρ hρ hRadius ζ hShift)
  apply hProbability.trans
  exact add_le_add le_rfl (hCosts d (llySourceScale n d a₁) hLower hdn hScaleLower)

end CircularLaw
