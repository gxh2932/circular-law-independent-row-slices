import CircularLaw.LLYSecondSourceProbability
import CircularLaw.LLYSecondAdjointDecay
import CircularLaw.LLYAlmostSteepSplit

/-!
# Arbitrary polynomial second-class adjoint failure at the actual source radius

Both the centered-operator exception and the first-rank exponential
remainder fit n^(-A). The almost-constant second-class event is a subset
of the unit-vector event, so its estimate has every probability input
proved and no separate deterministic budget left to discharge.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem two_shifted_polynomial_rates_le {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    2 * (n : ℝ) ^ (-(A + 1)) ≤ (n : ℝ) ^ (-A) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hPower : (n : ℝ) ^ (-(A + 1)) = (n : ℝ) ^ (-A) / n := by
    rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hnR, Real.rpow_neg_one]
    rfl
  rw [hPower, ← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  have hScaled := mul_le_mul_of_nonneg_right (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-A))
  nlinarith only [hScaled]

theorem eventually_lly_second_source_radius_probability_polynomial {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llySecondUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)) ≤ (n : ℝ) ^ (-A) := by
  have hCPos : 0 < C := by linarith
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_lly_second_source_radius_probability hC hAOne (by linarith : A + 1 + 3 ≤ 9 * C)
      ha₁ ha₁One ha₂,
    eventually_lly_source_first_rank_exponential_polynomial ha₁ hAOne]
      with n hn hDegrees hProbability hExponents
  intro d hLower hDegree ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hExp := hExponents d hd (by omega : d ≤ n)
  apply (hProbability d hLower hDegree ζ hShift).trans
  exact (by nlinarith only [hExp] :
    (n : ℝ) ^ (-(A + 1)) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) ≤
      2 * (n : ℝ) ^ (-(A + 1))).trans (two_shifted_polynomial_rates_le hn A)

theorem eventually_lly_second_almost_source_radius_probability_polynomial {C A a₁ a₂ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llySecondAlmostUnitAdjointFailure ζ rows (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂) α (llySourceAlmostRadius n d a₁)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)) ≤ (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_lly_second_source_radius_probability_polynomial hC hA hNormCost
    ha₁ ha₁One ha₂] with n hProbability
  intro d hLower hDegree ζ hShift
  apply (uniformProbability_mono ?_).trans (hProbability d hLower hDegree ζ hShift)
  intro rows hFail
  obtain ⟨x, hUnit, hx, _, hSmall⟩ := hFail
  exact ⟨x, hUnit, hx, hSmall⟩

end CircularLaw
