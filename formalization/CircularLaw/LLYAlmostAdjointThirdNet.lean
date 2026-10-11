import CircularLaw.LLYAlmostSteepSplit
import CircularLaw.LLYFirstRadiusBudgets
import CircularLaw.LLYGradualRadiusBudgets

/-!
# The full almost-constant adjoint event with its third branch proved

The first and gradual probabilities are the already checked expansion
and column-load bounds. The actual third branch uses the constructed
mean-corrected finite net. Only the second-class probability remains
as an event term; all other inputs are deterministic parameter budgets.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem source_almost_adjoint_probability_with_lly_third_net {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hHalf : 2 * k₃ ≤ n) (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000)
    {A α ρ δ ε : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hρ : 0 ≤ ρ) (hDensity : α * n ≤ k₃)
    (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThirdRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hε : 0 ≤ ε) (hOutSize : (d : ℝ) * k₁ ≤ ε * n)
    (hOutBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hOutError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hBudget : llyThirdSteepNormConstant n d r * ((ρ / Real.sqrt n) * ρ / Real.sqrt n) +
      ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) α ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      (((((r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) +
          (n : ℝ) * Real.exp (-2 * sliceTailRate * d)) +
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llySecondAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ α ρ ((ρ / Real.sqrt n) * ρ / Real.sqrt n))) +
          ((n : ℝ) ^ (-A) +
            ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
              (meanCorrectedScalarNet k d (1 / 3) δ).card *
                ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
                  (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
                    Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n))) +
        (n : ℝ) * Real.exp (-(d : ℝ) / 72)) := by
  have hnPos : 0 < n := by omega
  have hdn : d ≤ n := by omega
  have hk₂n : k₂ ≤ n := by omega
  have hk₃n : k₃ ≤ n := by omega
  have hSpectral : ‖ζ‖ ≤ (d : ℝ) := hShift.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hThreshold := lly_gradual_radius_smallest_threshold hnPos hd hρ hRadius
  have hNonneg : 0 ≤ (ρ / Real.sqrt n) * ρ / Real.sqrt n := by positivity
  apply (source_almost_adjoint_probability_lly_split_preserving_almost ζ ℓ r k₁ k₂ k₃ α ρ _).trans
  exact add_le_add
    (add_le_add
      (add_le_add
        (lly_first_steep_adjoint_failure_probability_of_gradual_radius hnPos hd hdn hℓ hk₁ hk₁n
          hε hOutSize hOutBudget hOutError hStride hρ hRadius ζ hSpectral) le_rfl)
      (lly_third_almost_unit_adjoint_probability hn hd hDegree hk hk₁ hk₂ hk₃ hk₁n hRanks hHalf
        hFirstFit hA hDegreeLog hρ hDensity hThirdRadius hδ hδSmall hGrid hNonneg ζ hBudget))
    (lly_gradual_almost_adjoint_failure_probability hnPos hd hdn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hRanks
      hFirstFit hHalf (lly_first_rank_column_budget hd hk₁Small) hScale₂ hScale₃ hDensity hRadius
      hThreshold ζ hShift)

end CircularLaw
