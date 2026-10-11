import CircularLaw.LLYFirstSteepAdjoint
import CircularLaw.LLYMinimumFirstSteepReduction
import CircularLaw.LLYFirstRadiusBudgets

/-!
# Actual minimum-value reduction with both first-steep actions proved

Only the second/third right-kernel and second/third adjoint probability
estimates remain as inputs. All first-steep witness, expansion and column
degree failure terms are proved and charged explicitly.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyLaterSteepAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ k₃ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
      (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ τ

theorem lly_steep_adjoint_failure_split {n d ℓ r k₁ k₂ k₃ : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (τ : ℝ)
    (hFail : llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ) :
    llyFirstSteepAdjointFailure ζ rows ℓ r k₁ τ ∨
      llyLaterSteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ := by
  obtain ⟨x, hUnit, hSteep, hSmall⟩ := hFail
  rcases hSteep with (hFirst | hSecond) | hThird
  · exact Or.inl ⟨x, hUnit, hFirst, hSmall⟩
  · exact Or.inr ⟨x, hUnit, Or.inl hSecond, hSmall⟩
  · exact Or.inr ⟨x, hUnit, Or.inr hThird, hSmall⟩

theorem lly_steep_adjoint_probability_le_later {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n)
    {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k₁ ≤ ε * n)
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) {τ : ℝ}
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    uniformProbability (fun rows : RowSliceMatrix n d => llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ) ≤
      ((r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) + (n : ℝ) * Real.exp (-2 * sliceTailRate * d)) +
        uniformProbability (fun rows : RowSliceMatrix n d => llyLaterSteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ τ) := by
  apply (uniformProbability_mono (fun rows hFail => lly_steep_adjoint_failure_split ζ rows τ hFail)).trans
    ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add (lly_first_steep_adjoint_failure_probability hn hd hdn hℓ hk₁ hk₁n hε hSize hBudget
    hError hStride ζ hSpectral hThreshold) (le_refl _)

theorem lly_steep_adjoint_probability_le_later_of_gradual_radius {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n)
    {ε ρ : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k₁ ≤ ε * n)
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (hρ : 0 ≤ ρ) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      ((r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) + (n : ℝ) * Real.exp (-2 * sliceTailRate * d)) +
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyLaterSteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) := by
  apply (uniformProbability_mono (fun rows hFail =>
    lly_steep_adjoint_failure_split ζ rows _ hFail)).trans ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add (lly_first_steep_adjoint_failure_probability_of_gradual_radius hn hd hdn hℓ hk₁ hk₁n
    hε hSize hBudget hError hStride hρ hRadius ζ hSpectral) (le_refl _)

theorem row_slice_smallest_probability_of_lly_second_third_bounds {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hSize : 2 * d ≤ n) (hℓ : 0 < ℓ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ a η κ ε : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ)
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (hFirstBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (hε : 0 ≤ ε) (hOutSize : (d : ℝ) * k₁ ≤ ε * n)
    (hOutBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hOutError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hLaterKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llyLaterSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) ≤ η)
    (hLaterAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llyLaterSteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      ((((r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) +
          (n : ℝ) * Real.exp (-2 * sliceTailRate * d)) + κ) + (n : ℝ) * Real.exp (-(d : ℝ) / 72)) +
        (sliceSmallBallDegreeConstant δ / Real.sqrt d +
          ((r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) + η) +
          Real.exp (-(rowLoadRate / 4) * n)) / δ := by
  have hdn : d ≤ n := by omega
  have hSpectral : ‖ζ‖ ≤ (d : ℝ) := hShift.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  apply row_slice_smallest_probability_of_lly_later_bounds hn hd hSize hℓ hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    hk₂₃ hFit hHalf hk₁Small hScale₂ hScale₃ hδ hδOne hρ hDensity hRadius ha haOne hRank₂ hRank₃
    hEntropy0 hEntropy hDimension hFirstBudget ζ hShift hLaterKernel ?_
  exact (lly_steep_adjoint_probability_le_later_of_gradual_radius (by omega : 0 < n) hd hdn hℓ hk₁ hk₁n
    hε hOutSize hOutBudget hOutError hStride hρ.le hRadius ζ hSpectral).trans
    (add_le_add (le_refl _) hLaterAdjoint)

end CircularLaw
