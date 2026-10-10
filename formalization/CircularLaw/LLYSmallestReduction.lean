import CircularLaw.LLYAlmostAdjointReduction
import CircularLaw.LLYLeaveOneOutReduction
import CircularLaw.RowSliceNonAlmostMinimumBound
import CircularLaw.LLYGradualRadiusBudgets

/-!
# Actual minimum-value reduction with both gradual branches discharged

The scalar slice estimate, gradual adjoint exclusion and gradual
leave-one-out kernel exclusion are proved. Only the actual steep
adjoint and steep leave-one-out probabilities are retained as inputs.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem row_slice_smallest_probability_of_lly_steep_bounds {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hSize : 2 * d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ a η κ : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ)
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hSteepKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llySteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) ≤ η)
    (hSteepAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      (κ + (n : ℝ) * Real.exp (-(d : ℝ) / 72)) +
        (sliceSmallBallDegreeConstant δ / Real.sqrt d + η + Real.exp (-(rowLoadRate / 4) * n)) / δ := by
  have hdn : d ≤ n := by omega
  have hTop := lly_first_rank_column_budget hd hk₁Small
  have hThreshold := lly_gradual_radius_smallest_threshold (by omega : 0 < n) hd hρ.le hRadius
  have hKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) ≤
      η + Real.exp (-(rowLoadRate / 4) * n) := by
    intro i
    apply (source_leave_one_out_almost_kernel_probability_le_lly_steep hn hd hdn hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hk₁Small hScale₂ hScale₃ hDensity hRadius ha haOne hRank₂ hRank₃
      hEntropy0 hEntropy hDimension ζ hShift i).trans
    exact add_le_add (hSteepKernel i) (le_refl _)
  have hAlmost : uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ + (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
    apply (source_almost_adjoint_failure_probability_le_lly_steep (by omega) hd hdn hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hTop hScale₂ hScale₃ hDensity hRadius hThreshold ζ hShift).trans
    exact add_le_add hSteepAdjoint (le_refl _)
  simpa only [add_assoc] using
    row_slice_smallest_probability_of_almost_constant_bounds hd hSize ζ hδ hδOne hρ hKernel hAlmost

end CircularLaw
