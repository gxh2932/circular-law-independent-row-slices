import CircularLaw.LLYSmallestReduction
import CircularLaw.LLYFirstSteepProbability
import CircularLaw.LLYFirstWitnessBudgets

/-!
# Minimum-value reduction after first-steep right-kernel exclusion

Both gradual branches and the first steep right-kernel class are proved.
Only the second/third right-kernel classes and the steep adjoint event
remain probability inputs. The exact floor rank discharges the witness
size budget rather than introducing another hypothesis.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem row_slice_smallest_probability_of_lly_later_bounds {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hSize : 2 * d ≤ n) (hℓ : 0 < ℓ)
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
    (hFirstBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hLaterKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llyLaterSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) ≤ η)
    (hSteepAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llySteepAdjointFailure ζ rows ℓ r k₁ k₂ k₃ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      (κ + (n : ℝ) * Real.exp (-(d : ℝ) / 72)) +
        (sliceSmallBallDegreeConstant δ / Real.sqrt d +
          ((r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) + η) +
          Real.exp (-(rowLoadRate / 4) * n)) / δ := by
  have hdn : d ≤ n := by omega
  have hSpectral : ‖ζ‖ ≤ (d : ℝ) := hShift.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  apply row_slice_smallest_probability_of_lly_steep_bounds hn hd hSize hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hk₁Small hScale₂ hScale₃ hδ hδOne hρ hDensity hRadius
    ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension ζ hShift ?_ hSteepAdjoint
  intro i
  exact (lly_steep_leave_one_out_probability_le_later hn hd hdn hℓ hk₁ hk₁n
    (lly_first_rank_witness_budget hd hk₁Small) hFirstBudget ζ hSpectral i).trans
    (add_le_add (le_refl _) (hLaterKernel i))

end CircularLaw
