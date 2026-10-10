import CircularLaw.MeanCorrectedScalarNet
import CircularLaw.RestrictedNormRetained

/-!
# Mean-corrected sparse nets for the retained right action

The centered part of a coordinate error pays the checked centered
operator norm. Its residual mean pays the deterministic row sum and
diagonal shift. The scalar grid is the same finite grid used for the
adjoint net, so its existing entropy and source budgets still apply.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem retained_shifted_slice_mean_corrected_error {n d : ℕ} (hn : 0 < n)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (ζ : ℂ) {B δ ε : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hNorm : RetainedCenteredNormBound I rows B)
    (x u : Fin n → ℂ) (c w : ℂ) (hBound : ∀ i, ‖x i - u i‖ ≤ δ)
    (hMean : ‖c + coordinateMean (fun i => x i - u i) - w‖ ≤ ε) :
    ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
        (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)))‖ ≤
      (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * ε := by
  let v : Fin n → ℂ := fun i => x i - u i
  let a := c + coordinateMean v - w
  have hDecomp : (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 (meanCenteredVector v) + WithLp.toLp 2 (fun _ => a) := by
    ext i
    change (x i + c) - (u i + w) = (x i - u i - coordinateMean v) + (c + coordinateMean v - w)
    ring
  have hCentered := retainedShiftedMatrix_zero_sum_norm_bound I ζ rows B hNorm
    (meanCenteredVector v) (meanCenteredVector_sum hn v)
  have hCenteredBudget := hCentered.trans
    (mul_le_mul_of_nonneg_left (meanCenteredVector_euclidean_bound hn v hδ hBound) (by positivity))
  have hConstant := retainedShiftedMatrix_l2_error I ζ rows (fun _ => a) hε
    (fun _ => hMean)
  have hConstantBudget : ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
      (WithLp.toLp 2 (fun _ => a))‖ ≤ (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * ε := by
    apply hConstant.trans
    have hFactor : (d : ℝ) + ‖ζ‖ ≤ B * Real.sqrt d + d + ‖ζ‖ := by
      linarith [mul_nonneg hB (Real.sqrt_nonneg d)]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFactor (Real.sqrt_nonneg n)) hε
    convert h using 1
    ring
  rw [hDecomp, map_add]
  exact (norm_add_le _ _).trans (add_le_add hCenteredBudget hConstantBudget)

theorem mean_corrected_scalar_net_retained_cover {n k d : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (ζ : ℂ) {B R δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hNorm : RetainedCenteredNormBound I rows B)
    (x u : Fin n → ℂ) (c : ℂ) (hCenter : ‖c‖ ≤ R) (hBound : ∀ i, ‖x i - u i‖ ≤ δ) :
    ∃ w ∈ meanCorrectedScalarNet k d R δ,
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
          (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)))‖ ≤
        (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
          (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d)) := by
  obtain ⟨w, hw, hMean⟩ := mean_corrected_scalar_net_cover hn hk hd x u c hCenter hBound
  exact ⟨w, hw, retained_shifted_slice_mean_corrected_error hn I rows ζ hB hδ
    (by positivity) hNorm x u c w hBound hMean⟩

end CircularLaw
