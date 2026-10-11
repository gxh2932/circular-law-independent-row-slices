import CircularLaw.CenteredSliceAdjointError
import CircularLaw.GridBox

/-!
# A finite scalar grid for arbitrary mean-corrected sparse approximations

Unlike ordinary floor errors, errors from truncating a sparse grid need
not have nonnegative components. A bounded complex grid box covers their
actual mean together with the constant center, at the finer resolution.
-/

noncomputable section
open Classical

namespace CircularLaw

def meanCorrectedScalarNet (k d : ℕ) (R δ : ℝ) : Finset ℂ :=
  gridBox (k * d) (gridBoxRadius (k * d) (R + δ))

theorem meanCorrectedScalarNet_card_le (k d : ℕ) (R δ : ℝ) :
    (meanCorrectedScalarNet k d R δ).card ≤
      (2 * gridBoxRadius (k * d) (R + δ) + 1) ^ 2 := gridBox_card_le _ _

theorem mean_corrected_scalar_net_cover {n k d : ℕ} (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (x u : Fin n → ℂ) (c : ℂ) {R δ : ℝ}
    (hCenter : ‖c‖ ≤ R) (hBound : ∀ i, ‖x i - u i‖ ≤ δ) :
    ∃ w ∈ meanCorrectedScalarNet k d R δ,
      ‖c + coordinateMean (fun i => x i - u i) - w‖ ≤ Real.sqrt 2 / ((k : ℝ) * d) := by
  let a := c + coordinateMean (fun i => x i - u i)
  have hRadius : ‖a‖ ≤ R + δ := (norm_add_le _ _).trans
    (add_le_add hCenter (coordinateMean_norm_le hn _ hBound))
  exact ⟨canonicalApprox (k * d) a, canonicalApprox_mem_gridBox a hRadius,
    by simpa only [Nat.cast_mul] using canonicalApprox_norm_error (Nat.mul_pos hk hd) a⟩

theorem mean_corrected_scalar_net_adjoint_cover {n k d : ℕ} (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (rows : RowSliceMatrix n d) (ζ : ℂ) {B R δ : ℝ} (hδ : 0 ≤ δ)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B)
    (x u : Fin n → ℂ) (c : ℂ) (hCenter : ‖c‖ ≤ R) (hBound : ∀ i, ‖x i - u i‖ ≤ δ) :
    ∃ w ∈ meanCorrectedScalarNet k d R δ,
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)))‖ ≤
        (B + ‖ζ‖) * (2 * Real.sqrt n * δ) +
          (B + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d)) := by
  obtain ⟨w, hw, hMean⟩ := mean_corrected_scalar_net_cover hn hk hd x u c hCenter hBound
  exact ⟨w, hw, shifted_slice_adjoint_mean_corrected_error hn rows ζ hδ hNorm x u c w hBound hMean⟩

end CircularLaw
