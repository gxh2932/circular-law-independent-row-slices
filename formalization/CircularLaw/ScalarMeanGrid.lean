import CircularLaw.CenteredCanonicalApproximation

/-!
# The scalar grid for the mean rounding error

The actual canonical mean lies in the half-open square `[0,1/k)^2`.
Floor rounding at resolution `1/(k*d)` therefore uses the image of
exactly `d^2` index pairs and has error at most `sqrt(2)/(k*d)`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def scalarMeanGrid (k d : ℕ) : Finset ℂ :=
  ((Finset.range d) ×ˢ (Finset.range d)).image
    (fun ab => gridValue (k * d) (ab.1 : ℤ) (ab.2 : ℤ))

theorem scalarMeanGrid_card_le (k d : ℕ) : (scalarMeanGrid k d).card ≤ d ^ 2 := by
  calc
    _ ≤ ((Finset.range d) ×ˢ (Finset.range d)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_range, pow_two]

theorem fine_floor_index_range {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    {z : ℝ} (hz : 0 ≤ z ∧ z < 1 / (k : ℝ)) :
    0 ≤ ⌊((k * d : ℕ) : ℝ) * z⌋ ∧ ⌊((k * d : ℕ) : ℝ) * z⌋ < (d : ℤ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hz.1), ?_⟩
  apply Int.floor_lt.mpr
  have hSmall := mul_lt_mul_of_pos_left ((lt_div_iff₀ hkR).mp hz.2) hdR
  simp only [Nat.cast_mul, Int.cast_natCast]
  nlinarith only [hSmall]

theorem scalarMeanGrid_canonical_mem {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (z : ℂ) (hRe : 0 ≤ z.re ∧ z.re < 1 / (k : ℝ))
    (hIm : 0 ≤ z.im ∧ z.im < 1 / (k : ℝ)) :
    canonicalApprox (k * d) z ∈ scalarMeanGrid k d := by
  have hReIndex := fine_floor_index_range hk hd hRe
  have hImIndex := fine_floor_index_range hk hd hIm
  unfold scalarMeanGrid
  apply Finset.mem_image.mpr
  refine ⟨(⌊((k * d : ℕ) : ℝ) * z.re⌋.toNat, ⌊((k * d : ℕ) : ℝ) * z.im⌋.toNat), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  · simp only [Int.toNat_of_nonneg hReIndex.1, Int.toNat_of_nonneg hImIndex.1, canonicalApprox]

theorem canonicalErrorMean_fine_grid_mem {n k d : ℕ} (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (x : Fin n → ℂ) : canonicalApprox (k * d) (canonicalErrorMean k x) ∈ scalarMeanGrid k d := by
  have hRange := canonicalErrorMean_component_ranges hn hk x
  exact scalarMeanGrid_canonical_mem hk hd _ hRange.1 hRange.2

theorem canonicalErrorMean_fine_grid_error {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (x : Fin n → ℂ) :
    ‖canonicalErrorMean k x - canonicalApprox (k * d) (canonicalErrorMean k x)‖ ≤
      Real.sqrt 2 / ((k : ℝ) * d) := by
  simpa only [Nat.cast_mul] using canonicalApprox_norm_error (Nat.mul_pos hk hd) (canonicalErrorMean k x)

end CircularLaw
