import CircularLaw.SourceGradualCoordinates

/-!
# Coordinate ranges for the normalized source steep classes

Outside `T0` and `T3`, the first modulus is bounded by `n^6` times
the `n1` modulus. The terminal ceiling bounds all but the high prefix
by `4*d` times that modulus. Normalizing `T1` and `T2` supplies the
three ranges and the truncation error needed by the finite grid nets.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem source_kernel_first_scale_data {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L) :
    1 < firstSteepScale n d ∧ firstSteepScale n d ≤ n ∧
      steepStartExponent (steepStride d) d L ≤
        steepEndExponent (steepStride d) (firstSteepScale n d) := by
  have hRanks := source_starting_rank_bounds h.degree_large h.dimension_fourth h.dimension_root
    hL h.stride_pos h.stride_upper
  have hPower : 1 < steepStride d ^ steepStartExponent (steepStride d) d L :=
    Nat.one_lt_pow (by omega : steepStartExponent (steepStride d) d L ≠ 0) h.stride_pos
  exact ⟨hPower.trans_le hRanks.2.1, hRanks.2.2.1, hRanks.2.2.2.2.le⟩

theorem source_no_steep_norm_bound {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L) :
    ∀ j : Fin n, ‖x j‖ ≤ (n : ℝ) ^ 6 * orderedNormAt x (firstSteepScale n d) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hData := source_kernel_first_scale_data h hL
  have hRoot : (32 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    have hLarge := h.degree_large
    exact_mod_cast (by omega : 32 ^ 2 ≤ d)
  have hCoefficient := firstSteepScale_cubic_coefficient hd h.dimension_root hRoot
  have hDCube : (1 : ℝ) ≤ (d : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hReduced : 4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by
    calc
      _ = (4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3) * 1 := by ring
      _ ≤ (4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3) * (d : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hDCube (by positivity)
      _ ≤ _ := hCoefficient
  have hFirst := source_initial_modulus_bound h.stride_pos hData.1 hData.2.1
    hData.2.2 hCubic x h₀ h₃
  have hBound : orderedNormAt x 1 ≤ (n : ℝ) ^ 6 * orderedNormAt x (firstSteepScale n d) := by
    calc
      _ ≤ 4 * (d : ℝ) * (n : ℝ) ^ 3 * (firstSteepScale n d : ℝ) ^ 3 *
          orderedNormAt x (firstSteepScale n d) := hFirst
      _ = (n : ℝ) ^ 3 * (4 * (d : ℝ) * (firstSteepScale n d : ℝ) ^ 3) *
          orderedNormAt x (firstSteepScale n d) := by ring
      _ ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 3 * orderedNormAt x (firstSteepScale n d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hReduced (by positivity))
          (orderedNormAt_nonneg x _)
      _ = _ := by ring
  intro j
  exact (norm_le_first_orderedNormAt (by omega : 0 < n) x j).trans hBound

theorem source_terminal_no_jump {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (x : Fin n → ℂ) (h₀ : x ∉ sourceT0 n d L) (h₃ : x ∉ sourceT3 n d L) :
    orderedNormAt x (terminalSteepSize (steepStride d) (firstSteepScale n d)) ≤
      4 * (d : ℝ) * orderedNormAt x (firstSteepScale n d) := by
  have hData := source_kernel_first_scale_data h hL
  have hLast := source_no_T0_jump x hData.2.2
    (le_refl (steepEndExponent (steepStride d) (firstSteepScale n d))) h₀ h₃
  simpa only [sourceSteepPairAt, lt_self_iff_false, if_false] using hLast

theorem normalized_sourceT1_coordinate_ranges {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT1 n d L) (hNorm : orderedNormAt x (firstSteepScale n d) = 1) :
    (∀ j : Fin n, ‖x j‖ ≤ (n : ℝ) ^ 6) ∧
      orderedNormAt x (terminalSteepSize (steepStride d) (firstSteepScale n d)) ≤ 4 * (d : ℝ) ∧
        orderedNormAt x (secondSteepScale n d) < 1 / Real.rpow (d : ℝ) (3 / 2) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hScale : 0 < Real.rpow (d : ℝ) (3 / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hNorm, mul_one] using source_no_steep_norm_bound h hL hCubic x hx.1 hx.2.1
  · simpa only [hNorm, mul_one] using source_terminal_no_jump h hL x hx.1 hx.2.1
  · apply (lt_div_iff₀ hScale).mpr
    simpa only [hNorm, mul_comm] using hx.2.2

theorem normalized_sourceT2_coordinate_ranges {n d L : ℕ} {a₃ : ℝ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT2 n d L a₃) (hNorm : orderedNormAt x (secondSteepScale n d) = 1) :
    orderedNormAt x (firstSteepScale n d) ≤ Real.rpow (d : ℝ) (3 / 2) ∧
      (∀ j : Fin n, ‖x j‖ ≤ (n : ℝ) ^ 6 * Real.rpow (d : ℝ) (3 / 2)) ∧
        orderedNormAt x (terminalSteepSize (steepStride d) (firstSteepScale n d)) ≤
          4 * (d : ℝ) * Real.rpow (d : ℝ) (3 / 2) ∧
            orderedNormAt x (thirdSteepScale n a₃) < 1 / Real.rpow (d : ℝ) (3 / 2) := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hScale : 0 < Real.rpow (d : ℝ) (3 / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hFirst : orderedNormAt x (firstSteepScale n d) ≤ Real.rpow (d : ℝ) (3 / 2) := by
    apply le_of_not_gt
    intro hBad
    apply hx.2.1
    exact ⟨hx.1, hx.2.2.1, by simpa only [hNorm, mul_one] using hBad⟩
  refine ⟨hFirst, ?_, ?_, ?_⟩
  · intro j
    exact (source_no_steep_norm_bound h hL hCubic x hx.1 hx.2.2.1 j).trans
      (mul_le_mul_of_nonneg_left hFirst (by positivity))
  · exact (source_terminal_no_jump h hL x hx.1 hx.2.2.1).trans
      (mul_le_mul_of_nonneg_left hFirst (by positivity))
  · apply (lt_div_iff₀ hScale).mpr
    simpa only [hNorm, mul_comm] using hx.2.2.2

end CircularLaw
