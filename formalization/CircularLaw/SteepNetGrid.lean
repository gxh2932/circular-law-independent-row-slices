import CircularLaw.SparseGridNet
import CircularLaw.SourceNetCoordinates

/-!
# The finite source steep-class nets and their geometry

Each nonconstant net is a filtered, explicitly finite three-range grid
family. The filter retains the actual ordered gap and the strict support
cutoff. The constant component is a finite complex grid, counted separately.
This module proves the approximation and support conclusions. The sharp
source exponential cardinality bound is proved in `SteepNetCardinalityUniform`.
-/

noncomputable section
open Classical

namespace CircularLaw

def steepNetResolution (d : ℕ) : ℕ := ⌈2 * Real.rpow (d : ℝ) (3 / 2)⌉₊

def steepNetError (d : ℕ) : ℝ := 1 / Real.rpow (d : ℝ) (3 / 2)

theorem steepNetResolution_pos {d : ℕ} (hd : 0 < d) : 0 < steepNetResolution d := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

theorem steepNetError_eq_rpow_neg (d : ℕ) :
    steepNetError d = Real.rpow (d : ℝ) (-(3 / 2)) := by
  simp only [steepNetError, Real.rpow_eq_pow, Real.rpow_neg (Nat.cast_nonneg d), one_div]

theorem steepNetResolution_error {d : ℕ} (hd : 0 < d) :
    Real.sqrt 2 / (steepNetResolution d : ℝ) ≤ steepNetError d := by
  have hR : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hkR : (0 : ℝ) < steepNetResolution d := by exact_mod_cast steepNetResolution_pos hd
  have hSqrt : Real.sqrt 2 ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    norm_num [Real.sq_sqrt]
  have hCeil : 2 * Real.rpow (d : ℝ) (3 / 2) ≤ (steepNetResolution d : ℝ) := Nat.le_ceil _
  unfold steepNetError
  apply (le_div_iff₀ hR).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hkR).mpr
  have h := mul_le_mul_of_nonneg_right hSqrt hR.le
  convert h.trans hCeil using 1
  ring

theorem steepNetResolution_upper {d : ℕ} (hd : 0 < d) :
    (steepNetResolution d : ℝ) ≤ 3 * Real.rpow (d : ℝ) (3 / 2) := by
  have hR : 1 ≤ Real.rpow (d : ℝ) (3 / 2) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hCeil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * Real.rpow (d : ℝ) (3 / 2))
  change (⌈2 * Real.rpow (d : ℝ) (3 / 2)⌉₊ : ℝ) ≤ _
  linarith

theorem steepNetError_lt_third {d : ℕ} (hd : 4 ≤ d) : steepNetError d < 1 / 3 := by
  have hdPos : 0 < d := by omega
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot : (1 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    linarith
  have hR : 3 < Real.rpow (d : ℝ) (3 / 2) := by
    rw [degree_three_halves_eq hdPos]
    nlinarith
  unfold steepNetError
  apply (div_lt_iff₀ (by linarith : 0 < Real.rpow (d : ℝ) (3 / 2))).mpr
  linarith

def steepRawNet (n d next : ℕ) (cap : ℝ) : Finset (Fin n → ℂ) :=
  threeRangeGridNet n (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1)
    (firstSteepScale n d - 1) (next - 1)
      (gridBox (steepNetResolution d) (gridBoxRadius (steepNetResolution d) ((n : ℝ) ^ 6 * cap)))
      (gridBox (steepNetResolution d) (gridBoxRadius (steepNetResolution d) (4 * (d : ℝ) * cap)))
      (gridBox (steepNetResolution d) (gridBoxRadius (steepNetResolution d) cap))

def steepNonconstantNet (n d rank next : ℕ) (cap : ℝ) : Finset (Fin n → ℂ) :=
  (steepRawNet n d next cap).filter (fun u =>
    1 - steepNetError d ≤ orderedNormAt u rank ∧
      2 / 3 < orderedNormAt u rank ∧ orderedNormAt u next = 0)

def steepConstantNet (d : ℕ) (cap : ℝ) : Finset ℂ :=
  gridBox (steepNetResolution d) (gridBoxRadius (steepNetResolution d) cap)

def sourceT1Net (n d : ℕ) : Finset (Fin n → ℂ) :=
  steepNonconstantNet n d (firstSteepScale n d) (secondSteepScale n d) 1

def sourceT2Net (n d : ℕ) (a₃ : ℝ) : Finset (Fin n → ℂ) :=
  steepNonconstantNet n d (secondSteepScale n d) (thirdSteepScale n a₃)
    (Real.rpow (d : ℝ) (3 / 2))

theorem steepNonconstantNet_gap_and_tail {n d rank next : ℕ} {cap : ℝ}
    (u : Fin n → ℂ) (hu : u ∈ steepNonconstantNet n d rank next cap) :
    2 / 3 < orderedNormAt u rank ∧ orderedNormAt u next = 0 := (Finset.mem_filter.mp hu).2.2

theorem steepNonconstantNet_normalized_gap {n d rank next : ℕ} {cap : ℝ}
    (u : Fin n → ℂ) (hu : u ∈ steepNonconstantNet n d rank next cap) :
    1 - steepNetError d ≤ orderedNormAt u rank := (Finset.mem_filter.mp hu).2.1

theorem normalized_steep_net_approximation {n d L rank next : ℕ} {cap : ℝ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hRank : 0 < rank) (hRankN : rank ≤ n) (hNext : 0 < next) (hNextN : next ≤ n)
    (x : Fin n → ℂ) (hNorm : orderedNormAt x rank = 1)
    (hHigh : ∀ j, ‖x j‖ ≤ (n : ℝ) ^ 6 * cap)
    (hMiddle : orderedNormAt x (terminalSteepSize (steepStride d) (firstSteepScale n d)) ≤
      4 * (d : ℝ) * cap)
    (hBase : orderedNormAt x (firstSteepScale n d) ≤ cap)
    (hTail : orderedNormAt x next ≤ steepNetError d) :
    ∃ u ∈ steepNonconstantNet n d rank next cap,
      ∀ j, ‖x j - u j‖ ≤ steepNetError d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hData := source_kernel_first_scale_data h hL
  have hTerminal := terminalSteepSize_bounds (by have hp := h.stride_pos; omega : 1 ≤ steepStride d)
    (by omega : 0 < firstSteepScale n d)
  let u := truncatedCanonicalApprox (steepNetResolution d) next x
  have hApprox : ∀ j, ‖x j - u j‖ ≤ steepNetError d :=
    truncatedCanonicalApprox_error (steepNetResolution_pos hd) hNext hNextN
      (steepNetResolution_error hd) x hTail
  have hRaw : u ∈ steepRawNet n d next cap :=
    truncatedCanonicalApprox_mem_threeRangeGridNet hTerminal.1
      (by omega : 0 < firstSteepScale n d) hNext (hTerminal.2.1.trans hData.2.1)
        hData.2.1 hNextN x hHigh hMiddle hBase
  refine ⟨u, Finset.mem_filter.mpr ⟨hRaw, ?_⟩, hApprox⟩
  have hPerturb := (orderedNormAt_perturbation x u hRank hRankN (steepNetError d)
    (by intro j; simpa only [norm_sub_rev] using hApprox j)).2
  rw [hNorm] at hPerturb
  refine ⟨by linarith, ?_, ?_⟩
  · have hError := steepNetError_lt_third (by have hLarge := h.degree_large; omega : 4 ≤ d)
    linarith
  · exact truncatedCanonicalApprox_tail_zero hNext hNextN x

theorem normalized_sourceT1_net_approximation {n d L : ℕ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT1 n d L) (hNorm : orderedNormAt x (firstSteepScale n d) = 1) :
    ∃ u ∈ sourceT1Net n d, ∀ j, ‖x j - u j‖ ≤ steepNetError d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hRanges := normalized_sourceT1_coordinate_ranges h hL hCubic x hx hNorm
  have hData := source_kernel_first_scale_data h hL
  have hSecond := secondSteepScale_valid hd h.dimension_root
  apply normalized_steep_net_approximation h hL (by omega : 0 < firstSteepScale n d)
    hData.2.1 hSecond.1 hSecond.2 x hNorm
  · simpa only [mul_one] using hRanges.1
  · simpa only [mul_one] using hRanges.2.1
  · exact hNorm.le
  · exact hRanges.2.2.le

theorem normalized_sourceT2_net_approximation {n d L : ℕ} {a₃ : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (x : Fin n → ℂ)
    (hx : x ∈ sourceT2 n d L a₃) (hNorm : orderedNormAt x (secondSteepScale n d) = 1) :
    ∃ u ∈ sourceT2Net n d a₃, ∀ j, ‖x j - u j‖ ≤ steepNetError d := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hRanges := normalized_sourceT2_coordinate_ranges h hL hCubic x hx hNorm
  have hSecond := secondSteepScale_valid hd h.dimension_root
  have hThird := thirdSteepScale_bounds ha hSize
  have hThirdN : thirdSteepScale n a₃ ≤ n := by
    have hScaled := mul_le_mul_of_nonneg_right haOne (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    exact_mod_cast (by linarith [hThird.2.2] : (thirdSteepScale n a₃ : ℝ) ≤ n)
  exact normalized_steep_net_approximation h hL hSecond.1 hSecond.2 hThird.1 hThirdN
    x hNorm hRanges.2.1 hRanges.2.2.1 hRanges.1 hRanges.2.2.2.le

theorem steep_constant_net_approximation {d : ℕ} {cap : ℝ} (hd : 0 < d)
    (c : ℂ) (hc : ‖c‖ ≤ cap) :
    ∃ w ∈ steepConstantNet d cap, ‖c - w‖ ≤ steepNetError d := by
  refine ⟨canonicalApprox (steepNetResolution d) c, canonicalApprox_mem_gridBox c hc, ?_⟩
  exact (canonicalApprox_norm_error (steepNetResolution_pos hd) c).trans (steepNetResolution_error hd)

end CircularLaw
