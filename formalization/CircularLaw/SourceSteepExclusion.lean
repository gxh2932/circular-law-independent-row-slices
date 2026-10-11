import CircularLaw.SourceSteepWitness
import CircularLaw.SourceSteepClasses
import CircularLaw.SteepWitnessExclusion

/-!
# Exclusion of the actual shifted source `T0` class

The multiscale witness event excludes every member of the recursively
defined shifted source class, simultaneously for all spectral shifts
in the allowed window. The failure probability has the manuscript's
`exp(-c*n/d^3)` rate, uniformly over the two codimensions and deterministic
retained row sets throughout the source degree band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem source_shifted_T0_exclusion {n d L : ℕ} (hdLarge : 40000 ≤ d)
    (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (hp : 1 < steepStride d)
    (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (hWitness : SourceSteepWitness I L rows)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ) / 20) (v : Fin n → ℂ)
    (hv : v ∈ sourceShiftedT0 n d L) :
    (retainedShiftedMatrix I ζ rows).mulVec v ≠ 0 := by
  have hd : 0 < d := by omega
  have hPower := Nat.pow_le_pow_right hd (by decide : 1 ≤ 4)
  simp only [pow_one] at hPower
  have hnPos : 0 < n := by omega
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hn
  have hRoot : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    exact_mod_cast hdLarge
  have hSmall := firstSteepScale_small hd hDimension hRoot
  have hn1n : firstSteepScale n d ≤ n := by nlinarith
  have hLLarge := kernelCodimension_large_lower hd hn hL
  have hSize := codimension_first_scale_bound (by omega : 20 ≤ d) hn3 hL
  have hn1 : 1 < firstSteepScale n d := by omega
  obtain ⟨x, c, hx, hCenter, rfl⟩ := hv
  obtain ⟨a, ha, hJump⟩ := sourceT0_has_source_jump x hx
  have hBounds := source_steep_scale_conditions hdLarge hn hDimension hL hp hStride a ha
  have ht1 := sourceSteepScalePairs_second_le hp hn1 a ha
  have htn := ht1.trans hn1n
  have hCenterAt : ‖c‖ ≤ orderedNormAt x a.2 / 10 :=
    hCenter.trans (div_le_div_of_nonneg_right
      (orderedNormAt_antitone x (by omega : 0 < a.2) ht1 hn1n) (by norm_num))
  rw [orderedNormAt_eq x (by omega : 0 < a.2) htn,
    orderedNormAt_eq x hBounds.1 (by omega : a.1 ≤ n)] at hJump
  rw [orderedNormAt_eq x (by omega : 0 < a.2) htn] at hCenterAt
  exact steep_unique_witness_exclusion hd hBounds.1 hBounds.2.1 htn I rows
    (hWitness a ha) x c ζ hJump hCenterAt hSpectral

theorem source_shifted_T0_kernel_probability {n d L : ℕ} (hdLarge : 40000 ≤ d)
    (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (I : Finset (Fin n)) (hI : I.card = n - L)
    (hp : 1 < steepStride d) (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5)
    (hDegree : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d)
    (hLog : Real.log n ≤ (5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) / 20 ∧ ∃ v ∈ sourceShiftedT0 n d L,
        (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
      Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) := by
  apply (uniformProbability_mono ?_).trans
    (source_steep_witness_failure hdLarge hn hDimension hL I hI hp hStride hDegree hLog)
  intro rows hEvent hWitness
  obtain ⟨ζ, hSpectral, v, hv, hKernel⟩ := hEvent
  exact source_shifted_T0_exclusion hdLarge hn hDimension hL hp hStride I rows
    hWitness ζ hSpectral v hv hKernel

theorem eventually_source_shifted_T0_kernel_probability_degree_band {C : ℝ} (hC : 0 < C)
    {d : ℕ → ℕ} (hLower : LogLowerBound C d) (power Z₀ : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) power) :
    ∀ᶠ n : ℕ in atTop, ∀ L : ℕ, IsKernelCodimension n (d n) L →
      ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n (d n) =>
          ∃ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt (d n) ∧ ∃ v ∈ sourceShiftedT0 n (d n) L,
            (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
          Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d n : ℝ) ^ 3) := by
  have hDegree := degree_tendsto_atTop_of_log_lower hC hLower
  have hLarge := hDegree.eventually (eventually_ge_atTop 40000)
  have hStride := hDegree.eventually eventually_steepStride_bounds
  have hEntropy := hDegree.eventually eventually_steep_witness_entropy
  have hWindow := hDegree.eventually (eventually_fixed_shift_witness_window Z₀)
  filter_upwards [hLarge, hStride, hEntropy, hWindow,
    eventually_polylog_power_dimension power 4 (by norm_num : (0 : ℝ) < 4),
    eventually_firstSteepScale_dimension power, eventually_steep_scale_prefactor power, hUpper]
    with n hLarge hStride hEntropy hWindow hPoly hDimension hLog hUpper
  intro L hL I hI
  have hd : 0 < d n := by omega
  have hn : 4 * d n ^ 4 ≤ n := by exact_mod_cast hPoly (d n) hUpper
  apply (uniformProbability_mono ?_).trans
    (source_shifted_T0_kernel_probability hLarge hn (hDimension (d n) hd hUpper)
      hL I hI hStride.1 hStride.2 hEntropy (hLog (d n) hd hUpper))
  intro rows hEvent
  obtain ⟨ζ, hSpectral, v, hv, hKernel⟩ := hEvent
  exact ⟨ζ, hWindow ζ hSpectral, v, hv, hKernel⟩

end CircularLaw
