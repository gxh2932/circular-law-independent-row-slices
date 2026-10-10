import CircularLaw.LowerBandEventually

/-!
# Common finite kernel conditions, uniformly in the degree band

The dimension threshold applies to every integer degree in the band,
not just to a fixed degree sequence. This packages conditions already
proved from the band for the finite source witness and class estimates.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

structure SourceKernelConditions (n d : ℕ) : Prop where
  degree_large : 40000 ≤ d
  dimension_fourth : 4 * d ^ 4 ≤ n
  dimension_root : (d : ℝ) * Real.sqrt d ≤ n
  stride_pos : 1 < steepStride d
  stride_upper : (steepStride d : ℝ) ≤ Real.sqrt d / 5
  witness_entropy : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
    (uniqueWitnessRate / 2) * d
  scale_prefactor : Real.log n ≤ (5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3

theorem eventually_source_kernel_conditions_uniform {C : ℝ} (hC : 0 < C) (power : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) →
      (d : ℝ) ≤ Real.rpow (Real.log n) power → SourceKernelConditions n d := by
  have hDegree : ∀ᶠ d : ℕ in atTop, 40000 ≤ d ∧
      (1 < steepStride d ∧ (steepStride d : ℝ) ≤ Real.sqrt d / 5) ∧
      Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤ (uniqueWitnessRate / 2) * d := by
    filter_upwards [eventually_ge_atTop 40000, eventually_steepStride_bounds,
      eventually_steep_witness_entropy] with d hLarge hStride hEntropy
    exact ⟨hLarge, hStride, hEntropy⟩
  filter_upwards [eventually_degree_property_uniform hC hDegree,
    eventually_polylog_power_dimension power 4 (by norm_num : (0 : ℝ) < 4),
    eventually_firstSteepScale_dimension power, eventually_steep_scale_prefactor power]
    with n hDegree hPoly hDimension hPrefactor
  intro d hLower hUpper
  obtain ⟨hLarge, hStride, hEntropy⟩ := hDegree d hLower
  have hd : 0 < d := by omega
  exact ⟨hLarge, by exact_mod_cast hPoly d hUpper, hDimension d hd hUpper,
    hStride.1, hStride.2, hEntropy, hPrefactor d hd hUpper⟩

end CircularLaw
