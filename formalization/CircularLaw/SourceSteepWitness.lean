import CircularLaw.SteepDimensionRates
import CircularLaw.SteepScaleGeometry

/-!
# The actual source multiscale witness event

The event uses the literal floor stride, least starting exponent,
geometric scales and terminal ceiling. Its failure has the source
`exp(-c*n/d^3)` rate for both codimensions and every deterministic row
set of the required size. All finite scale conditions are discharged
throughout the manuscript's logarithmic degree band.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def SourceSteepWitness {n d : ℕ} (I : Finset (Fin n)) (L : ℕ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∀ a ∈ sourceSteepScalePairs n d L, UniformUniqueWitness I a.1 a.2 rows

theorem source_steep_witness_failure {n d L : ℕ} (hdLarge : 40000 ≤ d)
    (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (I : Finset (Fin n)) (hI : I.card = n - L)
    (hp : 1 < steepStride d) (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5)
    (hDegree : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d)
    (hLog : Real.log n ≤ (5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceSteepWitness I L rows) ≤
      Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) := by
  have hd : 0 < d := by omega
  have hPower := Nat.pow_le_pow_right hd (by decide : 1 ≤ 4)
  simp only [pow_one] at hPower
  have hdn : d ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnPos : 0 < n := by omega
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hn
  have hRows := kernelCodimension_retained_card (by omega : 5 ≤ d) hn3 hL I hI
  have hScales := source_steep_scale_conditions hdLarge hn hDimension hL hp hStride
  have hRoot : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    exact_mod_cast hdLarge
  have hCard := source_steep_scale_card_le (L := L) hd hnPos
    (firstSteepScale_small hd hDimension hRoot)
  have hEvent : (fun rows : RowSliceMatrix n d => ¬SourceSteepWitness I L rows) =
      (fun rows => ∃ a ∈ sourceSteepScalePairs n d L, ¬UniformUniqueWitness I a.1 a.2 rows) := by
    funext rows
    simp only [SourceSteepWitness, not_forall, exists_prop]
  rw [hEvent]
  apply (steep_witness_failure_union hn2 hd hdn I hRows (sourceSteepScalePairs n d L)
    hStride hDegree hScales).trans
  apply le_trans _ (steep_witness_prefactor_absorbed hnPos hLog)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (Real.exp_pos _).le

theorem eventually_source_steep_witness_failure_degree_band {C : ℝ} (hC : 0 < C)
    {d : ℕ → ℕ} (hLower : LogLowerBound C d) (power : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) power) :
    ∀ᶠ n : ℕ in atTop, ∀ L : ℕ, IsKernelCodimension n (d n) L →
      ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n (d n) => ¬SourceSteepWitness I L rows) ≤
          Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d n : ℝ) ^ 3) := by
  have hDegree := degree_tendsto_atTop_of_log_lower hC hLower
  have hLarge := hDegree.eventually (eventually_ge_atTop 40000)
  have hStride := hDegree.eventually eventually_steepStride_bounds
  have hEntropy := hDegree.eventually eventually_steep_witness_entropy
  filter_upwards [hLarge, hStride, hEntropy, eventually_polylog_power_dimension power 4
    (by norm_num : (0 : ℝ) < 4), eventually_firstSteepScale_dimension power,
    eventually_steep_scale_prefactor power, hUpper]
    with n hLarge hStride hEntropy hPoly hDimension hLog hUpper
  intro L hL I hI
  have hd : 0 < d n := by omega
  have hn : 4 * d n ^ 4 ≤ n := by exact_mod_cast hPoly (d n) hUpper
  exact source_steep_witness_failure hLarge hn (hDimension (d n) hd hUpper) hL I hI
    hStride.1 hStride.2 hEntropy (hLog (d n) hd hUpper)

end CircularLaw
