import CircularLaw.PermittedSteepShift
import CircularLaw.SourceStartingRank
import CircularLaw.SourceSteepWitness

/-!
# The actual permitted inclusion `T3^K(L) ⊆ VL`

Both the constant `0.9` and the literal floor normal rank are retained.
All finite conditions hold eventually in the source degree band,
uniformly for the two source codimensions.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceVL (n L : ℕ) (a : ℝ) : Set (Fin n → ℂ) :=
  sourceVerySteep n (sourceNormalRank a L)

theorem source_shifted_T3_in_VL {n d L : ℕ} {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hdLarge : 40000 ≤ d) (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (hp : 1 < steepStride d)
    (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5)
    (hRoot : 8 / a ≤ Real.sqrt d) (hSize : 2 ≤ a * (L : ℝ)) :
    sourceShiftedT3 n d L ⊆ sourceVL n L a := by
  have hd : 0 < d := by omega
  have hBounds := source_starting_rank_bounds hdLarge hn hDimension hL hp hStride
  have hRank := source_starting_rank_le_normal ha hd hp hBounds.1 hStride hRoot hSize
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hn
  have hLBound := (kernelCodimension_quotient_bounds hd hn3 hL).2.1
  have hNormal := sourceNormalRank_le_dimension ha.le haOne
    (hLBound.trans (Nat.div_le_self n (d ^ 3)))
  intro v hv
  exact sourceVerySteep_mono_rank hRank hNormal v
    (sourceT3_constant_shift_witness hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2.1 v hv)

theorem eventually_source_shifted_T3_in_VL_degree_band {C a : ℝ} (hC : 0 < C)
    (ha : 0 < a) (haOne : a ≤ 1) {d : ℕ → ℕ} (hLower : LogLowerBound C d) (power : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Real.rpow (Real.log n) power) :
    ∀ᶠ n : ℕ in atTop, ∀ L : ℕ, IsKernelCodimension n (d n) L →
      sourceShiftedT3 n (d n) L ⊆ sourceVL n L a := by
  have hDegree := degree_tendsto_atTop_of_log_lower hC hLower
  have hLarge := hDegree.eventually (eventually_ge_atTop 40000)
  have hStride := hDegree.eventually eventually_steepStride_bounds
  have hDReal : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hRoot : ∀ᶠ n : ℕ in atTop, 8 / a ≤ Real.sqrt (d n) :=
    (Real.tendsto_sqrt_atTop.comp hDReal).eventually_ge_atTop _
  have hDSize := hDReal.eventually_ge_atTop (1 / a)
  filter_upwards [hLarge, hStride, hRoot, hDSize,
    eventually_polylog_power_dimension power 4 (by norm_num : (0 : ℝ) < 4),
    eventually_firstSteepScale_dimension power, hUpper]
    with n hLarge hStride hRoot hDSize hPoly hDimension hUpper
  intro L hL
  have hd : 0 < d n := by omega
  have hn : 4 * d n ^ 4 ≤ n := by exact_mod_cast hPoly (d n) hUpper
  have hLReal : 2 * (d n : ℝ) ≤ L := by
    exact_mod_cast kernelCodimension_large_lower hd hn hL
  have hDScaled := (div_le_iff₀ ha).mp hDSize
  have hLScaled := mul_le_mul_of_nonneg_left hLReal ha.le
  have hSize : 2 ≤ a * (L : ℝ) := by nlinarith
  exact source_shifted_T3_in_VL ha haOne hLarge hn (hDimension (d n) hd hUpper) hL
    hStride.1 hStride.2 hRoot hSize

end CircularLaw
