import CircularLaw.AlmostConstantReductionFinite
import CircularLaw.AlmostConstantRanks
import CircularLaw.LowerBandEventually

/-!
# The full manuscript almost-constant reduction

The target spells out the surrounding Section 4 degree band and fixed
small third-scale constant. Its threshold is uniform in every degree
in that band and in both source codimensions. No rank compatibility,
center bounds, recursive alternatives or decomposition conclusion is
an added hypothesis of the target.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_almost_constant_reduction_uniform {a₃ C : ℝ} (ha : 0 < a₃)
    (haHalf : a₃ < 1 / 2) (hC : 0 < C) (power : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) →
      (d : ℝ) ≤ Real.rpow (Real.log n) power →
      ∀ L : ℕ, IsKernelCodimension n d L →
        (sourceAlmostConstant n d a₃ \ sourceS n d a₃ 12) \ {0} ⊆
          sourceShiftedSteepUnion n d L a₃ := by
  have hDegree : ∀ᶠ d : ℕ in atTop, 40000 ≤ d ∧
      (1 < steepStride d ∧ (steepStride d : ℝ) ≤ Real.sqrt d / 5) ∧
      1 / (8 * a₃) ≤ (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 40000, eventually_steepStride_bounds,
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop
        (1 / (8 * a₃))] with d hLarge hStride hSize
    exact ⟨hLarge, hStride, hSize⟩
  have hNSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_degree_property_uniform hC hDegree,
    eventually_polylog_power_dimension power 4 (by norm_num : (0 : ℝ) < 4),
    eventually_firstSteepScale_dimension power, hNSize]
    with n hDegree hPoly hDimension hNSize
  intro d hLower hUpper L hL x hx
  obtain ⟨hLarge, hStride, hDSize⟩ := hDegree d hLower
  have hd : 0 < d := by omega
  have hn : 4 * d ^ 4 ≤ n := by exact_mod_cast hPoly d hUpper
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hn
  have hDim := hDimension d hd hUpper
  have hSource := source_starting_rank_bounds hLarge hn hDim hL hStride.1 hStride.2
  have hRoot : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    exact_mod_cast hLarge
  have hSmall := firstSteepScale_small hd hDim hRoot
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have h := (div_le_iff₀ ha).mp hNSize
    nlinarith
  have hThird := thirdSteepScale_bounds ha hSize
  have hRanks : firstSteepScale n d ≤ almostConstantRank n d ∧
      almostConstantRank n d ≤ thirdSteepScale n a₃ :=
    ⟨firstSteepScale_le_almostConstantRank hd hSmall,
      almostConstantRank_le_thirdSteepScale hd ha hDSize hSize⟩
  have hLLarge := kernelCodimension_large_lower hd hn hL
  have hSizeFirst := codimension_first_scale_bound (by omega : 20 ≤ d) hn3 hL
  have hn1 : 1 < firstSteepScale n d := by omega
  have hNZ : x ≠ 0 := by simpa only [Set.mem_singleton_iff] using hx.2
  exact almost_constant_reduction_finite a₃ (by omega : 6 ≤ d) hStride.1 hn1 hRanks
    hThird.1 (thirdSteepScale_half ha.le haHalf.le) hSource.2.2.2.2.le x hNZ hx.1.1 hx.1.2

/-- The manuscript lemma, with its surrounding lower-band and fixed
third-scale constant made explicit. The statement applies to every
degree in the band once the common dimension threshold is reached. -/
def AlmostConstantReductionLemma : Prop :=
  ∀ a₃ : ℝ, 0 < a₃ → a₃ < 1 / 2 → ∀ C : ℝ, 0 < C →
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ d : ℕ, InLowerBand C σ n d → ∀ L : ℕ, IsKernelCodimension n d L →
        (sourceAlmostConstant n d a₃ \ sourceS n d a₃ 12) \ {0} ⊆
          sourceShiftedSteepUnion n d L a₃

theorem almost_constant_reduction_lemma : AlmostConstantReductionLemma := by
  intro a₃ ha haHalf C hC σ _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_almost_constant_reduction_uniform ha haHalf hC (1 + σ))
  refine ⟨N, ?_⟩
  intro n hn d hBand L hL
  exact hN n hn d hBand.1 hBand.2 L hL

end CircularLaw
