import CircularLaw.SteepNetCardinalityUniform
import CircularLaw.ShiftedSteepNetCover

/-!
# The closed source steep-net lemma

The actual finite grids satisfy the exponential product count, ordered
gap, strict support cutoff and separate component approximation. A single
dimension threshold supplies every finite condition for both literal
classes, every degree in the lower band and both kernel codimensions.

This supplies the net dependency in Section 4. It does not yet prove the
kernel exclusions, which also require the equal-block fit and probability
absorption estimates.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def SourceSteepNetData (n d L : ℕ) (a₃ : ℝ) : Prop :=
  (((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card ≤
    Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ))) ∧
  (((sourceT2Net n d a₃).card : ℝ) *
      (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card ≤
    Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ))) ∧
  (∀ u ∈ sourceT1Net n d,
    1 - steepNetError d ≤ orderedNormAt u (firstSteepScale n d) ∧
    2 / 3 < orderedNormAt u (firstSteepScale n d) ∧
    ∀ j : ℕ, secondSteepScale n d ≤ j → j ≤ n → orderedNormAt u j = 0) ∧
  (∀ u ∈ sourceT2Net n d a₃,
    1 - steepNetError d ≤ orderedNormAt u (secondSteepScale n d) ∧
    2 / 3 < orderedNormAt u (secondSteepScale n d) ∧
    ∀ j : ℕ, thirdSteepScale n a₃ ≤ j → j ≤ n → orderedNormAt u j = 0) ∧
  (∀ x ∈ sourceT1 n d L, orderedNormAt x (firstSteepScale n d) = 1 →
    ∀ c : ℂ, ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 →
      ∃ u ∈ sourceT1Net n d, ∃ w ∈ steepConstantNet d 1,
        (∀ j, ‖x j - u j‖ ≤ steepNetError d) ∧ ‖c - w‖ ≤ steepNetError d) ∧
  (∀ x ∈ sourceT2 n d L a₃, orderedNormAt x (secondSteepScale n d) = 1 →
    ∀ c : ℂ, ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 →
      ∃ u ∈ sourceT2Net n d a₃, ∃ w ∈ steepConstantNet d (Real.rpow (d : ℝ) (3 / 2)),
        (∀ j, ‖x j - u j‖ ≤ steepNetError d) ∧ ‖c - w‖ ≤ steepNetError d)

theorem eventually_source_steep_net_data_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → SourceSteepNetData n d L a₃ := by
  have hSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_source_steep_net_cardinality_uniform ha haOne hC σ,
    eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC eventually_steepStride_cubic, hSize]
      with n hCounts hConditions hCubic hSize
  intro d hBand L hL
  have h := hConditions d hBand.1 hBand.2
  have hCube := hCubic d hBand.1
  have hd : 0 < d := (source_kernel_dimension_twice_degree h).2.1
  have hThirdSize : 2 ≤ a₃ * (n : ℝ) := by
    have h := (div_le_iff₀ ha).mp hSize
    nlinarith
  have hSecond := secondSteepScale_valid hd h.dimension_root
  have hThird := thirdSteepScale_bounds ha hThirdSize
  have hCount := hCounts d hBand
  refine ⟨hCount.1, hCount.2, ?_, ?_, ?_, ?_⟩
  · intro u hu
    refine ⟨steepNonconstantNet_normalized_gap u hu,
      (steepNonconstantNet_gap_and_tail u hu).1, ?_⟩
    intro j hNextJ hJN
    exact steepNonconstantNet_all_later_zero hSecond.1 hNextJ hJN u hu
  · intro u hu
    refine ⟨steepNonconstantNet_normalized_gap u hu,
      (steepNonconstantNet_gap_and_tail u hu).1, ?_⟩
    intro j hNextJ hJN
    exact steepNonconstantNet_all_later_zero hThird.1 hNextJ hJN u hu
  · intro x hx hNorm c hc
    exact normalized_shifted_sourceT1_net_cover h hL hCube x hx hNorm c hc
  · intro x hx hNorm c hc
    exact normalized_shifted_sourceT2_net_cover ha haOne hThirdSize h hL hCube x hx hNorm c hc

def SourceSteepNetLemma : Prop :=
  ∀ a₃ : ℝ, 0 < a₃ → a₃ < 1 / 2 → ∀ C : ℝ, 0 < C →
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ d : ℕ, InLowerBand C σ n d → ∀ L : ℕ, IsKernelCodimension n d L →
        SourceSteepNetData n d L a₃

theorem source_steep_net_lemma : SourceSteepNetLemma := by
  intro a₃ ha haHalf C hC σ _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_source_steep_net_data_uniform ha (by linarith : a₃ ≤ 1) hC σ)
  exact ⟨N, hN⟩

end CircularLaw
