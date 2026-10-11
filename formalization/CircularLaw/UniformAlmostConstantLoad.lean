import CircularLaw.AlmostConstantLoadExclusion

/-!
# Uniform almost-constant row-load exclusion

All rank, floor, dimension, and spectral-window requirements are derived
from the literal source degree band. The same load event excludes all
almost-constant `S(12)` kernel vectors and all allowed spectral shifts,
for either codimension and every deterministic retained set.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_source_almost_constant_load_exclusion_uniform {C a₃ : ℝ}
    (hC : 0 < C) (ha : 0 < a₃) (haSmall : a₃ ≤ 1 / 1000) (σ Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ rows : RowSliceMatrix n d, SourceRowLoad I (thirdSteepScale n a₃) rows →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            ∀ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
              (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0 := by
  have hNSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC (eventually_fixed_shift_witness_window Z₀), hNSize]
    with n hConditions hWindow hNSize
  intro d hBand L hL I hI rows hLoad ζ hζ
  have h := hConditions d hBand.1 hBand.2
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hPower : 4 ≤ d ^ 3 := by
    have hLarge := h.degree_large
    have hPow := Nat.pow_le_pow_left (by omega : 2 ≤ d) 3
    norm_num at hPow
    omega
  have h16 : 16 * d ≤ n := by
    have hDimension := h.dimension_fourth
    calc
      _ ≤ 4 * d ^ 3 * d := by nlinarith
      _ = 4 * d ^ 4 := by ring
      _ ≤ n := hDimension
  have hn : 0 < n := by omega
  have hRank : 0 < almostConstantRank n d := by
    have hOne : 1 ≤ n / (16 * d) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 16 * d)).mpr (by simpa only [one_mul] using h16)
    change 0 < n / (16 * d)
    omega
  have hRankN : almostConstantRank n d ≤ n := Nat.div_le_self n (16 * d)
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have hScaled := (div_le_iff₀ ha).mp hNSize
    nlinarith
  have hk := thirdSteepScale_bounds ha hSize
  have hScale : (thirdSteepScale n a₃ : ℝ) ≤ (n : ℝ) / 1000 := by
    have hScaled := mul_le_mul_of_nonneg_right haSmall (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [hk.2.2]
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans h.dimension_fourth
  have hRows := kernelCodimension_retained_card (by have hLarge := h.degree_large; omega) hn3 hL I hI
  exact source_almost_constant_load_kernel_exclusion (by have hLarge := h.degree_large; omega)
    hn hRank hRankN hk.1 (thirdSteepScale_half ha.le (by linarith)) hScale I hRows rows hLoad
    ζ (hWindow d hBand.1 ζ hζ)

theorem eventually_source_almost_constant_load_kernel_probability_uniform {C a₃ : ℝ}
    (hC : 0 < C) (ha : 0 < a₃) (haSmall : a₃ ≤ 1 / 1000)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4) (σ Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ∃ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d ∧
            ∃ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
              (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤
          Real.exp (-(rowLoadRate / 4) * n) := by
  filter_upwards [eventually_source_almost_constant_load_exclusion_uniform hC ha haSmall σ Z₀,
    eventually_source_row_load_failure_uniform hC ha (by linarith) hEntropy σ]
    with n hExclusion hFailure
  intro d hBand L hL I hI
  apply (uniformProbability_mono ?_).trans (hFailure d hBand L hL I hI)
  intro rows hEvent hLoad
  obtain ⟨ζ, hζ, x, hx, hKernel⟩ := hEvent
  exact hExclusion d hBand L hL I hI rows hLoad ζ hζ x hx hKernel

/-- Closed source row-load and almost-constant kernel estimates with a
fixed positive small-density range; no entropy or rank estimate is an
assumed premise of this target. -/
def AlmostConstantRowLoadExclusionLemma : Prop :=
  ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 1000 ∧
    ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ a → ∀ C : ℝ, 0 < C → ∀ σ Z₀ : ℝ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ¬SourceRowLoad I (thirdSteepScale n a₃) rows) ≤ Real.exp (-(rowLoadRate / 4) * n) ∧
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d ∧
              ∃ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
                (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤ Real.exp (-(rowLoadRate / 4) * n)

theorem almost_constant_row_load_exclusion_lemma : AlmostConstantRowLoadExclusionLemma := by
  obtain ⟨a, ha, haSmall, hEntropy⟩ := source_row_load_small_constant
  refine ⟨a, ha, haSmall, ?_⟩
  intro a₃ ha₃ ha₃a C hC σ Z₀
  have hSmall := ha₃a.trans haSmall
  have hEnt := hEntropy a₃ ha₃ ha₃a
  have hEventually : ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬SourceRowLoad I (thirdSteepScale n a₃) rows) ≤ Real.exp (-(rowLoadRate / 4) * n) ∧
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ∃ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d ∧
            ∃ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
              (retainedShiftedMatrix I ζ rows).mulVec x = 0) ≤ Real.exp (-(rowLoadRate / 4) * n) := by
    filter_upwards [eventually_source_row_load_failure_uniform hC ha₃ (by linarith) hEnt σ,
      eventually_source_almost_constant_load_kernel_probability_uniform hC ha₃ hSmall hEnt σ Z₀]
      with n hLoad hKernel
    intro d hBand L hL I hI
    exact ⟨hLoad d hBand L hL I hI, hKernel d hBand L hL I hI⟩
  exact eventually_atTop.mp hEventually

end CircularLaw
