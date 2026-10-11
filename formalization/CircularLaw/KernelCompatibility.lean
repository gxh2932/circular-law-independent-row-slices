import CircularLaw.KernelProbabilityAssembly

/-!
# Rectangular right-kernel compatibility

This is the named Section 4 theorem. The exact source very-steep class
and nonzero complex scalar cone contain the nonzero retained kernel with
probability at least `1-4/n`. A fixed positive admissible range for a3 and
a fixed absolute logarithmic lower constant are proved, rather than
assumed. One threshold applies to both literal codimensions and every
deterministic retained set and spectral shift in the source window.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_rectangular_kernel_compatibility_uniform {C a₃ a : ℝ}
    (hC : sourceKernelLowerConstant ≤ C) (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 1000)
    (hEntropy : smallSetEntropy a₃ ≤ rowLoadRate / 4)
    (ha₃Net : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800)
    (ha : 0 < a) (haOne : a ≤ 1) (σ Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          1 - 4 / (n : ℝ) ≤ uniformProbability (fun rows : RowSliceMatrix n d =>
            SourceKernelCompatible L a a₃ I ζ rows) := by
  have hCPos := sourceKernelLowerConstant_pos.trans_le hC
  have hZ : 0 ≤ max 0 Z₀ := le_max_left _ _
  have hHalf : a₃ ≤ 1 / 2 := by linarith
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_source_kernel_alternative_from_steep_exclusions_uniform hCPos ha₃ ha₃Small ha haOne σ (max 0 Z₀),
    eventually_source_shifted_T0_kernel_probability_uniform hCPos σ (max 0 Z₀),
    eventually_source_shifted_T1_kernel_probability_uniform (cw := 1 / 4) hCPos (by norm_num) (le_refl _) hZ σ,
    eventually_source_shifted_T2_kernel_probability_uniform (cw := 1 / 4) hCPos ha₃ hHalf (by norm_num)
      (le_refl _) ha₃Net hZ σ,
    eventually_source_row_load_failure_uniform hCPos ha₃ hHalf hEntropy σ]
      with n hConditions hAlternative hT₀ hT₁ hT₂ hLoad
  intro d hBand L hL I hI ζ hShift
  have h := hConditions d hBand.1 hBand.2
  have hShiftMax : ‖ζ‖ ≤ max 0 Z₀ * Real.sqrt d :=
    hShift.trans (mul_le_mul_of_nonneg_right (le_max_right 0 Z₀) (Real.sqrt_nonneg _))
  have hAlternativeHere : ∀ rows : RowSliceMatrix n d,
      SourceRowLoad I (thirdSteepScale n a₃) rows →
      (∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
      (∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
      (∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
        SourceKernelCompatible L a a₃ I ζ rows := by
    intro rows hLoad h₀ h₁ h₂
    exact hAlternative d hBand L hL I hI rows hLoad ζ hShiftMax h₀ h₁ h₂
  have h₀ := (uniformProbability_mono (fun rows hEvent => ⟨ζ, hShiftMax, hEvent⟩)).trans
    (hT₀ d hBand L hL I hI)
  have h₁ := hT₁ d hBand L hL I hI ζ hShiftMax
  have h₂ := hT₂ d hBand L hL I hI ζ hShiftMax
  have hLoadHere := hLoad d hBand L hL I hI
  have hFailure := (source_kernel_failure_union_bound I ζ hAlternativeHere).trans
    ((add_le_add (add_le_add (add_le_add h₀ h₁) h₂) hLoadHere).trans
      (source_kernel_four_rates_le_inverse_dimension h hC hBand.1))
  have hdn : d ≤ n := by have hN := (source_kernel_dimension_twice_degree h).2.2; omega
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_not] at hFailure
  linarith

/-- Full source theorem with an absolute admissible density range and
logarithmic lower constant. The explicit `4/n` is stronger than the
manuscript's unspecified absolute `C/n`. The lower constant is independent
of sigma, the fixed spectral window, both codimensions and retained sets. -/
def RectangularKernelCompatibilityTheorem : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 / 1000 ∧ ∃ Cstar : ℝ, 0 < Cstar ∧
    ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ a₀ → ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
          ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
            ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
              1 - 4 / (n : ℝ) ≤ uniformProbability (fun rows : RowSliceMatrix n d =>
                SourceKernelCompatible L a a₃ I ζ rows)

theorem rectangular_kernel_compatibility_theorem : RectangularKernelCompatibilityTheorem := by
  obtain ⟨aLoad, haLoad, haLoadSmall, hEntropy⟩ := source_row_load_small_constant
  let a₀ := min aLoad (equalBlockRateConstant (1 / 4) / 33600)
  have ha₀ : 0 < a₀ := lt_min haLoad
    (div_pos (equalBlockRateConstant_pos (by norm_num)) (by norm_num))
  refine ⟨a₀, ha₀, (min_le_left _ _).trans haLoadSmall,
    sourceKernelLowerConstant, sourceKernelLowerConstant_pos, ?_⟩
  intro a₃ ha₃ ha₃Bound a ha haOne C hC σ Z₀ _ _
  have haLoadBound := ha₃Bound.trans (min_le_left aLoad (equalBlockRateConstant (1 / 4) / 33600))
  have haSmall := haLoadBound.trans haLoadSmall
  have haRate := ha₃Bound.trans (min_le_right aLoad (equalBlockRateConstant (1 / 4) / 33600))
  have haNet : 7 * a₃ ≤ equalBlockRateConstant (1 / 4) / 4800 := by linarith
  exact eventually_atTop.mp (eventually_rectangular_kernel_compatibility_uniform hC ha₃ haSmall
    (hEntropy a₃ ha₃ haLoadBound) haNet ha haOne σ Z₀)

end CircularLaw
