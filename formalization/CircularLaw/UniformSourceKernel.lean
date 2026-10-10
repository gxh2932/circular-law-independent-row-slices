import CircularLaw.UniformSourceKernelConditions
import CircularLaw.SourceSteepExclusion
import CircularLaw.SourceVerySteepInclusion

/-!
# Uniform source kernel inputs

These thresholds apply to every degree in the literal lower band and
both codimensions. The `T0` event simultaneously covers every spectral
shift in the prescribed window; the permitted `T3` inclusion retains
the actual floor normal rank.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_source_steep_witness_failure_uniform {C : ℝ} (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceSteepWitness I L rows) ≤
          Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) := by
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ)] with n hConditions
  intro d hBand L hL I hI
  have h := hConditions d hBand.1 hBand.2
  exact source_steep_witness_failure h.degree_large h.dimension_fourth h.dimension_root hL I hI
    h.stride_pos h.stride_upper h.witness_entropy h.scale_prefactor

theorem eventually_source_shifted_T0_kernel_probability_uniform {C : ℝ} (hC : 0 < C) (σ Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ∃ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d ∧ ∃ v ∈ sourceShiftedT0 n d L,
            (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
          Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) := by
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC (eventually_fixed_shift_witness_window Z₀)]
    with n hConditions hWindow
  intro d hBand L hL I hI
  have h := hConditions d hBand.1 hBand.2
  apply (uniformProbability_mono ?_).trans
    (source_shifted_T0_kernel_probability h.degree_large h.dimension_fourth h.dimension_root
      hL I hI h.stride_pos h.stride_upper h.witness_entropy h.scale_prefactor)
  intro rows hEvent
  obtain ⟨ζ, hSpectral, v, hv, hKernel⟩ := hEvent
  exact ⟨ζ, hWindow d hBand.1 ζ hSpectral, v, hv, hKernel⟩

theorem eventually_source_shifted_T3_in_VL_uniform {C a : ℝ} (hC : 0 < C)
    (ha : 0 < a) (haOne : a ≤ 1) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → sourceShiftedT3 n d L ⊆ sourceVL n L a := by
  have hDegree : ∀ᶠ d : ℕ in atTop, 8 / a ≤ Real.sqrt d ∧ 1 / a ≤ (d : ℝ) := by
    filter_upwards [(Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop (8 / a),
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop (1 / a)]
      with d hRoot hSize
    exact ⟨hRoot, hSize⟩
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC hDegree] with n hConditions hDegree
  intro d hBand L hL
  have h := hConditions d hBand.1 hBand.2
  have hD := hDegree d hBand.1
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hLReal : 2 * (d : ℝ) ≤ L := by
    exact_mod_cast kernelCodimension_large_lower hd h.dimension_fourth hL
  have hDScaled := (div_le_iff₀ ha).mp hD.2
  have hLScaled := mul_le_mul_of_nonneg_left hLReal ha.le
  have hSize : 2 ≤ a * (L : ℝ) := by nlinarith
  exact source_shifted_T3_in_VL ha haOne h.degree_large h.dimension_fourth h.dimension_root
    hL h.stride_pos h.stride_upper hD.1 hSize

end CircularLaw
