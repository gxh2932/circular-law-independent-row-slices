import CircularLaw.SourceGradualNormalization
import CircularLaw.UniformAlmostConstantLoad
import CircularLaw.AlmostConstantReduction
import CircularLaw.UniformSourceKernel

/-!
# Combining the deterministic source kernel arguments

The checked almost-constant reduction and row-load exclusion yield the
almost-constant part of the source event. Homogeneity then gives the exact
very-steep-or-gradual-cone alternative. The `T1` and `T2` exclusions are
explicit inputs of this deterministic bridge. `KernelCompatibility`
discharges them using the checked uniform net probability estimates and
completes the named source kernel theorem.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem source_almost_constant_exclusion_of_reduction {n d L : ℕ} {a₃ : ℝ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hReduction : (sourceAlmostConstant n d a₃ \ sourceS n d a₃ 12) \ {0} ⊆
      sourceShiftedSteepUnion n d L a₃)
    (h₀ : ∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₁ : ∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₂ : ∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (hLoad : ∀ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
      (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) :
    ∀ x ∈ sourceAlmostConstant n d a₃ \ sourceShiftedT3 n d L,
      x ≠ 0 → (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0 := by
  intro x hx hNZ hKernel
  by_cases hS : x ∈ sourceS n d a₃ 12
  · exact hLoad x ⟨hx.1, hS⟩ hKernel
  have hShift := hReduction ⟨⟨hx.1, hS⟩, by simpa only [Set.mem_singleton_iff] using hNZ⟩
  rw [sourceShiftedSteepUnion_eq] at hShift
  rcases hShift with ((h0 | h1) | h2) | h3
  · exact h₀ x h0 hKernel
  · exact h₁ x h1 hKernel
  · exact h₂ x h2 hKernel
  · exact hx.2 h3

theorem source_kernel_alternative_of_reduction_and_load {n d L : ℕ} {a₃ a : ℝ}
    (hk : 0 < thirdSteepScale n a₃) (hkn : thirdSteepScale n a₃ ≤ n)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hReduction : (sourceAlmostConstant n d a₃ \ sourceS n d a₃ 12) \ {0} ⊆
      sourceShiftedSteepUnion n d L a₃)
    (h₀ : ∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₁ : ∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (h₂ : ∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (hLoad : ∀ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
      (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0)
    (hVL : sourceShiftedT3 n d L ⊆ sourceVL n L a) :
    {x | x ≠ 0 ∧ (retainedShiftedMatrix I ζ rows).mulVec x = 0} ⊆
      sourceVL n L a ∪ nonzeroScalarCone (sourceGradual n d L a₃) :=
  source_kernel_alternative_of_class_exclusions hk hkn I ζ rows h₀ h₁ h₂
    (source_almost_constant_exclusion_of_reduction I ζ rows hReduction h₀ h₁ h₂ hLoad) hVL

theorem eventually_source_kernel_alternative_from_steep_exclusions_uniform {C a₃ a : ℝ}
    (hC : 0 < C) (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 1000)
    (ha : 0 < a) (haOne : a ≤ 1) (σ Z₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ rows : RowSliceMatrix n d, SourceRowLoad I (thirdSteepScale n a₃) rows →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            (∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
            (∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
            (∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
              {x | x ≠ 0 ∧ (retainedShiftedMatrix I ζ rows).mulVec x = 0} ⊆
                sourceVL n L a ∪ nonzeroScalarCone (sourceGradual n d L a₃) := by
  have hNSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_almost_constant_reduction_uniform ha₃ (by linarith) hC (1 + σ),
    eventually_source_almost_constant_load_exclusion_uniform hC ha₃ ha₃Small σ Z₀,
    eventually_source_shifted_T3_in_VL_uniform hC ha haOne σ, hNSize]
    with n hReduction hLoad hVL hNSize
  intro d hBand L hL I hI rows hRows ζ hζ h₀ h₁ h₂
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have hScaled := (div_le_iff₀ ha₃).mp hNSize
    nlinarith
  have hk := (thirdSteepScale_bounds ha₃ hSize).1
  have hkn : thirdSteepScale n a₃ ≤ n := by
    have hHalf := thirdSteepScale_half (n := n) ha₃.le (by linarith : a₃ ≤ 1 / 2)
    omega
  exact source_kernel_alternative_of_reduction_and_load hk hkn I ζ rows
    (hReduction d hBand.1 hBand.2 L hL) h₀ h₁ h₂ (hLoad d hBand L hL I hI rows hRows ζ hζ)
    (hVL d hBand L hL)

end CircularLaw
