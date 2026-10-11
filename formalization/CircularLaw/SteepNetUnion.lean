import CircularLaw.SteepKernelNormalization
import CircularLaw.RowLoadFailure

/-!
# Finite steep-net probability reduction

The witness failure is kept outside the net union bound. Each source
kernel vector gives a normalized finite-grid approximant; the union is
over the actual Cartesian product of the nonconstant and constant nets.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem finite_net_event_probability {α ι κ : Type*} [Fintype α]
    (N : Finset ι) (C : Finset κ) (E W : α → Prop) (F : ι → κ → α → Prop)
    {P : ℝ} (hCover : ∀ a, E a → ∃ u ∈ N, ∃ w ∈ C, F u w a)
    (hSmall : ∀ u ∈ N, ∀ w ∈ C, uniformProbability (fun a => F u w a ∧ W a) ≤ P) :
    uniformProbability E ≤ uniformProbability (fun a => ¬W a) + (N.card : ℝ) * C.card * P := by
  let G : ι × κ → α → Prop := fun uw a => F uw.1 uw.2 a ∧ W a
  have hEvent : ∀ a, E a → ¬W a ∨ ∃ uw ∈ N ×ˢ C, G uw a := by
    intro a ha
    by_cases hW : W a
    · obtain ⟨u, hu, w, hw, hF⟩ := hCover a ha
      exact Or.inr ⟨(u, w), Finset.mem_product.mpr ⟨hu, hw⟩, hF, hW⟩
    · exact Or.inl hW
  apply (uniformProbability_mono hEvent).trans
  apply (uniformProbability_or_le _ _).trans
  apply add_le_add (le_refl _)
  apply (uniformProbability_finset_exists_le (N ×ˢ C) G).trans
  calc
    _ ≤ ∑ _uw ∈ N ×ˢ C, P := by
      apply Finset.sum_le_sum
      intro uw huw
      obtain ⟨hu, hw⟩ := Finset.mem_product.mp huw
      exact hSmall uw.1 hu uw.2 hw
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]

theorem source_shifted_T1_kernel_finite_net_bound {n d L : ℕ} {cw Z₀ P : ℝ}
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hZ : 0 ≤ Z₀)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (hSmall : ∀ u ∈ sourceT1Net n d, ∀ w ∈ steepConstantNet d 1,
      uniformProbability (fun rows : RowSliceMatrix n d =>
        shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤
          2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ∧
            UniformEqualBlockWitness cw (firstSteepScale n d) (fun i : I => rows i.val)) ≤ P) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬UniformEqualBlockWitness cw (firstSteepScale n d) (fun i : I => rows i.val)) +
            ((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card * P := by
  apply finite_net_event_probability _ _ _ _ _ ?_ hSmall
  intro rows hEvent
  obtain ⟨v, hv, hKernel⟩ := hEvent
  obtain ⟨x, hx, hNorm, c, hc, hNormalizedKernel⟩ :=
    source_shifted_T1_kernel_normalization I ζ rows v hv hKernel
  exact normalized_shifted_sourceT1_kernel_net h hL hCubic hZ I ζ hShift rows x hx hNorm c hc hNormalizedKernel

theorem source_shifted_T2_kernel_finite_net_bound {n d L : ℕ} {a₃ cw Z₀ P : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hL : IsKernelCodimension n d L)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hZ : 0 ≤ Z₀)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d)
    (hSmall : ∀ u ∈ sourceT2Net n d a₃, ∀ w ∈ steepConstantNet d (Real.rpow (d : ℝ) (3 / 2)),
      uniformProbability (fun rows : RowSliceMatrix n d =>
        shiftedRowsL2Norm (fun i : I => rows i.val) u w ζ (fun i => i.val) ≤
          2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) ∧
            UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) ≤ P) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ¬UniformEqualBlockWitness cw (equalBlockScale n d) (fun i : I => rows i.val)) +
            ((sourceT2Net n d a₃).card : ℝ) *
              (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card * P := by
  apply finite_net_event_probability _ _ _ _ _ ?_ hSmall
  intro rows hEvent
  obtain ⟨v, hv, hKernel⟩ := hEvent
  obtain ⟨x, hx, hNorm, c, hc, hNormalizedKernel⟩ :=
    source_shifted_T2_kernel_normalization I ζ rows v hv hKernel
  exact normalized_shifted_sourceT2_kernel_net ha haOne hSize h hL hCubic hZ I ζ hShift
    rows x hx hNorm c hc hNormalizedKernel

end CircularLaw
