import CircularLaw.LLYFirstSteepProbability
import CircularLaw.LLYSecondSteepKernelProbability
import CircularLaw.LLYThirdSteepKernelProbability
import CircularLaw.LLYAlmostSteepSplit
import CircularLaw.RowSliceNonAlmostMinimumBound
import CircularLaw.LLYGradualRadiusBudgets

/-!
# Full minimum-value reduction retaining the almost-constant condition

Only the first and second kernel bounds use larger unrestricted classes.
The third kernel event keeps the unit-vector almost-constant condition
needed by its finite net. The strict first prefix includes the dense
rank-one case in both gradual branches.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem source_leave_one_out_almost_kernel_lly_split_preserving_almost {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {α ρ : ℝ}
    (hDensity : α * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) (rows : RowSliceMatrix n d) (i : Fin n)
    (hFail : sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i α ρ) :
    ((llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ ∨
      llySecondRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂) ∨
      llyThirdAlmostUnitRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂ k₃ α ρ) ∨
      ¬LLYRowLoad (Finset.univ.erase i) k₂ k₃ rows := by
  obtain ⟨x, hUnit, hAlmost, hKernel⟩ := hFail
  have hRetained : (retainedShiftedMatrix (Finset.univ.erase i) ζ rows).toEuclideanLin x = 0 := by
    ext j
    rw [retained_shifted_slice_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1
  by_cases hFirst : (fun j => x j) ∈ llyFirstSteep d ℓ r k₁
  · exact Or.inl (Or.inl (Or.inl ⟨x, hUnit, hFirst, hKernel⟩))
  by_cases hSecond : (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂
  · exact Or.inl (Or.inl (Or.inr ⟨x, hSecond, hRetained⟩))
  by_cases hThird : (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃
  · exact Or.inl (Or.inr ⟨x, hUnit, hThird, hAlmost, hRetained⟩)
  · right
    intro hLoad
    have hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ := by
      rintro ((h | h) | h)
      · exact hFirst h
      · exact hSecond h
      · exact hThird h
    exact lly_gradual_almost_retained_kernel_exclusion_of_prefix (by omega : 0 < n) hd
      hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius
      (Finset.univ.erase i) (one_row_deleted_retained_card hn i) rows hLoad ζ hShift
      x hUnit hGradual hAlmost hRetained

theorem source_leave_one_out_almost_kernel_probability_lly_split_preserving_almost {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {α ρ a : ℝ}
    (hDensity : α * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) (i : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i α ρ) ≤
      ((uniformProbability (fun rows : RowSliceMatrix n d =>
        llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁) +
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llySecondRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂)) +
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyThirdAlmostUnitRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂ k₃ α ρ)) +
        Real.exp (-(rowLoadRate / 4) * n) := by
  apply (uniformProbability_mono (fun rows hFail =>
    source_leave_one_out_almost_kernel_lly_split_preserving_almost hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
      hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius ζ hShift rows i hFail)).trans
  apply (uniformProbability_or_le _ _).trans
  apply add_le_add _ (lly_row_load_failure_absorbed hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃
    (Finset.univ.erase i) (one_row_deleted_retained_card hn i) hEntropy0 hEntropy hDimension)
  apply (uniformProbability_or_le _ _).trans
  apply add_le_add _ le_rfl
  exact uniformProbability_or_le _ _

theorem row_slice_smallest_probability_of_lly_almost_class_bounds {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hSize : 2 * d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {α ρ a η₁ η₂ η₃ κ₁ κ₂ κ₃ : ℝ}
    (hα : 0 < α) (hαOne : α ≤ 1) (hρ : 0 < ρ)
    (hDensity : α * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hFirstKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁) ≤ η₁)
    (hSecondKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂) ≤ η₂)
    (hThirdKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      llyThirdAlmostUnitRetainedKernelFailure (Finset.univ.erase i) ζ rows ℓ r k₁ k₂ k₃ α ρ) ≤ η₃)
    (hFirstAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepAdjointFailure ζ rows ℓ r k₁ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ₁)
    (hSecondAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ α ρ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ₂)
    (hThirdAdjoint : uniformProbability (fun rows : RowSliceMatrix n d =>
      llyThirdAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ₃) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      (((κ₁ + κ₂) + κ₃) + (n : ℝ) * Real.exp (-(d : ℝ) / 72)) +
        (sliceSmallBallDegreeConstant α / Real.sqrt d + ((η₁ + η₂) + η₃) +
          Real.exp (-(rowLoadRate / 4) * n)) / α := by
  have hdn : d ≤ n := by omega
  have hThreshold := lly_gradual_radius_smallest_threshold (by omega : 0 < n) hd hρ.le hRadius
  have hKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i α ρ) ≤
      ((η₁ + η₂) + η₃) + Real.exp (-(rowLoadRate / 4) * n) := by
    intro i
    apply (source_leave_one_out_almost_kernel_probability_lly_split_preserving_almost hn hd hdn hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius ha haOne hRank₂ hRank₃
      hEntropy0 hEntropy hDimension ζ hShift i).trans
    exact add_le_add (add_le_add (add_le_add (hFirstKernel i) (hSecondKernel i)) (hThirdKernel i)) le_rfl
  have hAlmost : uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) α ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      ((κ₁ + κ₂) + κ₃) + (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
    apply (source_almost_adjoint_probability_lly_split_preserving_almost ζ ℓ r k₁ k₂ k₃ α ρ
      ((ρ / Real.sqrt n) * ρ / Real.sqrt n)).trans
    exact add_le_add (add_le_add (add_le_add hFirstAdjoint hSecondAdjoint) hThirdAdjoint)
      (lly_gradual_almost_adjoint_failure_probability_of_prefix (by omega : 0 < n) hd hdn
        hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃ hFit hHalf (lly_first_rank_column_budget hd hPrefix)
        hScale₂ hScale₃ hDensity hRadius hThreshold ζ hShift)
  simpa only [add_assoc] using
    row_slice_smallest_probability_of_almost_constant_bounds hd hSize ζ hα hαOne hρ hKernel hAlmost

end CircularLaw
