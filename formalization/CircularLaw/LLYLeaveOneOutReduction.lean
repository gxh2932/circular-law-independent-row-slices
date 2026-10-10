import CircularLaw.LLYGradualRetained

/-!
# The actual leave-one-out almost-constant kernel event reduced to steep vectors

The original full-square sample is retained throughout. The deleted row
is removed from the deterministic index set, so its shift remains the
original ambient diagonal. No independence of a vector-dependent set
is assumed.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem retained_shifted_slice_apply_eq_full {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) (x : EuclideanSpace ℂ (Fin n)) (j : I) :
    (retainedShiftedMatrix I ζ rows).toEuclideanLin x j =
      (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j.val := by
  change (retainedShiftedMatrix I ζ rows).mulVec (fun k => x k) j = _
  rw [retainedShiftedMatrix_mulVec, shifted_slice_matrix_apply_eq_row_form]

theorem one_row_deleted_retained_card {n : ℕ} (hn : 100 ≤ n) (i : Fin n) :
    (99 / 100 : ℝ) * n ≤ (Finset.univ.erase i).card := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have h : (100 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

def llySteepLeaveOneOutKernelFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (i : Fin n) (ℓ r k₁ k₂ k₃ : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0

theorem source_leave_one_out_almost_kernel_lly_split {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) (rows : RowSliceMatrix n d) (i : Fin n)
    (hFail : sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) :
    llySteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃ ∨
      ¬LLYRowLoad (Finset.univ.erase i) k₂ k₃ rows := by
  obtain ⟨x, hUnit, hAlmost, hKernel⟩ := hFail
  by_cases hSteep : (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃
  · exact Or.inl ⟨x, hUnit, hSteep, hKernel⟩
  · right
    intro hLoad
    have hNot := lly_gradual_almost_retained_kernel_exclusion (by omega) hd hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hk₁Small hScale₂ hScale₃ hDensity hRadius
      (Finset.univ.erase i) (one_row_deleted_retained_card hn i) rows hLoad ζ hShift x hUnit hSteep hAlmost
    apply hNot
    ext j
    rw [retained_shifted_slice_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1

theorem source_leave_one_out_almost_kernel_probability_le_lly_steep {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ a : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) (i : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d => sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) ≤
      uniformProbability (fun rows : RowSliceMatrix n d =>
        llySteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) +
      Real.exp (-(rowLoadRate / 4) * n) := by
  apply (uniformProbability_mono (fun rows hFail => source_leave_one_out_almost_kernel_lly_split
    hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hk₁Small hScale₂ hScale₃ hDensity hRadius
    ζ hShift rows i hFail)).trans ((uniformProbability_or_le _ _).trans ?_)
  apply add_le_add (le_refl _)
  exact lly_row_load_failure_absorbed hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃
    (Finset.univ.erase i) (one_row_deleted_retained_card hn i) hEntropy0 hEntropy hDimension

end CircularLaw
