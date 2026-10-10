import CircularLaw.LLYFirstWitnessProbability
import CircularLaw.LLYLeaveOneOutReduction

/-!
# First-steep small images and the remaining leave-one-out classes

The first class has a proved simultaneous norm and kernel estimate on
the actual row-slice law. Splitting the full steep event leaves only
the second and third classes as right-kernel probability obligations.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyFirstSteepRetainedFailure {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (ℓ r k : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyFirstSteep d ℓ r k ∧
    ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x‖ ≤ τ

theorem lly_first_steep_retained_failure_probability {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) {τ : ℝ}
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepRetainedFailure I ζ rows ℓ r k τ) ≤
        (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  apply (uniformProbability_mono ?_).trans
    (lly_first_witness_failure_probability hn hd hdn hℓ hk hkn I hI hSmall hBudget)
  intro rows hFail hWitness
  obtain ⟨x, hUnit, hFirst, hSmallImage⟩ := hFail
  have hNorm := lly_first_steep_retained_norm (by omega : 0 < n) hd hℓ hk hkn
    I rows hWitness ζ hSpectral x hUnit hFirst
  exact not_lt_of_ge (hNorm.trans hSmallImage) hThreshold

def llyFirstSteepLeaveOneOutKernelFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (i : Fin n) (ℓ r k : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyFirstSteep d ℓ r k ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0

theorem lly_first_steep_rank_one_kernel_probability {n d ℓ r : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    (ζ : ℂ) (i : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r 1) = 0 := by
  have hEvent : (fun rows : RowSliceMatrix n d =>
      llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r 1) = (fun _ => False) := by
    funext rows
    apply propext
    constructor
    · rintro ⟨x, _, hFirst, _⟩
      rw [lly_first_steep_rank_one_empty hd hℓ] at hFirst
      exact hFirst
    · exact False.elim
  rw [hEvent]
  simp [uniformProbability]

theorem lly_first_steep_leave_one_out_kernel_probability {n d ℓ r k : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (i : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r k) ≤
        (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  apply (uniformProbability_mono ?_).trans
    (lly_first_witness_failure_probability (by omega : 3 ≤ n) hd hdn hℓ hk hkn
      (Finset.univ.erase i) (one_row_deleted_retained_card hn i) hSmall hBudget)
  intro rows hFail hWitness
  obtain ⟨x, hUnit, hFirst, hKernel⟩ := hFail
  apply lly_first_steep_retained_kernel_exclusion (by omega : 0 < n) hd hℓ hk hkn
    (Finset.univ.erase i) rows hWitness ζ hSpectral x hUnit hFirst
  ext j
  rw [retained_shifted_slice_apply_eq_full]
  exact hKernel j.val (Finset.mem_erase.mp j.property).1

def llyLaterSteepLeaveOneOutKernelFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (i : Fin n) (ℓ r k₁ k₂ k₃ : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
      (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0

theorem lly_steep_leave_one_out_kernel_split {n d ℓ r k₁ k₂ k₃ : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n)
    (hFail : llySteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) :
    llyFirstSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ ∨
      llyLaterSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃ := by
  obtain ⟨x, hUnit, hSteep, hKernel⟩ := hFail
  rcases hSteep with (hFirst | hSecond) | hThird
  · exact Or.inl ⟨x, hUnit, hFirst, hKernel⟩
  · exact Or.inr ⟨x, hUnit, Or.inl hSecond, hKernel⟩
  · exact Or.inr ⟨x, hUnit, Or.inr hThird, hKernel⟩

theorem lly_steep_leave_one_out_probability_le_later {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n)
    (hSmall : 16 * d * k₁ ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (i : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) ≤
        (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) +
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llyLaterSteepLeaveOneOutKernelFailure ζ rows i ℓ r k₁ k₂ k₃) := by
  apply (uniformProbability_mono (fun rows hFail =>
    lly_steep_leave_one_out_kernel_split ζ rows i hFail)).trans
    ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add (lly_first_steep_leave_one_out_kernel_probability hn hd hdn hℓ hk₁ hk₁n
    hSmall hBudget ζ hSpectral i) (le_refl _)

end CircularLaw
