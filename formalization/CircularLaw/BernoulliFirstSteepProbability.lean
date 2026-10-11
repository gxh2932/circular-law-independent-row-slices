import CircularLaw.BernoulliFirstSteepAction
import CircularLaw.BernoulliLLYAlmostReduction
import CircularLaw.LLYLeaveOneOutReduction

/-!
# Checked first-steep Bernoulli failures and reduction to the later classes

The two actual exceptional events are a row degree above 2d and a
missing unique-coordinate witness. Their estimates also cover one-row
deletion. The remaining steep inputs are the second and third classes.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def BernoulliLLYFirstSteepRetainedFailure {n : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (sample : BernoulliSquareSample n) (d ℓ r k : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyFirstSteep d ℓ r k ∧
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤ τ

theorem bernoulli_lly_first_steep_retained_failure_probability {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) {τ : ℝ}
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYFirstSteepRetainedFailure I ζ sample d ℓ r k τ} ≤
        (n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) +
          (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYFirstSteepRetainedFailure I ζ sample d ℓ r k τ} ⊆
      {sample | ¬BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample} ∪
        {sample | ¬BernoulliLLYFirstWitness d I ℓ r k sample} := by
    intro sample hFail
    by_cases hDegree : BernoulliRowDegreeUpperBound (2 * (d : ℝ)) sample
    · apply Or.inr
      intro hWitness
      obtain ⟨x, hUnit, hFirst, hSmallImage⟩ := hFail
      have hNorm := bernoulli_lly_first_steep_retained_norm (by omega : 0 < n) hd hℓ hk hkn
        I sample hDegree hWitness ζ hSpectral x hUnit hFirst
      exact not_lt_of_ge (hNorm.trans hSmallImage) hThreshold
    · exact Or.inl hDegree
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (sparse_bernoulli_row_degree_upper_failure (by omega : 0 < n) hdn)
    (bernoulli_lly_first_witness_failure_probability hn hd hdn hℓ hk hkn I hI hSmall hBudget)

def BernoulliLLYFirstSteepLeaveOneOutKernelFailure {n : ℕ} (ζ : ℂ)
    (sample : BernoulliSquareSample n) (i : Fin n) (d ℓ r k : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyFirstSteep d ℓ r k ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0

theorem bernoulli_lly_first_steep_leave_one_out_kernel_probability {n d ℓ r k : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (i : Fin n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k} ≤
        (n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) +
          (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  have hB := lly_first_steep_norm_constant_pos (r := r) (by omega : 0 < n) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hThreshold : (0 : ℝ) < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) := by positivity
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (bernoulli_lly_first_steep_retained_failure_probability (by omega : 3 ≤ n) hd hdn hℓ hk hkn
      (Finset.univ.erase i) (one_row_deleted_retained_card hn i) hSmall hBudget ζ hSpectral hThreshold)
  intro sample hFail
  obtain ⟨x, hUnit, hFirst, hKernel⟩ := hFail
  have hZero : (retainedShiftedBernoulliMatrix (Finset.univ.erase i) ζ sample).toEuclideanLin x = 0 := by
    ext j
    rw [retained_shifted_bernoulli_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1
  exact ⟨x, hUnit, hFirst, by rw [hZero, norm_zero]⟩

theorem bernoulli_lly_first_steep_rank_one_kernel_probability {n d ℓ r : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (ζ : ℂ) (i : Fin n) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d ℓ r 1} = 0 := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d ℓ r 1} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro sample hFail
    obtain ⟨x, _, hFirst, _⟩ := hFail
    rw [lly_first_steep_rank_one_empty hd hℓ] at hFirst
    exact hFirst
  rw [hEvent, measureReal_empty]

def BernoulliLLYLaterSteepAlmostRightFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
      (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x‖ ≤ τ

def BernoulliLLYLaterSteepAlmostAdjointFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
      (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).conjTranspose.toEuclideanLin x‖ ≤ τ

def BernoulliLLYLaterSteepLeaveOneOutKernelFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
      (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0

theorem bernoulli_lly_steep_almost_right_probability_le_later {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n)
    (hSmall : 16 * d * k₁ ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (δ ρ τ : ℝ)
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ≤
        ((n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) +
          (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d)) +
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYLaterSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ⊆
      {sample | BernoulliLLYFirstSteepRetainedFailure Finset.univ ζ sample d ℓ r k₁ τ} ∪
        {sample | BernoulliLLYLaterSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
    intro sample hFail
    obtain ⟨x, hUnit, hAlmost, hSteep, hNorm⟩ := hFail
    rcases hSteep with (hFirst | hSecond) | hThird
    · exact Or.inl ⟨x, hUnit, hFirst, (retained_shifted_bernoulli_norm_le_full Finset.univ ζ sample x).trans hNorm⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inl hSecond, hNorm⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inr hThird, hNorm⟩
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ (le_refl _)
  exact bernoulli_lly_first_steep_retained_failure_probability hn hd hdn hℓ hk₁ hk₁n Finset.univ
    (by simp only [Finset.card_univ, Fintype.card_fin]; nlinarith [Nat.cast_nonneg (α := ℝ) n])
    hSmall hBudget ζ hSpectral hThreshold

theorem bernoulli_lly_steep_leave_one_out_kernel_probability_le_later {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n)
    (hSmall : 16 * d * k₁ ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (i : Fin n) (δ ρ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} ≤
        ((n : ℝ) * Real.exp (-bernoulliDegreeUpperRate * d) +
          (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d)) +
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYLaterSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} ⊆
      {sample | BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁} ∪
        {sample | BernoulliLLYLaterSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} := by
    intro sample hFail
    obtain ⟨x, hUnit, hAlmost, hSteep, hKernel⟩ := hFail
    rcases hSteep with (hFirst | hSecond) | hThird
    · exact Or.inl ⟨x, hUnit, hFirst, hKernel⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inl hSecond, hKernel⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inr hThird, hKernel⟩
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add
    (bernoulli_lly_first_steep_leave_one_out_kernel_probability hn hd hdn hℓ hk₁ hk₁n
      hSmall hBudget ζ hSpectral i) (le_refl _)

theorem bernoulli_lly_later_steep_almost_adjoint_probability_eq_right {n d : ℕ}
    (ζ : ℂ) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYLaterSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} =
      (sparseBernoulliMatrixLaw n d).real {sample |
        BernoulliLLYLaterSteepAlmostRightFailure (star ζ) sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
  let E := fun A : Matrix (Fin n) (Fin n) ℂ =>
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
      ((fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∨
        (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) ∧
      ‖(A - star ζ • 1).toEuclideanLin x‖ ≤ τ
  simpa only [BernoulliLLYLaterSteepAlmostAdjointFailure, BernoulliLLYLaterSteepAlmostRightFailure,
    fullShiftedBernoulliMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, E] using sparse_bernoulli_adjoint_event_probability (d := d) E

end CircularLaw
