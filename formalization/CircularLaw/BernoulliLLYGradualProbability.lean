import CircularLaw.BernoulliLLYGradualRetained
import CircularLaw.BernoulliAdjointLaw
import CircularLaw.LLYGradualRadiusBudgets
import CircularLaw.LLYLeaveOneOutReduction

/-!
# Bernoulli gradual adjoint and leave-one-out kernel probabilities

Retained norms are bounded by full norms. Adjoint invariance transports
the actual right-action estimate, retaining the conjugated diagonal shift.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem retained_shifted_bernoulli_norm_le_full {n : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤
      ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [retained_shifted_bernoulli_apply_eq_full]
  rw [Finset.sum_coe_sort I
    (fun i : Fin n => ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i‖ ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => sq_nonneg _)

def BernoulliLLYGradualAlmostRightFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x‖ ≤ τ

def BernoulliLLYGradualAlmostAdjointFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).conjTranspose.toEuclideanLin x‖ ≤ τ

theorem bernoulli_lly_gradual_almost_adjoint_probability_eq_right {n d : ℕ}
    (ζ : ℂ) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYGradualAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} =
      (sparseBernoulliMatrixLaw n d).real {sample |
        BernoulliLLYGradualAlmostRightFailure (star ζ) sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
  let E := fun A : Matrix (Fin n) (Fin n) ℂ =>
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
      (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
      ‖(A - star ζ • 1).toEuclideanLin x‖ ≤ τ
  simpa only [BernoulliLLYGradualAlmostAdjointFailure, BernoulliLLYGradualAlmostRightFailure,
    fullShiftedBernoulliMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, E] using sparse_bernoulli_adjoint_event_probability (d := d) E

theorem bernoulli_lly_gradual_almost_right_failure_probability {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ a : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYGradualAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n) := by
  have hSubset : {sample : BernoulliSquareSample n |
      BernoulliLLYGradualAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ⊆
      {sample | BernoulliLLYGradualAlmostRetainedFailure Finset.univ ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
    rintro sample ⟨x, hUnit, hAlmost, hGradual, hSmall⟩
    exact ⟨x, hUnit, hAlmost, hGradual,
      (retained_shifted_bernoulli_norm_le_full Finset.univ ζ sample x).trans hSmall⟩
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  apply bernoulli_lly_gradual_almost_retained_failure_probability hn hd hdn hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius hThreshold
    ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension Finset.univ ?_ ζ hShift
  simp only [Finset.card_univ, Fintype.card_fin]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem bernoulli_lly_gradual_almost_adjoint_failure_probability {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ a : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYGradualAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n) := by
  rw [bernoulli_lly_gradual_almost_adjoint_probability_eq_right]
  exact bernoulli_lly_gradual_almost_right_failure_probability hn hd hdn hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius hThreshold
    ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension (star ζ) (by simpa only [norm_star] using hShift)

theorem bernoulli_lly_gradual_leave_one_out_kernel_probability {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ a : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) (i : Fin n) :
    (sparseBernoulliMatrixLaw n d).real {sample | ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
      (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
      ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0} ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n) := by
  have hSubset : {sample : BernoulliSquareSample n | ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
      (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
      ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0} ⊆
      {sample | BernoulliLLYGradualAlmostRetainedFailure (Finset.univ.erase i) ζ sample
        d ℓ r k₁ k₂ k₃ δ ρ 0} := by
    rintro sample ⟨x, hUnit, hAlmost, hGradual, hKernel⟩
    have hZero : (retainedShiftedBernoulliMatrix (Finset.univ.erase i) ζ sample).toEuclideanLin x = 0 := by
      ext j
      rw [retained_shifted_bernoulli_apply_eq_full]
      exact hKernel j.val (Finset.mem_erase.mp j.property).1
    exact ⟨x, hUnit, hAlmost, hGradual, by rw [hZero, norm_zero]⟩
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hB := lly_gradual_norm_constant_pos hnPos hd (r := r) (k₁ := k₁)
  have hThreshold : 0 < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) := by positivity
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  exact bernoulli_lly_gradual_almost_retained_failure_probability hnPos hd hdn hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius hThreshold
    ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension (Finset.univ.erase i)
    (one_row_deleted_retained_card hn i) ζ hShift

end CircularLaw
