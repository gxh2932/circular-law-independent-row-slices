import CircularLaw.BernoulliLLYGradualProbability
import CircularLaw.BernoulliNonAlmostMinimumBound

/-!
# Bernoulli minimum reduction retaining only the steep-class probabilities

The fresh-row scalar estimate and both gradual almost-constant branches
are supplied. The remaining probability inputs are the actual steep
adjoint and leave-one-out kernel events, with almost-constancy retained.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def BernoulliLLYSteepAlmostRightFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x‖ ≤ τ

def BernoulliLLYSteepAlmostAdjointFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedBernoulliMatrix ζ sample).conjTranspose.toEuclideanLin x‖ ≤ τ

def BernoulliLLYSteepLeaveOneOutKernelFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0

def BernoulliLLYGradualLeaveOneOutKernelFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0

theorem bernoulli_source_almost_adjoint_lly_split {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ)
    (hFail : sourceAlmostConstantAdjointFailure (fullShiftedBernoulliMatrix ζ sample) δ ρ τ) :
    BernoulliLLYSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ ∨
      BernoulliLLYGradualAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ := by
  obtain ⟨x, hUnit, hAlmost, hSmall⟩ := hFail
  by_cases hSteep : (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃
  · exact Or.inl ⟨x, hUnit, hAlmost, hSteep, hSmall⟩
  · exact Or.inr ⟨x, hUnit, hAlmost, hSteep, hSmall⟩

theorem bernoulli_source_almost_adjoint_probability_le_lly_components {n d : ℕ}
    (ζ : ℂ) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      sourceAlmostConstantAdjointFailure (fullShiftedBernoulliMatrix ζ sample) δ ρ τ} ≤
      (sparseBernoulliMatrixLaw n d).real {sample |
        BernoulliLLYSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} +
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYGradualAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
  have hSubset : {sample : BernoulliSquareSample n |
      sourceAlmostConstantAdjointFailure (fullShiftedBernoulliMatrix ζ sample) δ ρ τ} ⊆
      {sample | BernoulliLLYSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ∪
        {sample | BernoulliLLYGradualAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} :=
    fun sample hFail => bernoulli_source_almost_adjoint_lly_split ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ hFail
  exact (measureReal_mono hSubset (h₂ := by finiteness)).trans (measureReal_union_le _ _)

theorem bernoulli_source_leave_one_out_almost_kernel_lly_split {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ : ℝ)
    (hFail : bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ) :
    BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ ∨
      BernoulliLLYGradualLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ := by
  obtain ⟨x, hUnit, hAlmost, hKernel⟩ := hFail
  by_cases hSteep : (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃
  · exact Or.inl ⟨x, hUnit, hAlmost, hSteep, hKernel⟩
  · exact Or.inr ⟨x, hUnit, hAlmost, hSteep, hKernel⟩

theorem bernoulli_source_leave_one_out_almost_kernel_probability_le_lly_components {n d : ℕ}
    (ζ : ℂ) (i : Fin n) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ} ≤
      (sparseBernoulliMatrixLaw n d).real {sample |
        BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} +
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYGradualLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} := by
  have hSubset : {sample : BernoulliSquareSample n |
      bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ} ⊆
      {sample | BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} ∪
        {sample | BernoulliLLYGradualLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} :=
    fun sample hFail => bernoulli_source_leave_one_out_almost_kernel_lly_split
      ζ sample i d ℓ r k₁ k₂ k₃ δ ρ hFail
  exact (measureReal_mono hSubset (h₂ := by finiteness)).trans (measureReal_union_le _ _)

theorem bernoulli_lly_steep_almost_adjoint_probability_eq_right {n d : ℕ}
    (ζ : ℂ) (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} =
      (sparseBernoulliMatrixLaw n d).real {sample |
        BernoulliLLYSteepAlmostRightFailure (star ζ) sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
  let E := fun A : Matrix (Fin n) (Fin n) ℂ =>
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
      (fun j => x j) ∈ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
      ‖(A - star ζ • 1).toEuclideanLin x‖ ≤ τ
  simpa only [BernoulliLLYSteepAlmostAdjointFailure, BernoulliLLYSteepAlmostRightFailure,
    fullShiftedBernoulliMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, E] using sparse_bernoulli_adjoint_event_probability (d := d) E

theorem bernoulli_smallest_probability_of_lly_steep_bounds {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 100 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ a η κ : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ)
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hSteepKernel : ∀ i : Fin n, (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} ≤ η)
    (hSteepAdjoint : (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYSteepAlmostAdjointFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤ κ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      squareSmallestSingularFailure (fullShiftedBernoulliMatrix ζ sample)
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤
      (κ + (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n)) +
        (bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) + η +
          (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n)) / δ := by
  have hnPos : 0 < n := by omega
  have hdn : d ≤ n := by omega
  have hThreshold := lly_gradual_radius_smallest_threshold hnPos hd hρ.le hRadius
  have hKernel (i : Fin n) : (sparseBernoulliMatrixLaw n d).real {sample |
      bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ} ≤
      η + ((n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n)) := by
    apply (bernoulli_source_leave_one_out_almost_kernel_probability_le_lly_components
      ζ i ℓ r k₁ k₂ k₃ δ ρ).trans
    apply add_le_add (hSteepKernel i)
    exact bernoulli_lly_gradual_leave_one_out_kernel_probability hn hd hdn hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius
      ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension ζ hShift i
  have hAlmost : (sparseBernoulliMatrixLaw n d).real {sample |
      sourceAlmostConstantAdjointFailure (fullShiftedBernoulliMatrix ζ sample) δ ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤
      κ + ((n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n)) := by
    apply (bernoulli_source_almost_adjoint_probability_le_lly_components ζ ℓ r k₁ k₂ k₃ δ ρ _).trans
    apply add_le_add hSteepAdjoint
    exact bernoulli_lly_gradual_almost_adjoint_failure_probability hnPos hd hdn hk₁ hk₂ hk₃
      hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius hThreshold
      ha haOne hRank₂ hRank₃ hEntropy0 hEntropy hDimension ζ hShift
  simpa only [add_assoc] using bernoulli_smallest_probability_of_almost_constant_bounds
    hnPos hd hDegree ζ hδ hδOne hρ hKernel hAlmost

end CircularLaw
