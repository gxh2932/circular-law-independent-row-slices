import CircularLaw.HybridComparisonMatrix

/-!
# Exact trace and codimension lower bound for the hybrid comparison

Cyclic trace and the ridge inverse identity give a nonnegative correction
to `number of columns - number of other rows`. Entrywise conjugation
has the same real trace. No rank or trace estimate remains assumed.
-/

noncomputable section
open Classical
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem hybridComparisonMatrix_trace (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridComparisonMatrix K η).trace =
      (Fintype.card n : ℂ) - (Fintype.card m : ℂ) +
        (η ^ 2) • ((hybridRowRidgeGram K η)⁻¹).trace := by
  have hGram : K * Kᴴ = hybridRowRidgeGram K η - (η ^ 2) • 1 := by
    dsimp [hybridRowRidgeGram]
    abel
  have hCycle : (Kᴴ * (hybridRowRidgeGram K η)⁻¹ * K).trace =
      ((hybridRowRidgeGram K η)⁻¹ * (K * Kᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [hybridComparisonMatrix, Matrix.trace_sub, Matrix.trace_one, hCycle, hGram,
    Matrix.mul_sub, Matrix.nonsing_inv_mul _ (hybridRowRidgeGram_isUnit_det K hη),
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul]
  abel

theorem hybridComparisonMatrix_trace_re (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridComparisonMatrix K η).trace.re =
      (Fintype.card n : ℝ) - (Fintype.card m : ℝ) +
        η ^ 2 * ((hybridRowRidgeGram K η)⁻¹).trace.re := by
  simpa only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
    Complex.smul_re] using congrArg Complex.re (hybridComparisonMatrix_trace K hη)

theorem hybridComparisonMatrix_trace_ge_codimension (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (Fintype.card n : ℝ) - (Fintype.card m : ℝ) ≤ (hybridComparisonMatrix K η).trace.re := by
  have hTrace := (hybridRowRidgeGram_posDef K hη).inv.posSemidef.trace_nonneg
  have hRe : 0 ≤ ((hybridRowRidgeGram K η)⁻¹).trace.re := (Complex.nonneg_iff.mp hTrace).1
  rw [hybridComparisonMatrix_trace_re K hη]
  nlinarith [sq_nonneg η]

theorem hybridConjugateComparisonMatrix_trace (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridConjugateComparisonMatrix K η).trace = (hybridComparisonMatrix K η).trace := by
  rw [hybridConjugateComparisonMatrix_eq_transpose K hη, Matrix.trace_transpose]

theorem hybridConjugateComparisonMatrix_trace_ge_codimension (K : Matrix m n ℂ)
    {η : ℝ} (hη : 0 < η) :
    (Fintype.card n : ℝ) - (Fintype.card m : ℝ) ≤ (hybridConjugateComparisonMatrix K η).trace.re := by
  rw [hybridConjugateComparisonMatrix_trace K hη]
  exact hybridComparisonMatrix_trace_ge_codimension K hη

theorem hybridConjugateComparisonMatrix_trace_ge_row_codimension {N k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ N) (K : Matrix (Fin (k - 1)) (Fin N) ℂ)
    {η : ℝ} (hη : 0 < η) :
    ((N - k : ℕ) : ℝ) + 1 ≤ (hybridConjugateComparisonMatrix K η).trace.re := by
  have h := hybridConjugateComparisonMatrix_trace_ge_codimension K hη
  simp only [Fintype.card_fin] at h
  have hCast : ((N - k : ℕ) : ℝ) + 1 = (N : ℝ) - (k - 1 : ℕ) := by
    rw [Nat.cast_sub hkn, Nat.cast_sub hk]
    norm_num
    ring
  rw [hCast]
  exact h

end CircularLaw
