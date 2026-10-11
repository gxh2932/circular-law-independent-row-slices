import CircularLaw.FiniteRowDistanceDual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Inverse Gram trace for arbitrary finite row families

The Gram matrix of the geometric duals is a right inverse of the actual
row Gram matrix. Its trace is exactly the sum of inverse squared
leave-one-out distances.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem finite_row_dual_expansion (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ finiteRowSpan rows) :
    (∑ j, ⟪finiteRowDual rows j, x⟫_ℂ • rows j) = x := by
  have hBi (i j : ι) : ⟪finiteRowDual rows i, rows j⟫_ℂ = if i = j then 1 else 0 := by
    by_cases h : i = j <;> simpa [h] using finite_row_dual_inner rows (hDistance i) j
  change x ∈ Submodule.span ℂ (Set.range rows) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp [hBi]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, hx, hy]
  | smul a x _ hx =>
    simp only [inner_smul_right, mul_smul, ← Finset.smul_sum, hx]

theorem finite_row_gram_mul_dual_gram (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) :
    Matrix.gram ℂ rows * Matrix.gram ℂ (finiteRowDual rows) = 1 := by
  ext i j
  change (∑ k, ⟪rows i, rows k⟫_ℂ * ⟪finiteRowDual rows k, finiteRowDual rows j⟫_ℂ) =
    if i = j then 1 else 0
  calc
    _ = ⟪rows i, ∑ k, ⟪finiteRowDual rows k, finiteRowDual rows j⟫_ℂ • rows k⟫_ℂ := by
      simp only [inner_sum, inner_smul_right, mul_comm]
    _ = ⟪rows i, finiteRowDual rows j⟫_ℂ := by
      rw [finite_row_dual_expansion rows hDistance _ (finite_row_dual_mem_span rows j)]
    _ = _ := by
      rw [← inner_conj_symm, finite_row_dual_inner rows (hDistance j) i]
      by_cases h : i = j
      · subst j
        simp
      · simp [h, Ne.symm h]

theorem finite_row_gram_inverse (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) :
    (Matrix.gram ℂ rows)⁻¹ = Matrix.gram ℂ (finiteRowDual rows) :=
  Matrix.inv_eq_right_inv (finite_row_gram_mul_dual_gram rows hDistance)

theorem finite_row_gram_inverse_diagonal (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) (i : ι) :
    (Matrix.gram ℂ rows)⁻¹ i i = ((finiteRowDistance rows i ^ 2)⁻¹ : ℝ) := by
  rw [finite_row_gram_inverse rows hDistance, Matrix.gram_apply, inner_self_eq_norm_sq_to_K]
  change (‖finiteRowDual rows i‖ : ℂ) ^ 2 = (((finiteRowDistance rows i ^ 2)⁻¹ : ℝ) : ℂ)
  simpa only [Complex.ofReal_pow] using congrArg Complex.ofReal
    (finite_row_dual_norm_sq rows (hDistance i))

theorem finite_row_gram_inverse_trace (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) :
    ((Matrix.gram ℂ rows)⁻¹).trace.re = ∑ i, (finiteRowDistance rows i ^ 2)⁻¹ := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    finite_row_gram_inverse_diagonal rows hDistance, Complex.ofReal_re]

end CircularLaw
