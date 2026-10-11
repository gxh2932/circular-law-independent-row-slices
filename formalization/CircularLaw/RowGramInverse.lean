import CircularLaw.RowDistanceDual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The inverse row Gram matrix and actual leave-one-out distances

Biorthogonality reconstructs every vector in the retained row span.
It follows that the inverse row Gram matrix is the Gram matrix of the
geometric dual vectors. Its diagonal entries and trace are therefore
the inverse squared actual row distances. `RowNegativeSecondMoment.lean`
supplies the spectral conversion to inverse squared singular values.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem retainedRowDual_expansion {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ retainedRowSpan H ζ rows) :
    (∑ j : H, ⟪leaveOneOutRowDual H ζ rows j.val, x⟫_ℂ • retainedConjugateRow H ζ rows j) = x := by
  have hBi (i j : H) :
      ⟪leaveOneOutRowDual H ζ rows i.val, retainedConjugateRow H ζ rows j⟫_ℂ =
        if i = j then 1 else 0 := by
    simpa only [Subtype.ext_iff] using
      leaveOneOutRowDual_inner H ζ rows (hDistance i.val i.property) j
  change x ∈ Submodule.span ℂ (Set.range (retainedConjugateRow H ζ rows)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp [hBi]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, hx, hy]
  | smul a x _ hx =>
    simp only [inner_smul_right, mul_smul, ← Finset.smul_sum, hx]

theorem retainedRowGram_mul_dualGram {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) :
    Matrix.gram ℂ (retainedConjugateRow H ζ rows) *
      Matrix.gram ℂ (fun i : H => leaveOneOutRowDual H ζ rows i.val) = 1 := by
  ext i j
  change (∑ k : H, ⟪retainedConjugateRow H ζ rows i, retainedConjugateRow H ζ rows k⟫_ℂ *
      ⟪leaveOneOutRowDual H ζ rows k.val, leaveOneOutRowDual H ζ rows j.val⟫_ℂ) =
        if i = j then 1 else 0
  calc
    _ = ⟪retainedConjugateRow H ζ rows i,
        ∑ k : H, ⟪leaveOneOutRowDual H ζ rows k.val, leaveOneOutRowDual H ζ rows j.val⟫_ℂ •
          retainedConjugateRow H ζ rows k⟫_ℂ := by
      simp only [inner_sum, inner_smul_right, mul_comm]
    _ = ⟪retainedConjugateRow H ζ rows i, leaveOneOutRowDual H ζ rows j.val⟫_ℂ := by
      rw [retainedRowDual_expansion H ζ rows hDistance _ (leaveOneOutRowDual_mem_span H ζ rows j.property)]
    _ = _ := by
      rw [← inner_conj_symm, leaveOneOutRowDual_inner H ζ rows (hDistance j.val j.property) i]
      by_cases h : i = j
      · subst j
        simp
      · have hji : j.val ≠ i.val := fun hEq => h (Subtype.ext hEq.symm)
        simp [h, hji]

theorem retainedRowGram_inverse {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) :
    (Matrix.gram ℂ (retainedConjugateRow H ζ rows))⁻¹ =
      Matrix.gram ℂ (fun i : H => leaveOneOutRowDual H ζ rows i.val) :=
  Matrix.inv_eq_right_inv (retainedRowGram_mul_dualGram H ζ rows hDistance)

theorem retainedRowGram_inverse_diagonal {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) (i : H) :
    (Matrix.gram ℂ (retainedConjugateRow H ζ rows))⁻¹ i i =
      ((leaveOneOutRowDistance H ζ rows i.val ^ 2)⁻¹ : ℝ) := by
  rw [retainedRowGram_inverse H ζ rows hDistance, Matrix.gram_apply, inner_self_eq_norm_sq_to_K]
  change (‖leaveOneOutRowDual H ζ rows i.val‖ : ℂ) ^ 2 =
    (((leaveOneOutRowDistance H ζ rows i.val ^ 2)⁻¹ : ℝ) : ℂ)
  simpa only [Complex.ofReal_pow] using congrArg Complex.ofReal
    (leaveOneOutRowDual_norm_sq H ζ rows (hDistance i.val i.property))

theorem retainedRowGram_inverse_trace {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d)
    (hDistance : ∀ i ∈ H, 0 < leaveOneOutRowDistance H ζ rows i) :
    ((Matrix.gram ℂ (retainedConjugateRow H ζ rows))⁻¹).trace.re =
      ∑ i ∈ H, (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    retainedRowGram_inverse_diagonal H ζ rows hDistance, Complex.ofReal_re]
  exact Finset.sum_coe_sort H (fun i => (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹)

theorem surviving_rows_inverse_trace_bound {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    ((Matrix.gram ℂ (retainedConjugateRow H ζ rows))⁻¹).trace.re ≤ H.card / r ^ 2 := by
  rw [retainedRowGram_inverse_trace H ζ rows (fun i hi => hr.trans_le (hDistance i hi))]
  exact surviving_rows_distance_energy H ζ rows hr hDistance

end CircularLaw
