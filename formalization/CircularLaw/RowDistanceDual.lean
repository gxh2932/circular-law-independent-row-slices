import CircularLaw.RowDeletion
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Dual vectors determined by surviving row distances

The normalized leave-one-out residual is biorthogonal to the actual
conjugated rows and lies in their span. Its squared norm is the inverse
squared row distance. These are the geometric identities required to
identify the inverse row Gram matrix in the negative second-moment proof.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def leaveOneOutRowResidual {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
  (retainedRowSpan (H.erase i) ζ rows)ᗮ.starProjection (shiftedConjugateRow ζ rows i)

def leaveOneOutRowDual {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
  ((((leaveOneOutRowDistance H ζ rows i) ^ 2)⁻¹ : ℝ) : ℂ) • leaveOneOutRowResidual H ζ rows i

theorem leaveOneOutRowResidual_norm {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) :
    ‖leaveOneOutRowResidual H ζ rows i‖ = leaveOneOutRowDistance H ζ rows i :=
  orthogonalProjection_norm_eq_infDist _ _

theorem leaveOneOutRowResidual_sub_projection {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) :
    leaveOneOutRowResidual H ζ rows i = shiftedConjugateRow ζ rows i -
      (retainedRowSpan (H.erase i) ζ rows).starProjection (shiftedConjugateRow ζ rows i) := by
  unfold leaveOneOutRowResidual
  rw [Submodule.starProjection_orthogonal]
  rfl

theorem leaveOneOutRowResidual_mem_span {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {i : Fin n} (hi : i ∈ H) :
    leaveOneOutRowResidual H ζ rows i ∈ retainedRowSpan H ζ rows := by
  rw [leaveOneOutRowResidual_sub_projection]
  apply (retainedRowSpan H ζ rows).sub_mem
  · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · exact retainedRowSpan_mono (Finset.erase_subset i H) ζ rows
      ((retainedRowSpan (H.erase i) ζ rows).starProjection_apply_mem _)

theorem leaveOneOutRowDual_mem_span {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {i : Fin n} (hi : i ∈ H) :
    leaveOneOutRowDual H ζ rows i ∈ retainedRowSpan H ζ rows := by
  exact (retainedRowSpan H ζ rows).smul_mem _ (leaveOneOutRowResidual_mem_span H ζ rows hi)

theorem leaveOneOutRowResidual_inner_other {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {i j : Fin n} (hj : j ∈ H) (hji : j ≠ i) :
    ⟪leaveOneOutRowResidual H ζ rows i, shiftedConjugateRow ζ rows j⟫_ℂ = 0 := by
  have hRow : shiftedConjugateRow ζ rows j ∈ retainedRowSpan (H.erase i) ζ rows :=
    Submodule.subset_span ⟨⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩⟩, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hRow
    ((retainedRowSpan (H.erase i) ζ rows)ᗮ.starProjection_apply_mem _)

theorem leaveOneOutRowResidual_inner_self_row {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) :
    ⟪leaveOneOutRowResidual H ζ rows i, shiftedConjugateRow ζ rows i⟫_ℂ =
      (leaveOneOutRowDistance H ζ rows i : ℂ) ^ 2 := by
  let P := (retainedRowSpan (H.erase i) ζ rows).starProjection (shiftedConjugateRow ζ rows i)
  have hZero : ⟪leaveOneOutRowResidual H ζ rows i, P⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal
      ((retainedRowSpan (H.erase i) ζ rows).starProjection_apply_mem _)
      ((retainedRowSpan (H.erase i) ζ rows)ᗮ.starProjection_apply_mem _)
  have hRow : shiftedConjugateRow ζ rows i = leaveOneOutRowResidual H ζ rows i + P := by
    rw [leaveOneOutRowResidual_sub_projection]
    abel
  calc
    _ = ⟪leaveOneOutRowResidual H ζ rows i, leaveOneOutRowResidual H ζ rows i⟫_ℂ := by
      conv_lhs => rw [hRow]
      rw [inner_add_right, hZero, add_zero]
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K, leaveOneOutRowResidual_norm]
      rfl

theorem leaveOneOutRowDual_inner {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {i : Fin n}
    (hDistance : 0 < leaveOneOutRowDistance H ζ rows i) (j : H) :
    ⟪leaveOneOutRowDual H ζ rows i, retainedConjugateRow H ζ rows j⟫_ℂ =
      if i = j.val then 1 else 0 := by
  rw [retainedConjugateRow_eq_shiftedConjugateRow]
  by_cases h : i = j.val
  · subst i
    rw [if_pos rfl]
    rw [leaveOneOutRowDual, inner_smul_left, leaveOneOutRowResidual_inner_self_row]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, map_inv₀, map_pow, Complex.conj_ofReal]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hDistance.ne'))
  · rw [if_neg h]
    rw [leaveOneOutRowDual, inner_smul_left,
      leaveOneOutRowResidual_inner_other H ζ rows j.property (Ne.symm h), mul_zero]

theorem leaveOneOutRowDual_norm_sq {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {i : Fin n}
    (hDistance : 0 < leaveOneOutRowDistance H ζ rows i) :
    ‖leaveOneOutRowDual H ζ rows i‖ ^ 2 = (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ := by
  rw [leaveOneOutRowDual, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), leaveOneOutRowResidual_norm]
  field_simp

theorem surviving_rows_distance_energy {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    ∑ i ∈ H, (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ ≤ H.card / r ^ 2 := by
  calc
    _ ≤ ∑ _i ∈ H, (r ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hPow : r ^ 2 ≤ leaveOneOutRowDistance H ζ rows i ^ 2 :=
        pow_le_pow_left₀ hr.le (hDistance i hi) 2
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hr) hPow
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem surviving_rows_dual_energy {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i) :
    ∑ i ∈ H, ‖leaveOneOutRowDual H ζ rows i‖ ^ 2 ≤ H.card / r ^ 2 := by
  have hRewrite : (∑ i ∈ H, ‖leaveOneOutRowDual H ζ rows i‖ ^ 2) =
      ∑ i ∈ H, (leaveOneOutRowDistance H ζ rows i ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i hi
    exact leaveOneOutRowDual_norm_sq H ζ rows (hr.trans_le (hDistance i hi))
  rw [hRewrite]
  exact surviving_rows_distance_energy H ζ rows hr hDistance

end CircularLaw
