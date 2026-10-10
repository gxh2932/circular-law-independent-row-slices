import CircularLaw.InvertibilityDistanceGeometry
import CircularLaw.GaussianRowSpanExtension

/-!
# A unit normal chosen only from the other rows

The span of the n-1 other rows has dimension below n. The existing
least-coordinate projection construction therefore gives a unit normal
without any rank assumption. Updating the omitted row preserves this
normal, and its scalar form is bounded by the actual row distance.
-/

noncomputable section
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem finite_row_span_except_eq_range {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    finiteRowSpanExcept rows i =
      Submodule.span ℂ (Set.range (fun j : {j : Fin n // j ≠ i} => rows j.val)) := by
  have hSet : rows '' (Set.univ \ {i}) =
      Set.range (fun j : {j : Fin n // j ≠ i} => rows j.val) := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by simpa only [Set.mem_diff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] using hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, by simpa only [Set.mem_diff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] using j.property, rfl⟩
  unfold finiteRowSpanExcept
  rw [hSet]

theorem finite_row_span_except_finrank_lt {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    Module.finrank ℂ (finiteRowSpanExcept rows i) < n := by
  rw [finite_row_span_except_eq_range]
  have hRank := finrank_range_le_card (R := ℂ) (fun j : {j : Fin n // j ≠ i} => rows j.val)
  have hCard : Fintype.card {j : Fin n // j ≠ i} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (x := i) (by simp)
  simp only [Fintype.card_fin] at hCard
  exact hRank.trans_lt hCard

def leaveOneOutUnitNormal {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  enlargementUnitVector (finiteRowSpanExcept rows i)
    (enlargementEligibleCoordinates_nonempty _ (finite_row_span_except_finrank_lt rows i))

theorem leave_one_out_unit_normal_norm {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖leaveOneOutUnitNormal rows i‖ = 1 := enlargementUnitVector_norm _ _

theorem leave_one_out_unit_normal_mem_orthogonal {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    leaveOneOutUnitNormal rows i ∈ (finiteRowSpanExcept rows i)ᗮ :=
  enlargementUnitVector_mem_orthogonal _ _

theorem finite_row_span_except_congr {n : ℕ}
    (rows rows' : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n)
    (hRows : ∀ j, j ≠ i → rows j = rows' j) :
    finiteRowSpanExcept rows i = finiteRowSpanExcept rows' i := by
  rw [finite_row_span_except_eq_range, finite_row_span_except_eq_range]
  congr 1
  congr 1
  funext j
  exact hRows j.val j.property

theorem leave_one_out_unit_normal_congr {n : ℕ}
    (rows rows' : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n)
    (hRows : ∀ j, j ≠ i → rows j = rows' j) :
    leaveOneOutUnitNormal rows i = leaveOneOutUnitNormal rows' i := by
  unfold leaveOneOutUnitNormal
  congr 1
  exact finite_row_span_except_congr rows rows' i hRows

theorem leave_one_out_unit_normal_inner_other {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) {i j : Fin n} (hji : j ≠ i) :
    ⟪leaveOneOutUnitNormal rows i, rows j⟫_ℂ = 0 := by
  have hRow : rows j ∈ finiteRowSpanExcept rows i :=
    Submodule.subset_span ⟨j, by simpa only [Set.mem_diff, Set.mem_univ,
      Set.mem_singleton_iff, true_and] using hji, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hRow
    (leave_one_out_unit_normal_mem_orthogonal rows i)

theorem leave_one_out_unit_normal_inner_le_distance {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖⟪leaveOneOutUnitNormal rows i, rows i⟫_ℂ‖ ≤ finiteRowDistance rows i := by
  have hZero : ⟪leaveOneOutUnitNormal rows i,
      (finiteRowSpanExcept rows i).starProjection (rows i)⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal
      ((finiteRowSpanExcept rows i).starProjection_apply_mem _)
      (leave_one_out_unit_normal_mem_orthogonal rows i)
  have hInner : ⟪leaveOneOutUnitNormal rows i, rows i⟫_ℂ =
      ⟪leaveOneOutUnitNormal rows i, finiteRowResidual rows i⟫_ℂ := by
    rw [finite_row_residual_sub_projection, inner_sub_right, hZero, sub_zero]
  rw [hInner]
  simpa only [leave_one_out_unit_normal_norm, one_mul, finite_row_residual_norm] using
    norm_inner_le_norm (leaveOneOutUnitNormal rows i) (finiteRowResidual rows i)

end CircularLaw
