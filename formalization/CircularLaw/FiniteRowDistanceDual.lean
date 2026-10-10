import CircularLaw.GaussianShiftSpanDistance
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Geometric duals for every finite complex row family

Leave-one-out residuals define biorthogonal dual vectors whenever all
row distances are positive. Their squared norms are the inverse squared
distances. These identities apply to arbitrary rows, including the
actual conjugated Gaussian rows used by singular-value counting.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

variable {ι : Type*} {n : ℕ}

def finiteRowSpan (rows : ι → EuclideanSpace ℂ (Fin n)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.span ℂ (Set.range rows)

def finiteRowSpanExcept (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.span ℂ (rows '' (Set.univ \ {i}))

def finiteRowDistance (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) : ℝ :=
  Metric.infDist (rows i) (finiteRowSpanExcept rows i : Set (EuclideanSpace ℂ (Fin n)))

def finiteRowResidual (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    EuclideanSpace ℂ (Fin n) := (finiteRowSpanExcept rows i)ᗮ.starProjection (rows i)

def finiteRowDual (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    EuclideanSpace ℂ (Fin n) := (((finiteRowDistance rows i ^ 2)⁻¹ : ℝ) : ℂ) • finiteRowResidual rows i

theorem finite_row_span_except_le (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    finiteRowSpanExcept rows i ≤ finiteRowSpan rows :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem finite_row_distance_nonneg (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    0 ≤ finiteRowDistance rows i := Metric.infDist_nonneg

theorem finite_row_distance_pos_of_linearIndependent (rows : ι → EuclideanSpace ℂ (Fin n))
    (hLI : LinearIndependent ℂ rows) (i : ι) : 0 < finiteRowDistance rows i := by
  have hNot := linearIndependent_iff_notMem_span.mp hLI i
  exact ((finiteRowSpanExcept rows i).closed_of_finiteDimensional.notMem_iff_infDist_pos
    ⟨0, (finiteRowSpanExcept rows i).zero_mem⟩).mp hNot

theorem finite_row_residual_norm (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    ‖finiteRowResidual rows i‖ = finiteRowDistance rows i := by
  rw [finiteRowResidual, Submodule.starProjection_orthogonal]
  change ‖rows i - (finiteRowSpanExcept rows i).starProjection (rows i)‖ =
    Metric.infDist (rows i) (finiteRowSpanExcept rows i : Set (EuclideanSpace ℂ (Fin n)))
  rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

theorem finite_row_residual_sub_projection (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    finiteRowResidual rows i = rows i - (finiteRowSpanExcept rows i).starProjection (rows i) := by
  rw [finiteRowResidual, Submodule.starProjection_orthogonal]
  rfl

theorem finite_row_residual_mem_span (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    finiteRowResidual rows i ∈ finiteRowSpan rows := by
  rw [finite_row_residual_sub_projection]
  exact (finiteRowSpan rows).sub_mem (Submodule.subset_span ⟨i, rfl⟩)
    (finite_row_span_except_le rows i ((finiteRowSpanExcept rows i).starProjection_apply_mem _))

theorem finite_row_dual_mem_span (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    finiteRowDual rows i ∈ finiteRowSpan rows :=
  (finiteRowSpan rows).smul_mem _ (finite_row_residual_mem_span rows i)

theorem finite_row_residual_inner_other (rows : ι → EuclideanSpace ℂ (Fin n))
    {i j : ι} (hji : j ≠ i) : ⟪finiteRowResidual rows i, rows j⟫_ℂ = 0 := by
  have hRow : rows j ∈ finiteRowSpanExcept rows i :=
    Submodule.subset_span ⟨j, by simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]; exact hji, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hRow
    ((finiteRowSpanExcept rows i)ᗮ.starProjection_apply_mem _)

theorem finite_row_residual_inner_self_row (rows : ι → EuclideanSpace ℂ (Fin n)) (i : ι) :
    ⟪finiteRowResidual rows i, rows i⟫_ℂ = (finiteRowDistance rows i : ℂ) ^ 2 := by
  let P := (finiteRowSpanExcept rows i).starProjection (rows i)
  have hZero : ⟪finiteRowResidual rows i, P⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal ((finiteRowSpanExcept rows i).starProjection_apply_mem _)
      ((finiteRowSpanExcept rows i)ᗮ.starProjection_apply_mem _)
  have hRow : rows i = finiteRowResidual rows i + P := by
    rw [finite_row_residual_sub_projection]
    abel
  calc
    _ = ⟪finiteRowResidual rows i, finiteRowResidual rows i⟫_ℂ := by
      conv_lhs => rw [hRow]
      rw [inner_add_right, hZero, add_zero]
    _ = _ := by rw [inner_self_eq_norm_sq_to_K, finite_row_residual_norm]; rfl

theorem finite_row_dual_inner (rows : ι → EuclideanSpace ℂ (Fin n))
    {i : ι} (hi : 0 < finiteRowDistance rows i) (j : ι) :
    ⟪finiteRowDual rows i, rows j⟫_ℂ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst i
    rw [if_pos rfl, finiteRowDual, inner_smul_left, finite_row_residual_inner_self_row]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, map_inv₀, map_pow, Complex.conj_ofReal]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hi.ne'))
  · rw [if_neg h, finiteRowDual, inner_smul_left, finite_row_residual_inner_other rows (Ne.symm h), mul_zero]

theorem finite_row_dual_norm_sq (rows : ι → EuclideanSpace ℂ (Fin n))
    {i : ι} (hi : 0 < finiteRowDistance rows i) :
    ‖finiteRowDual rows i‖ ^ 2 = (finiteRowDistance rows i ^ 2)⁻¹ := by
  rw [finiteRowDual, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), finite_row_residual_norm]
  field_simp

end CircularLaw
