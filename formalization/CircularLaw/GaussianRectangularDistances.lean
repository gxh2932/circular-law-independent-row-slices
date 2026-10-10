import CircularLaw.FiniteRowNegativeSecondMoment
import CircularLaw.GaussianRowExposure
import CircularLaw.GaussianConjugateLaw

/-!
# Quantitative inverse singular moments of actual shifted Gaussian rows

Conjugation preserves the actual row law. The common leave-one-out
distance bound therefore controls the Gram matrix `A A*` and the literal
ordered rectangular singular values, uniformly in every deterministic
matrix shift.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianShiftedRowMatrix {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ)
    (x : GaussianRowsSample m n) : Matrix (Fin m) (Fin n) ℂ := fun i j => x i j + B i j

theorem finite_row_distance_eq_leave_one_out {m n : ℕ}
    (rows : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (i : Fin (m + 1)) :
    finiteRowDistance rows i = finiteSpanDistance (rows i) (fun j => rows (i.succAbove j)) := by
  unfold finiteRowDistance finiteRowSpanExcept finiteSpanDistance
  rw [range_rows_except_eq_succAbove]

theorem gaussian_conjugate_rows_eq_shifted_rows {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℂ) (x : GaussianRowsSample m n) :
    complexConjugateRows (gaussianShiftedRowMatrix B x) = gaussianShiftedRows
      (fun i => WithLp.toLp 2 (fun j => star (B i j))) (fun i j => star (x i j)) := by
  funext i
  ext j
  change star (x i j + B i j) = star (x i j) + star (B i j)
  exact star_add _ _

theorem gaussian_conjugate_row_distance_eq {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (x : GaussianRowsSample (m + 1) n)
    (i : Fin (m + 1)) :
    finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i =
      gaussianLeaveOneOutDistance (fun k => WithLp.toLp 2 (fun j => star (B k j)))
        (fun k j => star (x k j)) i := by
  rw [finite_row_distance_eq_leave_one_out, gaussian_conjugate_rows_eq_shifted_rows]
  rfl

theorem measurable_gaussian_conjugate_row_distance {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (i : Fin (m + 1)) :
    Measurable (fun x => finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i) := by
  simp only [gaussian_conjugate_row_distance_eq]
  apply (measurable_gaussian_leave_one_out_distance _ i).comp
  exact measurable_pi_iff.mpr (fun k => measurable_pi_iff.mpr (fun j =>
    continuous_star.measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply k))))

theorem gaussian_conjugate_row_distances_bad_measurable {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (a : ℝ) :
    MeasurableSet {x | ∃ i, finiteRowDistance
      (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 ≤ a} := by
  have hUnion : MeasurableSet (⋃ i : Fin (m + 1),
      {x | finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 ≤ a}) :=
    MeasurableSet.iUnion (fun i => measurableSet_le
      ((measurable_gaussian_conjugate_row_distance B i).pow_const 2) measurable_const)
  simpa only [Set.iUnion_setOf] using hUnion

theorem gaussian_conjugate_row_distances_lower_eighth_tail {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (hmn : m < n) :
    (gaussianRowsLaw (m + 1) n).real
      {x | ∃ i, finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 ≤
        (n - m : ℕ) / (8 : ℝ)} ≤ (m + 1 : ℕ) * (1 / 2 : ℝ) ^ (n - m) := by
  let w : Fin (m + 1) → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun j => star (B i j))
  have hConj : Measurable (fun x : GaussianRowsSample (m + 1) n => fun i j => star (x i j)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j =>
      continuous_star.measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))))
  have hSet : MeasurableSet
      {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)} := by
    have hUnion : MeasurableSet (⋃ i : Fin (m + 1),
        {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)}) :=
      MeasurableSet.iUnion (fun i => measurableSet_le
        ((measurable_gaussian_leave_one_out_distance w i).pow_const 2) measurable_const)
    simpa only [Set.iUnion_setOf] using hUnion
  have hMap := map_measureReal_apply (μ := gaussianRowsLaw (m + 1) n) hConj hSet
  rw [gaussian_rows_conjugate_law] at hMap
  simp only [gaussian_conjugate_row_distance_eq]
  exact hMap.symm.trans_le (gaussian_all_row_distances_lower_eighth_tail w hmn)

theorem gaussian_rectangular_negative_second_moment_tail {m n : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin n) ℂ) (hmn : m < n) :
    (gaussianRowsLaw (m + 1) n).real
      {x | ¬ ((∀ j, 0 < orderedRectangularSingularValues (gaussianShiftedRowMatrix B x) j) ∧
        (∑ j, (orderedRectangularSingularValues (gaussianShiftedRowMatrix B x) j ^ 2)⁻¹) ≤
          8 * (m + 1 : ℕ) / (n - m : ℕ))} ≤
      (m + 1 : ℕ) * (1 / 2 : ℝ) ^ (n - m) := by
  apply (measureReal_mono (μ := gaussianRowsLaw (m + 1) n) (s₂ :=
    {x | ∃ i, finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 ≤
      (n - m : ℕ) / (8 : ℝ)}) ?_).trans
    (gaussian_conjugate_row_distances_lower_eighth_tail B hmn)
  intro x hx
  by_contra h
  have hCodim : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hDistance (i : Fin (m + 1)) : (n - m : ℕ) / (8 : ℝ) ≤
      finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i ^ 2 :=
    (lt_of_not_ge (fun hi => h ⟨i, hi⟩)).le
  have hPos (i : Fin (m + 1)) :
      0 < finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B x)) i := by
    nlinarith [hDistance i, finite_row_distance_nonneg
      (complexConjugateRows (gaussianShiftedRowMatrix B x)) i]
  apply hx
  refine ⟨rectangular_singular_values_pos_of_row_distances _ hPos, ?_⟩
  have hBound := rectangular_negative_second_moment_sq_bound (gaussianShiftedRowMatrix B x)
    (by positivity : (0 : ℝ) < (n - m : ℕ) / (8 : ℝ)) hDistance
  convert hBound using 1
  field_simp

end CircularLaw
