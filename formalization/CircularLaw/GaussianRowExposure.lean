import CircularLaw.GaussianProductCurry
import CircularLaw.GaussianIndependentSpanDistance
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Exposing each actual Gaussian matrix row

The row product law splits into all other rows and an independent fresh
row. The checked conditional distance estimates therefore apply to every
actual leave-one-out distance. A finite union gives their common lower
bound, and their almost sure positivity proves full row rank.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianShiftedRows {m n : ℕ} (w : Fin m → EuclideanSpace ℂ (Fin n))
    (x : GaussianRowsSample m n) (i : Fin m) : EuclideanSpace ℂ (Fin n) :=
  standardComplexGaussianVector n (x i) + w i

def gaussianFreshRowExposure {m n : ℕ} (i : Fin (m + 1))
    (x : GaussianRowsSample (m + 1) n) : GaussianRowsSample m n × (Fin n → ℂ) :=
  (fun j => x (i.succAbove j), x i)

theorem gaussian_fresh_row_exposure_measurePreserving {m n : ℕ} (i : Fin (m + 1)) :
    MeasurePreserving (gaussianFreshRowExposure (n := n) i) (gaussianRowsLaw (m + 1) n)
      ((gaussianRowsLaw m n).prod (standardComplexGaussianVectorLaw n)) := by
  exact (Measure.measurePreserving_swap (μ := standardComplexGaussianVectorLaw n)
    (ν := gaussianRowsLaw m n)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => standardComplexGaussianVectorLaw n) i)

def gaussianLeaveOneOutDistance {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n))
    (x : GaussianRowsSample (m + 1) n) (i : Fin (m + 1)) : ℝ :=
  finiteSpanDistance (gaussianShiftedRows w x i) (fun j => gaussianShiftedRows w x (i.succAbove j))

theorem measurable_gaussian_leave_one_out_distance {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (i : Fin (m + 1)) :
    Measurable (fun x => gaussianLeaveOneOutDistance w x i) := by
  apply measurable_finite_span_distance
  · exact ((standardComplexGaussianVector_continuous n).comp (continuous_apply i)).add continuous_const
  · intro j
    exact ((standardComplexGaussianVector_continuous n).comp
      (continuous_apply (i.succAbove j))).add continuous_const

theorem gaussian_leave_one_out_distance_lower_eighth_tail {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (hmn : m < n) (i : Fin (m + 1)) :
    (gaussianRowsLaw (m + 1) n).real
      {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)} ≤
        (1 / 2 : ℝ) ^ (n - m) := by
  let rows : Fin m → GaussianRowsSample m n → EuclideanSpace ℂ (Fin n) :=
    fun j x => standardComplexGaussianVector n (x j) + w (i.succAbove j)
  let shift : GaussianRowsSample m n → EuclideanSpace ℂ (Fin n) := fun _ => w i
  have hRows (j : Fin m) : Continuous (rows j) :=
    ((standardComplexGaussianVector_continuous n).comp (continuous_apply j)).add continuous_const
  have hShift : Continuous shift := continuous_const
  have hMeas := measurable_independent_gaussian_span_distance rows shift hRows hShift
  have hMap := map_measureReal_apply (μ := gaussianRowsLaw (m + 1) n)
    (s := {p | independentGaussianSpanDistance rows shift p ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)})
    (gaussian_fresh_row_exposure_measurePreserving (n := n) i).measurable
    (measurableSet_le (hMeas.pow_const 2) measurable_const)
  rw [(gaussian_fresh_row_exposure_measurePreserving (n := n) i).map_eq] at hMap
  apply hMap.symm.trans_le
  simpa only [Fintype.card_fin] using independent_gaussian_span_distance_lower_eighth_tail
    (gaussianRowsLaw m n) rows shift hRows hShift (by simpa only [Fintype.card_fin] using hmn)

theorem gaussian_leave_one_out_distance_pos_ae {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (hmn : m < n) (i : Fin (m + 1)) :
    ∀ᵐ x ∂gaussianRowsLaw (m + 1) n, 0 < gaussianLeaveOneOutDistance w x i := by
  let rows : Fin m → GaussianRowsSample m n → EuclideanSpace ℂ (Fin n) :=
    fun j x => standardComplexGaussianVector n (x j) + w (i.succAbove j)
  have hRows (j : Fin m) : Continuous (rows j) :=
    ((standardComplexGaussianVector_continuous n).comp (continuous_apply j)).add continuous_const
  exact (gaussian_fresh_row_exposure_measurePreserving (n := n) i).quasiMeasurePreserving.ae
    (independent_gaussian_span_distance_pos_ae (gaussianRowsLaw m n) rows (fun _ => w i)
      hRows continuous_const (by simpa only [Fintype.card_fin] using hmn))

theorem gaussian_all_row_distances_lower_eighth_tail {m n : ℕ}
    (w : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (hmn : m < n) :
    (gaussianRowsLaw (m + 1) n).real
      {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)} ≤
        (m + 1 : ℕ) * (1 / 2 : ℝ) ^ (n - m) := by
  let A := fun i : Fin (m + 1) =>
    {x | gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)}
  have hEq : {x | ∃ i, gaussianLeaveOneOutDistance w x i ^ 2 ≤ (n - m : ℕ) / (8 : ℝ)} =
      ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))), A i := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left, A]
  rw [hEq]
  calc
    _ ≤ ∑ i : Fin (m + 1), (gaussianRowsLaw (m + 1) n).real (A i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i : Fin (m + 1), (1 / 2 : ℝ) ^ (n - m) :=
      Finset.sum_le_sum (fun i _ => gaussian_leave_one_out_distance_lower_eighth_tail w hmn i)
    _ = _ := by simp

theorem range_rows_except_eq_succAbove {m : ℕ} {E : Type*} (rows : Fin (m + 1) → E)
    (i : Fin (m + 1)) :
    rows '' (Set.univ \ {i}) = Set.range (fun j => rows (i.succAbove j)) := by
  rw [show (fun j => rows (i.succAbove j)) = rows ∘ i.succAbove from rfl,
    Set.range_comp, Fin.range_succAbove]
  congr 1
  ext j
  simp

theorem gaussian_shifted_rows_linearIndependent_ae {m n : ℕ}
    (w : Fin m → EuclideanSpace ℂ (Fin n)) (hmn : m ≤ n) :
    ∀ᵐ x ∂gaussianRowsLaw m n, LinearIndependent ℂ (gaussianShiftedRows w x) := by
  cases m with
  | zero => exact ae_of_all _ (fun _ => linearIndependent_empty_type)
  | succ m =>
    have hPos : ∀ᵐ x ∂gaussianRowsLaw (m + 1) n,
        ∀ i, 0 < gaussianLeaveOneOutDistance w x i :=
      ae_all_iff.mpr (fun i => gaussian_leave_one_out_distance_pos_ae w (by omega) i)
    filter_upwards [hPos] with x hx
    apply linearIndependent_iff_notMem_span.mpr
    intro i hMem
    rw [range_rows_except_eq_succAbove] at hMem
    have hZero := Metric.infDist_zero_of_mem hMem
    exact (hx i).ne' hZero

end CircularLaw
