import CircularLaw.RowAdditionSingularInterlacing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# The logarithmic increment from row insertion

The logarithms are the actual sums over retained singular values.
Positivity follows from a positive old product and a positive growth
threshold. The normalized exposure-step failure is contained in the
projection-small event; its probability estimate remains an input.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators

namespace CircularLaw

def leadingRowLogPrefix {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) : ℝ :=
  ∑ j : Fin r, -Real.log (orderedMatrixSingularValues A (leadingSingularIndex h j))

def insertedLeadingLogPrefix {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) : ℝ :=
  ∑ j : Fin (r + 1), -Real.log (orderedMatrixSingularValues (hybridInsertedRows A x)
    (insertedLeadingSingularIndex h j))

theorem leading_row_log_prefix_eq_neg_log_product {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hProd : leadingRowSingularProduct A h ≠ 0) :
    leadingRowLogPrefix A h = -Real.log (leadingRowSingularProduct A h) := by
  have hFactors := Finset.prod_ne_zero_iff.mp hProd
  rw [leadingRowLogPrefix, leadingRowSingularProduct, Real.log_prod hFactors,
    Finset.sum_neg_distrib]

theorem inserted_leading_log_prefix_eq_neg_log_product {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hProd : insertedLeadingSingularProduct A h x ≠ 0) :
    insertedLeadingLogPrefix A h x = -Real.log (insertedLeadingSingularProduct A h x) := by
  have hFactors := Finset.prod_ne_zero_iff.mp hProd
  rw [insertedLeadingLogPrefix, insertedLeadingSingularProduct, Real.log_prod hFactors,
    Finset.sum_neg_distrib]

theorem row_addition_log_increment_of_product_growth {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {η : ℝ} (hη : 0 < η)
    (hGrowth : η * leadingRowSingularProduct A h ≤ insertedLeadingSingularProduct A h x) :
    0 < insertedLeadingSingularProduct A h x ∧
      insertedLeadingLogPrefix A h x ≤ leadingRowLogPrefix A h - Real.log η := by
  have hNew := (mul_pos hη hOld).trans_le hGrowth
  refine ⟨hNew, ?_⟩
  rw [leading_row_log_prefix_eq_neg_log_product A h hOld.ne',
    inserted_leading_log_prefix_eq_neg_log_product A h x hNew.ne']
  have hLog := Real.log_le_log (mul_pos hη hOld) hGrowth
  rw [Real.log_mul hη.ne' hOld.ne'] at hLog
  linarith

theorem row_addition_normalized_log_increment_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {N δ : ℝ} (hN : 0 < N)
    (hProjection : Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection (rowAdjointVector x)‖) :
    insertedLeadingLogPrefix A h x / N ≤ leadingRowLogPrefix A h / N + δ := by
  have hGrowth := row_addition_product_bound_of_projection A h x hProjection
  have hLog := (row_addition_log_increment_of_product_growth A h x hOld (Real.exp_pos _) hGrowth).2
  rw [Real.log_exp] at hLog
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ leadingRowLogPrefix A h - (-N * δ) := hLog
    _ = _ := by field_simp; ring

theorem row_addition_normalized_log_increment_of_next_singular_value {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {N δ : ℝ} (hN : 0 < N)
    (hThreshold : Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
      ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    insertedLeadingLogPrefix A h x / N ≤ leadingRowLogPrefix A h / N + δ := by
  have hGrowth := row_addition_product_bound_of_next_singular_value A h hNext x hThreshold
  have hLog := (row_addition_log_increment_of_product_growth A h x hOld (Real.exp_pos _) hGrowth).2
  rw [Real.log_exp] at hLog
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ leadingRowLogPrefix A h - (-N * δ) := hLog
    _ = _ := by field_simp; ring

theorem row_addition_log_failure_probability_le_projection_small
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (X : Ω → EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {N δ : ℝ} (hN : 0 < N) :
    μ.real {ω | leadingRowLogPrefix A h / N + δ < insertedLeadingLogPrefix A h (X ω) / N} ≤
      μ.real {ω | ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
        (rowAdjointVector (X ω))‖ < Real.exp (-N * δ)} := by
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hFailure
  by_contra hNotSmall
  exact not_lt_of_ge (row_addition_normalized_log_increment_of_projection A h (X ω) hOld hN
    (le_of_not_gt hNotSmall)) hFailure

end CircularLaw
