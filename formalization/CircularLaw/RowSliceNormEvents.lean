import CircularLaw.RowSliceMatrixDiscrepancy

/-!
# Joint discrepancy and degree events for the norm proof

The actual rectangular matrix is nonnegative, has row sums `d`, and
on this event has column sums at most `9*d` and source discrepancy.
The two failure probabilities combine to any prescribed inverse power
under the explicit logarithmic degree condition. The heavy estimate and
finite-net operator assembly are proved in the downstream norm modules.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def RowSliceDegreeDiscrepancy {m n d : ℕ} (beta : ℝ) (rows : Fin m → RowSlice n d) : Prop :=
  MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (rectangularSliceMatrixReal rows) ∧
    MatrixRowColumnBound (9 * d) (rectangularSliceMatrixReal rows)

theorem rowSliceDegreeDiscrepancy_failure_union {m n d : ℕ} (beta : ℝ) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceDegreeDiscrepancy beta rows) ≤
      uniformProbability (fun rows : Fin m → RowSlice n d =>
        ¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) +
      uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceColumnBound (9 * d) rows) := by
  have hCover : ∀ rows : Fin m → RowSlice n d, ¬RowSliceDegreeDiscrepancy beta rows →
      (¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) ∨ ¬RowSliceColumnBound (9 * d) rows := by
    intro rows hFail
    by_cases hDP : RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows
    · right
      intro hColumn
      exact hFail ⟨(rectangularSliceMatrixReal_discrepancy_iff rows _ _).mpr hDP,
        (rectangularSliceMatrixReal_rowColumnBound_iff rows).mpr hColumn⟩
    · exact Or.inl hDP
  apply (uniformProbability_mono hCover).trans
  exact uniformProbability_or_le _ _

theorem rowSliceDegreeDiscrepancy_failure_probability {m n d : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceDegreeDiscrepancy beta rows) ≤
      (n : ℝ) ^ (-beta) + (n : ℝ) * Real.exp (-9 * d) := by
  apply (rowSliceDegreeDiscrepancy_failure_union beta).trans
  exact add_le_add (rowSliceDiscrepancy_failure_probability hn hmn hd hdn hBeta)
    (rowSliceColumn_failure_probability hm hn hmn hd hdn)

theorem inverse_dimension_two_term_budget {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    (n : ℝ) ^ (-(A + 1)) + (n : ℝ) ^ (-(A + 1)) ≤ (n : ℝ) ^ (-A) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ = 2 * (n : ℝ) ^ (-(A + 1)) := by ring
    _ ≤ (n : ℝ) * (n : ℝ) ^ (-(A + 1)) :=
      mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(A + 1)) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + (-(A + 1))) := (Real.rpow_add hnR _ _).symm
    _ = (n : ℝ) ^ (-A) := by congr 1; ring

theorem rowSliceDegreeDiscrepancy_failure_polynomial {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) (hDegree : (A + 2) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceDegreeDiscrepancy (A + 1) rows) ≤
      (n : ℝ) ^ (-A) := by
  have hnPos : 0 < n := by omega
  have hBeta : 0 ≤ A + 1 := by linarith only [hA]
  have hColumn := rowSliceColumn_failure_polynomial hm hnPos hmn hd hdn (A + 1) (by
    simpa only [add_assoc, one_add_one_eq_two] using hDegree)
  exact (rowSliceDegreeDiscrepancy_failure_union (A + 1)).trans
    ((add_le_add (rowSliceDiscrepancy_failure_probability hnPos hmn hd hdn hBeta) hColumn).trans
      (inverse_dimension_two_term_budget hn A))

end CircularLaw
