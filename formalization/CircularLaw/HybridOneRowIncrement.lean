import CircularLaw.HybridLogPotential
import CircularLaw.OneRowLogComparison

/-!
# Checked expected hybrid increment with the other rows fixed

Every comparison-matrix hypothesis of the one-row logarithmic theorem
is discharged from the actual ridge matrix. The upper bound is uniform
over all other rows and all shifts with the specified norm cap.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

def rowReplacementUpperBound (n : ℕ) (η R : ℝ) : ℝ :=
  Real.sqrt (η ^ 2 + (Real.sqrt (n : ℝ) + R) ^ 2)

theorem regularizedDistance_upperBound_of_shift_norm {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u x : EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : ‖u‖ ≤ R)
    (hx : ‖x‖ ≤ Real.sqrt (n : ℝ)) :
    regularizedDistance P η u x ≤ rowReplacementUpperBound n η R := by
  apply (regularizedDistance_le_euclidean_bound hP η u x hx).trans
  apply Real.sqrt_le_sqrt
  apply add_le_add_right
  exact pow_le_pow_left₀ (by positivity) (add_le_add_right hR (Real.sqrt (n : ℝ))) 2

theorem hybrid_one_row_expected_increment {Ω : Type*} [MeasurableSpace Ω]
    {n d k : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (K : Matrix (Fin (k - 1)) (Fin n) ℂ) {η : ℝ} (hη : 0 < η)
    (u : EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : ‖u‖ ≤ R)
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → RowSlice n d) (hX : Measurable X) (hXlaw : μ.map X = rowSliceLaw n d)
    (Y : Ω → (Fin n → Bool)) (hY : Measurable Y)
    (hYlaw : μ.map Y = bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn)) :
    (∫ ω, |regularizedRowPotential (hybridInsertedRows K (rowSliceEuclideanRow (X ω) + u)) η -
      regularizedRowPotential (hybridInsertedRows K (bernoulliCubeVector (Y ω) + u)) η| ∂μ) ≤
      9216 * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d (n - k)) +
        (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) *
          Real.log (rowReplacementUpperBound n η R / η) *
            Real.exp (-(1 / 262144) * rowLogComparisonQ n d (n - k)) := by
  have hP := hybridConjugateComparisonMatrix_positive_contraction K hη
  have hTrace := hybridConjugateComparisonMatrix_trace_ge_row_codimension hk hkn.le K hη
  have hU : ∀ᵐ ω ∂μ,
      regularizedDistance (hybridConjugateComparisonMatrix K η) η u (rowSliceEuclideanRow (X ω)) ≤
        rowReplacementUpperBound n η R ∧
      regularizedDistance (hybridConjugateComparisonMatrix K η) η u (bernoulliCubeVector (Y ω)) ≤
        rowReplacementUpperBound n η R := by
    apply ae_of_all
    intro ω
    exact ⟨regularizedDistance_upperBound_of_shift_norm hP η u _ hR (rowSliceEuclideanRow_norm_le _),
      regularizedDistance_upperBound_of_shift_norm hP η u _ hR (by
        simpa only [Fintype.card_fin] using bernoulliCubeVector_norm_le (Y ω))⟩
  have h := one_row_log_comparison hd hdn hP hTrace η hη u hQ μ X hX hXlaw Y hY hYlaw
    (rowReplacementUpperBound n η R) hU
  simp_rw [regularizedRowPotential_hybrid_increment K hη u]
  exact h

end CircularLaw
