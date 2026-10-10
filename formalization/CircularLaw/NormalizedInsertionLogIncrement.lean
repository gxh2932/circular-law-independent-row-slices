import CircularLaw.InsertionDegreeNormalization

/-!
# Actual degree-normalized row and column logarithmic steps

A positive old retained product and growth by sqrt(d) times exp(-N*delta)
give a positive new retained product and the required normalized log step.
Failure includes a zero new product, so Real.log 0 cannot hide singularity.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators

namespace CircularLaw

theorem row_addition_degree_normalized_success_of_product_growth {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hGrowth : (Real.sqrt d * Real.exp (-N * δ)) * leadingRowSingularProduct A h ≤
      insertedLeadingSingularProduct A h x) :
    0 < insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedRowLogPrefix d A h x / N ≤
        degreeNormalizedLeadingLogPrefix d A h / N + δ := by
  obtain ⟨hNew, hLog⟩ := row_addition_log_increment_of_product_growth A h x hOld
    (mul_pos (Real.sqrt_pos.mpr hd) (Real.exp_pos _)) hGrowth
  refine ⟨(inserted_leading_singular_product_degree_normalization_pos_iff A h x hd).mpr hNew, ?_⟩
  rw [Real.log_mul (Real.sqrt_pos.mpr hd).ne' (Real.exp_pos _).ne', Real.log_exp] at hLog
  have hStep : degreeNormalizedInsertedRowLogPrefix d A h x ≤
      degreeNormalizedLeadingLogPrefix d A h + N * δ := by
    rw [inserted_row_log_prefix_degree_normalization A h x hd hNew.ne',
      leading_row_log_prefix_degree_normalization A h hd hOld.ne']
    push_cast
    linarith
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ degreeNormalizedLeadingLogPrefix d A h + N * δ := hStep
    _ = _ := by field_simp

theorem row_addition_degree_normalized_success_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hProjection : Real.sqrt d * Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection (rowAdjointVector x)‖) :
    0 < insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedRowLogPrefix d A h x / N ≤
        degreeNormalizedLeadingLogPrefix d A h / N + δ :=
  row_addition_degree_normalized_success_of_product_growth A h x hOld hd hN
    (row_addition_product_bound_of_projection A h x hProjection)

theorem row_addition_degree_normalized_success_of_next_singular_value {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
      ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    0 < insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedRowLogPrefix d A h x / N ≤
        degreeNormalizedLeadingLogPrefix d A h / N + δ :=
  row_addition_degree_normalized_success_of_product_growth A h x hOld hd hN
    (row_addition_product_bound_of_next_singular_value A h hNext x hThreshold)

theorem column_addition_degree_normalized_success_of_product_growth {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hGrowth : (Real.sqrt d * Real.exp (-N * δ)) * leadingRowSingularProduct A hRow ≤
      insertedColumnLeadingSingularProduct A hNext x) :
    0 < insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) hNext (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedColumnLogPrefix d A hNext x / N ≤
        degreeNormalizedLeadingLogPrefix d A hRow / N + δ := by
  have hOldAdj : 0 < leadingRowSingularProduct A.conjTranspose hCol := by
    rwa [← leading_row_singular_product_conjTranspose A hRow hCol]
  have hGrowthAdj : (Real.sqrt d * Real.exp (-N * δ)) * leadingRowSingularProduct A.conjTranspose hCol ≤
      insertedLeadingSingularProduct A.conjTranspose hCol (rowAdjointVector x) := by
    rwa [← leading_row_singular_product_conjTranspose A hRow hCol,
      ← inserted_column_product_eq_adjoint_row_product A hCol hNext x]
  obtain ⟨hNew, hLog⟩ := row_addition_log_increment_of_product_growth A.conjTranspose hCol
    (rowAdjointVector x) hOldAdj (mul_pos (Real.sqrt_pos.mpr hd) (Real.exp_pos _)) hGrowthAdj
  rw [← inserted_column_product_eq_adjoint_row_product A hCol hNext x] at hNew
  rw [← inserted_column_log_prefix_eq_adjoint_row_prefix A hCol hNext x,
    ← leading_row_log_prefix_conjTranspose A hRow hCol,
    Real.log_mul (Real.sqrt_pos.mpr hd).ne' (Real.exp_pos _).ne', Real.log_exp] at hLog
  refine ⟨(inserted_column_singular_product_degree_normalization_pos_iff A hNext x hd).mpr hNew, ?_⟩
  have hStep : degreeNormalizedInsertedColumnLogPrefix d A hNext x ≤
      degreeNormalizedLeadingLogPrefix d A hRow + N * δ := by
    rw [inserted_column_log_prefix_degree_normalization A hNext x hd hNew.ne',
      leading_row_log_prefix_degree_normalization A hRow hd hOld.ne']
    push_cast
    linarith
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ degreeNormalizedLeadingLogPrefix d A hRow + N * δ := hStep
    _ = _ := by field_simp

theorem column_addition_degree_normalized_success_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hProjection : Real.sqrt d * Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection x‖) :
    0 < insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) hNext (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedColumnLogPrefix d A hNext x / N ≤
        degreeNormalizedLeadingLogPrefix d A hRow / N + δ :=
  column_addition_degree_normalized_success_of_product_growth A hRow hCol hNext x hOld hd hN
    (column_addition_product_bound_of_projection A hRow hCol hNext x hProjection)

theorem column_addition_degree_normalized_success_of_next_singular_value {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m)
    (hNextRow : r + 1 ≤ n) (hNextCol : r + 1 ≤ m)
    (x : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
      ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    0 < insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) hNextRow (degreeNormalizingScalar d • x) ∧
      degreeNormalizedInsertedColumnLogPrefix d A hNextRow x / N ≤
        degreeNormalizedLeadingLogPrefix d A hRow / N + δ := by
  apply column_addition_degree_normalized_success_of_product_growth A hRow hCol hNextRow x hOld hd hN
  rw [leading_row_singular_product_conjTranspose A hRow hCol,
    inserted_column_product_eq_adjoint_row_product A hCol hNextRow x]
  apply row_addition_product_bound_of_next_singular_value A.conjTranspose hCol hNextCol (rowAdjointVector x)
  rwa [← ordered_matrix_singular_values_conjTranspose A
    ⟨r, by simp only [Fintype.card_fin]; omega⟩
    ⟨r, by simp only [Fintype.card_fin]; omega⟩ rfl]

def degreeNormalizedRowStepFailure {r n m : ℕ} (d N δ : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) : Prop :=
  insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) = 0 ∨
    degreeNormalizedLeadingLogPrefix d A h / N + δ < degreeNormalizedInsertedRowLogPrefix d A h x / N

def degreeNormalizedColumnStepFailure {r n m : ℕ} (d N δ : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin n)) : Prop :=
  insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) hNext (degreeNormalizingScalar d • x) = 0 ∨
    degreeNormalizedLeadingLogPrefix d A hRow / N + δ < degreeNormalizedInsertedColumnLogPrefix d A hNext x / N

theorem not_degree_normalized_row_failure_iff {r n m : ℕ} (d N δ : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    ¬ degreeNormalizedRowStepFailure d N δ A h x ↔
      0 < insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ∧
        degreeNormalizedInsertedRowLogPrefix d A h x / N ≤ degreeNormalizedLeadingLogPrefix d A h / N + δ := by
  rw [degreeNormalizedRowStepFailure, not_or, not_lt]
  constructor
  · rintro ⟨hNe, hStep⟩
    exact ⟨lt_of_le_of_ne (inserted_leading_singular_product_nonneg _ _ _) (Ne.symm hNe), hStep⟩
  · rintro ⟨hPos, hStep⟩
    exact ⟨hPos.ne', hStep⟩

theorem not_degree_normalized_column_failure_iff {r n m : ℕ} (d N δ : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ¬ degreeNormalizedColumnStepFailure d N δ A hRow hNext x ↔
      0 < insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) hNext (degreeNormalizingScalar d • x) ∧
        degreeNormalizedInsertedColumnLogPrefix d A hNext x / N ≤ degreeNormalizedLeadingLogPrefix d A hRow / N + δ := by
  have hNonneg : 0 ≤ insertedColumnLeadingSingularProduct
      (degreeNormalizingScalar d • A) hNext (degreeNormalizingScalar d • x) :=
    Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
  rw [degreeNormalizedColumnStepFailure, not_or, not_lt]
  constructor
  · rintro ⟨hNe, hStep⟩
    exact ⟨lt_of_le_of_ne hNonneg (Ne.symm hNe), hStep⟩
  · rintro ⟨hPos, hStep⟩
    exact ⟨hPos.ne', hStep⟩

theorem row_degree_normalized_failure_projection_small {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    (hOld : 0 < leadingRowSingularProduct A h) {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hFailure : degreeNormalizedRowStepFailure d N δ A h x) :
    ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection (rowAdjointVector x)‖ <
      Real.sqrt d * Real.exp (-N * δ) := by
  by_contra hNot
  obtain ⟨hNew, hStep⟩ := row_addition_degree_normalized_success_of_projection A h x hOld hd hN
    (le_of_not_gt hNot)
  rcases hFailure with hZero | hLog
  · exact hNew.ne' hZero
  · exact not_lt_of_ge hStep hLog

theorem column_degree_normalized_failure_projection_small {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hFailure : degreeNormalizedColumnStepFailure d N δ A hRow hNext x) :
    ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection x‖ <
      Real.sqrt d * Real.exp (-N * δ) := by
  by_contra hNot
  obtain ⟨hNew, hStep⟩ := column_addition_degree_normalized_success_of_projection A hRow hCol hNext x hOld
    hd hN (le_of_not_gt hNot)
  rcases hFailure with hZero | hLog
  · exact hNew.ne' hZero
  · exact not_lt_of_ge hStep hLog

theorem row_degree_normalized_failure_probability_le_projection_small
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (X : Ω → EuclideanSpace ℂ (Fin m)) (hOld : 0 < leadingRowSingularProduct A h)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N) :
    μ.real {ω | degreeNormalizedRowStepFailure d N δ A h (X ω)} ≤
      μ.real {ω | ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
        (rowAdjointVector (X ω))‖ < Real.sqrt d * Real.exp (-N * δ)} := by
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hFailure
  exact row_degree_normalized_failure_projection_small A h (X ω) hOld hd hN hFailure

theorem column_degree_normalized_failure_probability_le_projection_small
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m)
    (hNext : r + 1 ≤ n) (X : Ω → EuclideanSpace ℂ (Fin n))
    (hOld : 0 < leadingRowSingularProduct A hRow) {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N) :
    μ.real {ω | degreeNormalizedColumnStepFailure d N δ A hRow hNext (X ω)} ≤
      μ.real {ω | ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection
        (X ω)‖ < Real.sqrt d * Real.exp (-N * δ)} := by
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hFailure
  exact column_degree_normalized_failure_projection_small A hRow hCol hNext (X ω) hOld hd hN hFailure

end CircularLaw
