import CircularLaw.RowSliceNormalizedLogComparison

/-!
# The actual row-slice circular law from its normalized logarithmic limit

Degree normalization has energy per dimension at most one, including
zero degree and dimension. To apply the probability-space hermitization
criterion in every dimension we use `min(d,n)`, which equals the actual
degree eventually. Exact eventual equality returns the conclusion to
the original uniform row-slice law and variance normalization.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology ENNReal

namespace CircularLaw

theorem degree_normalized_row_slice_energy_le {n d : ℕ} (rows : RowSliceMatrix n d) :
    squareMatrixEnergy (degreeNormalizedMatrix rows) ≤ n := by
  by_cases hd : d = 0
  · simp [degreeNormalizedMatrix, hd, squareMatrixEnergy]
  · exact (degree_normalized_matrix_energy rows (Nat.pos_of_ne_zero hd)).le

theorem degree_normalized_row_slice_energy_fraction_le {n d : ℕ} (rows : RowSliceMatrix n d) :
    squareMatrixEnergy (degreeNormalizedMatrix rows) / n ≤ 1 :=
  div_le_one_of_le₀ (degree_normalized_row_slice_energy_le rows) (Nat.cast_nonneg n)

theorem degree_normalized_row_slice_energy_bounded_in_probability (d : ℕ → ℕ) :
    VaryingBoundedInProbability (fun n => rowSliceMatrixLaw n (d n))
      (fun n rows => squareMatrixEnergy (degreeNormalizedMatrix rows) / n) := by
  intro δ hδ
  refine ⟨2, by norm_num, Eventually.of_forall ?_⟩
  intro n
  have hEmpty : {rows : RowSliceMatrix n (d n) |
      (2 : ℝ) < |squareMatrixEnergy (degreeNormalizedMatrix rows) / n|} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro rows hRows
    have hNonneg := div_nonneg (squareMatrixEnergy_nonneg (degreeNormalizedMatrix rows))
      (Nat.cast_nonneg n)
    simp only [Set.mem_setOf_eq, abs_of_nonneg hNonneg] at hRows
    have hBound := degree_normalized_row_slice_energy_fraction_le rows
    linarith
  rw [hEmpty, measureReal_empty]
  exact hδ

theorem row_slice_degree_circular_convergence_of_log_limit (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability
      (fun n => rowSliceMatrixLaw n (d n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z)) :
    DegreeCircularConvergence d := by
  let d' := fun n => min (d n) n
  haveI : ∀ n, IsProbabilityMeasure (rowSliceMatrixLaw n (d' n)) := fun n =>
    rowSliceMatrixLaw_probability (Nat.min_le_right (d n) n)
  have hLog' : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability
      (fun n => rowSliceMatrixLaw n (d' n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z) := by
    filter_upwards [hLog] with z hz
    intro ε hε
    apply (hz ε hε).congr'
    filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
    dsimp only [d']
    rw [Nat.min_eq_left hd.2]
  have hCircular := matrix_circular_hermitization
    (fun n => rowSliceMatrixLaw n (d' n)) (fun _ rows => degreeNormalizedMatrix rows)
    (fun _ => measurable_of_countable _)
    (degree_normalized_row_slice_energy_bounded_in_probability d') hLog'
  intro ε hε
  apply (hCircular ε hε).congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  dsimp only [d']
  rw [Nat.min_eq_left hd.2]
  exact finiteUniformMeasure_real (fun rows : RowSliceMatrix n (d n) => ENNReal.ofReal ε <
    boundedLipschitzDistance (empiricalSpectralMeasure (degreeNormalizedMatrix rows)) circularMeasure)

theorem row_slice_variance_circular_convergence_of_log_limit (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability
      (fun n => rowSliceMatrixLaw n (d n))
      (fun _ rows => normalizedLogDeterminant (degreeNormalizedMatrix rows) z) (circularLogPotential z)) :
    CircularConvergence d := by
  have hValid : ∀ᶠ n in atTop, 0 < d n ∧ d n < n := by
    have hHalf := hSparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse, hHalf,
      eventually_gt_atTop 0] with n hd hRatio hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdnR : (d n : ℝ) < n := by
      have h := (div_lt_iff₀ hnR).mp hRatio
      linarith
    exact ⟨hd.1, by exact_mod_cast hdnR⟩
  exact variance_normalized_circular_convergence_of_degree d hValid hSparse
    (row_slice_degree_circular_convergence_of_log_limit d hDegree hSparse hLog)

end CircularLaw
