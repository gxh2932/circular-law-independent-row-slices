import CircularLaw.InvertibilityDistanceProbability
import CircularLaw.SmallestSingularFailureTransfer
import CircularLaw.MatrixSingularVolumes

/-!
# Actual smallest-singular-value failure reduced to source distance events

The ordered Gram eigenbasis supplies an actual unit singular witness.
Its adjoint image is the literal combination of conjugated rows. Splitting
this witness into the source almost-constant and non-almost-constant
classes therefore bounds the actual smallest-value failure event.
The almost-constant probability and the row-distance probabilities are
still inputs to this reduction, not proved probabilistic estimates.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

namespace CircularLaw

theorem finite_conjugate_row_combination_eq_adjoint {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    finiteRowCombination (complexConjugateRows A) (fun i => x i) =
      A.conjTranspose.toEuclideanLin x := by
  ext j
  simp only [finiteRowCombination, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    complexConjugateRows, PiLp.toLp_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    smul_eq_mul, mul_comm]

theorem matrix_source_nonalmost_distance_probability {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 0 < n) (A : Ω → Matrix (Fin n) (Fin n) ℂ)
    {δ ρ ε : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    μ.real {ω | (⨅ x : {x : EuclideanSpace ℂ (Fin n) //
        ‖x‖ = 1 ∧ sourceNonAlmostConstant δ ρ x},
        ENNReal.ofReal ‖(A ω).conjTranspose.toEuclideanLin x.val‖) ≤
          ENNReal.ofReal (ε * ρ / Real.sqrt n)} ≤
      (∑ i : Fin n, μ.real {ω |
        finiteRowDistance (complexConjugateRows (A ω)) i ≤ ε}) / (δ * n) := by
  simpa only [sourceNonAlmostRowMinimum, finite_conjugate_row_combination_eq_adjoint] using
    source_nonalmost_row_distance_probability μ hn
      (fun ω => complexConjugateRows (A ω)) hδ hδOne hρ hε

theorem square_singular_value_has_unit_adjoint_witness {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
      ‖A.conjTranspose.toEuclideanLin x‖ = orderedSquareSingularValues A j := by
  let H := Matrix.isHermitian_mul_conjTranspose_self A
  let hT := Matrix.isHermitian_iff_isSymmetric.mp H
  let k : Fin (Fintype.card (Fin n)) :=
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
  let x := hT.eigenvectorBasis finrank_euclideanSpace k
  have hNorm : ‖x‖ = 1 := (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 k
  have hEigen : (A * A.conjTranspose).toEuclideanLin x = (H.eigenvalues₀ k : ℂ) • x :=
    hT.apply_eigenvectorBasis finrank_euclideanSpace k
  have hSq : orderedSquareSingularValues A j ^ 2 =
      ‖A.conjTranspose.toEuclideanLin x‖ ^ 2 := by
    rw [orderedSquareSingularValues_sq]
    have hQuad := matrix_row_gram_quadratic_eq_adjoint_norm A x
    rw [hEigen, inner_smul_left, inner_self_eq_norm_sq_to_K, hNorm] at hQuad
    simpa only [k, map_one, one_pow, mul_one, Complex.conj_ofReal, Complex.ofReal_re] using hQuad
  refine ⟨x, hNorm, ?_⟩
  nlinarith [norm_nonneg (A.conjTranspose.toEuclideanLin x),
    orderedSquareSingularValues_nonneg A j]

def sourceAlmostConstantAdjointFailure {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    ¬sourceNonAlmostConstant δ ρ x ∧ ‖A.conjTranspose.toEuclideanLin x‖ ≤ τ

theorem source_almost_constant_adjoint_failure_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (δ ρ τ : ℝ) :
    sourceAlmostConstantAdjointFailure A δ ρ τ ↔
      ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
        (∃ center : ℂ, (1 - δ) * n <
          ((Finset.univ.filter (fun i => ‖x i - center‖ ≤ ρ / Real.sqrt n)).card : ℝ)) ∧
        ‖A.conjTranspose.toEuclideanLin x‖ ≤ τ := by
  simp only [sourceAlmostConstantAdjointFailure, sourceNonAlmostConstant,
    not_forall, not_le]

theorem square_smallest_failure_subset_source_split {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (δ ρ τ : ℝ)
    (hSmall : squareSmallestSingularFailure A τ) :
    sourceAlmostConstantAdjointFailure A δ ρ τ ∨
      sourceNonAlmostRowMinimum (complexConjugateRows A) δ ρ ≤ ENNReal.ofReal τ := by
  obtain ⟨j, hj⟩ := hSmall
  obtain ⟨x, hx, hImage⟩ := square_singular_value_has_unit_adjoint_witness A j
  by_cases hNon : sourceNonAlmostConstant δ ρ x
  · right
    exact (iInf_le_of_le ⟨x, hx, hNon⟩ (le_refl _)).trans
      (ENNReal.ofReal_le_ofReal (by
        rw [finite_conjugate_row_combination_eq_adjoint, hImage]
        exact hj))
  · exact Or.inl ⟨x, hx, hNon, hImage.le.trans hj⟩

theorem square_smallest_failure_probability_le_source_distances {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (hn : 0 < n)
    (A : Ω → Matrix (Fin n) (Fin n) ℂ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    μ.real {ω | squareSmallestSingularFailure (A ω) (ε * ρ / Real.sqrt n)} ≤
      μ.real {ω | sourceAlmostConstantAdjointFailure (A ω) δ ρ (ε * ρ / Real.sqrt n)} +
        (∑ i : Fin n, μ.real {ω |
          finiteRowDistance (complexConjugateRows (A ω)) i ≤ ε}) / (δ * n) := by
  have hSubset : {ω | squareSmallestSingularFailure (A ω) (ε * ρ / Real.sqrt n)} ⊆
      {ω | sourceAlmostConstantAdjointFailure (A ω) δ ρ (ε * ρ / Real.sqrt n)} ∪
        {ω | sourceNonAlmostRowMinimum (complexConjugateRows (A ω)) δ ρ ≤
          ENNReal.ofReal (ε * ρ / Real.sqrt n)} := by
    intro ω hω
    exact square_smallest_failure_subset_source_split (A ω) δ ρ _ hω
  exact (measureReal_mono hSubset (h₂ := by finiteness)).trans
    (measureReal_union_le _ _ |>.trans (add_le_add_right
      (source_nonalmost_row_distance_probability μ hn
        (fun ω => complexConjugateRows (A ω)) hδ hδOne hρ hε) _))

theorem row_slice_smallest_failure_probability_le_source_distances {n d : ℕ}
    (hn : 0 < n) (ζ : ℂ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) (ε * ρ / Real.sqrt n)) ≤
      uniformProbability (fun rows : RowSliceMatrix n d =>
        sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ
          (ε * ρ / Real.sqrt n)) +
        (∑ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
          finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ ε)) / (δ * n) := by
  haveI : IsFiniteMeasure (rowSliceMatrixLaw n d) := by
    unfold rowSliceMatrixLaw
    infer_instance
  simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real] using
    square_smallest_failure_probability_le_source_distances (rowSliceMatrixLaw n d) hn
      (fun rows => fullShiftedSliceMatrix ζ rows) hδ hδOne hρ hε

end CircularLaw
