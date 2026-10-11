import CircularLaw.InvertibilityDistanceGeometry
import CircularLaw.MeasureModel
import CircularLaw.FiniteRowNegativeSecondMoment
import CircularLaw.SquareSliceSingularValues

/-!
# The source invertibility-via-distance probability bound

The expected number of close rows is the sum of its actual marginal
probabilities; no independence of those distance events is needed.
Markov and the checked uniform geometric lower bound prove LLY26a
Lemma 7.1 for arbitrary finite laws, including both manuscript models.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal

namespace CircularLaw

theorem source_close_row_distances_cast_sum {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (ε : ℝ) :
    ((sourceCloseRowDistances rows ε).card : ℝ) =
      ∑ i : Fin n, if finiteRowDistance rows i ≤ ε then (1 : ℝ) else 0 := by
  simp only [sourceCloseRowDistances, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem source_close_row_distances_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} (rows : Ω → Fin n → EuclideanSpace ℂ (Fin n)) (ε : ℝ) :
    (∫ ω, ((sourceCloseRowDistances (rows ω) ε).card : ℝ) ∂μ) =
      ∑ i : Fin n, μ.real {ω | finiteRowDistance (rows ω) i ≤ ε} := by
  simp_rw [source_close_row_distances_cast_sum]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ ω, ({ω | finiteRowDistance (rows ω) i ≤ ε}.indicator (fun _ => (1 : ℝ))) ω ∂μ) = _
  exact integral_indicator_one (Set.toFinite _).measurableSet

theorem source_nonalmost_row_distance_probability {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 0 < n) (rows : Ω → Fin n → EuclideanSpace ℂ (Fin n))
    {δ ρ ε : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    μ.real {ω | sourceNonAlmostRowMinimum (rows ω) δ ρ ≤
        ENNReal.ofReal (ε * ρ / Real.sqrt n)} ≤
      (∑ i : Fin n, μ.real {ω | finiteRowDistance (rows ω) i ≤ ε}) / (δ * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hScale : 0 < δ * n := mul_pos hδ hnR
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => Nat.cast_nonneg (sourceCloseRowDistances (rows ω) ε).card))
    (Integrable.of_finite (μ := μ)) (δ * n)
  rw [source_close_row_distances_integral] at hMark
  have hSubset : {ω | sourceNonAlmostRowMinimum (rows ω) δ ρ ≤ ENNReal.ofReal (ε * ρ / Real.sqrt n)} ⊆
      {ω | δ * n ≤ ((sourceCloseRowDistances (rows ω) ε).card : ℝ)} := by
    intro ω hω
    exact source_nonalmost_small_image_forces_close_rows hn (rows ω) hδOne hρ hε hω
  apply (le_div_iff₀ hScale).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset (h₂ := by finiteness))
    hScale.le).trans hMark

theorem row_slice_nonalmost_distance_probability {n d : ℕ} (hn : 0 < n) (ζ : ℂ)
    {δ ρ ε : ℝ} (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceNonAlmostRowMinimum (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) δ ρ ≤
        ENNReal.ofReal (ε * ρ / Real.sqrt n)) ≤
      (∑ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
        finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ ε)) / (δ * n) := by
  haveI : IsFiniteMeasure (rowSliceMatrixLaw n d) := by
    unfold rowSliceMatrixLaw
    infer_instance
  have h := source_nonalmost_row_distance_probability (rowSliceMatrixLaw n d) hn
    (fun rows => complexConjugateRows (fullShiftedSliceMatrix ζ rows)) hδ hδOne hρ hε
  simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real] using h

end CircularLaw
