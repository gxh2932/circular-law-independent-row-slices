import CircularLaw.ShiftedSliceUnitNormal
import CircularLaw.FreshRowGaussianProbability

/-!
# Conditioning the literal leave-one-out distance on the other rows

Exact finite resampling replaces the omitted row by an independent fresh
uniform slice. On the good normal event only the scalar concentration
bound is needed. The bad normal event is contained in an actual
almost-constant kernel failure for the n-1 other shifted rows.

The source small-ball and almost-constant kernel estimates remain
explicit hypotheses; no estimate is introduced as an axiom.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem uniform_probability_resample_bound_with_bad_event {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (E G : (ι → α) → Prop) {q : ℝ} (hq : 0 ≤ q)
    (hBound : ∀ rows, G rows →
      uniformProbability (fun s : α => E (Function.update rows i s)) ≤ q) :
    uniformProbability E ≤ q + uniformProbability (fun rows => ¬G rows) := by
  rw [← finiteMean_indicator E, finiteMean_resample_coordinate i]
  calc
    _ ≤ finiteMean (fun rows : ι → α => q + if ¬G rows then (1 : ℝ) else 0) := by
      apply finiteMean_mono
      intro rows
      rw [finiteMean_indicator]
      by_cases hG : G rows
      · simpa only [hG, not_true_eq_false, if_false, add_zero] using hBound rows hG
      · simp only [hG, not_false_eq_true, if_true]
        exact (uniformProbability_le_one _).trans (by linarith)
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_indicator]

theorem shifted_slice_normal_scalar_probability_le_concentration {n d : ℕ}
    (hdn : d ≤ n) (ζ : ℂ) (i : Fin n) (δ ρ r : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hSmallBall : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      sourceNonAlmostConstant δ ρ x →
        rowSliceDiskConcentration (d := d) (fun j => x j) r ≤ q) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖rowLinearForm (rows i) (fun j => shiftedSliceUnitNormal ζ rows i j) -
        ζ * shiftedSliceUnitNormal ζ rows i i‖ ≤ r) ≤
      q + uniformProbability (fun rows : RowSliceMatrix n d =>
        ¬sourceNonAlmostConstant δ ρ (shiftedSliceUnitNormal ζ rows i)) := by
  haveI := rowSlice_nonempty hdn
  apply uniform_probability_resample_bound_with_bad_event i _ _ hq
  intro rows hGood
  simp only [shifted_slice_unit_normal_update, Function.update_self]
  simp_rw [rowLinearForm_eq_support_sum]
  exact (uniformProbability_le_finiteDiskConcentration _ r
      (ζ * shiftedSliceUnitNormal ζ rows i i)).trans
    (hSmallBall _ (shifted_slice_unit_normal_norm ζ rows i) hGood)

theorem shifted_slice_row_distance_probability_le_normal_scalar {n d : ℕ}
    (ζ : ℂ) (i : Fin n) (r : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ r) ≤
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ‖rowLinearForm (rows i) (fun j => shiftedSliceUnitNormal ζ rows i j) -
          ζ * shiftedSliceUnitNormal ζ rows i i‖ ≤ r) := by
  apply uniformProbability_mono
  intro rows hRows
  exact (shifted_slice_unit_normal_row_form_le_distance ζ rows i).trans hRows

theorem shifted_slice_row_distance_probability_le_source_components {n d : ℕ}
    (hdn : d ≤ n) (ζ : ℂ) (i : Fin n) (δ ρ r : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hSmallBall : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      sourceNonAlmostConstant δ ρ x →
        rowSliceDiskConcentration (d := d) (fun j => x j) r ≤ q) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ r) ≤
      q + uniformProbability (fun rows : RowSliceMatrix n d =>
        sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) := by
  exact (shifted_slice_row_distance_probability_le_normal_scalar ζ i r).trans
    ((shifted_slice_normal_scalar_probability_le_concentration hdn ζ i δ ρ r hq hSmallBall).trans
      (add_le_add (le_refl q)
        (shifted_slice_unit_normal_almost_probability_le_kernel_failure ζ i δ ρ)))

theorem shifted_slice_row_distance_probability_of_source_kernel_bound {n d : ℕ}
    (hdn : d ≤ n) (ζ : ℂ) (i : Fin n) (δ ρ r : ℝ) {q η : ℝ} (hq : 0 ≤ q)
    (hSmallBall : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      sourceNonAlmostConstant δ ρ x →
        rowSliceDiskConcentration (d := d) (fun j => x j) r ≤ q)
    (hKernel : uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) ≤ η) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ r) ≤ q + η :=
  (shifted_slice_row_distance_probability_le_source_components hdn ζ i δ ρ r hq hSmallBall).trans
    (add_le_add (le_refl q) hKernel)

theorem row_slice_smallest_probability_of_source_components {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (ζ : ℂ) {δ ρ r q η κ : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hSmallBall : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      sourceNonAlmostConstant δ ρ x →
        rowSliceDiskConcentration (d := d) (fun j => x j) r ≤ q)
    (hKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) ≤ η)
    (hAlmost : uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ
        (r * ρ / Real.sqrt n)) ≤ κ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) (r * ρ / Real.sqrt n)) ≤
        κ + (q + η) / δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCount : (∑ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤ r)) ≤
        (n : ℝ) * (q + η) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        shifted_slice_row_distance_probability_of_source_kernel_bound hdn ζ i δ ρ r hq
          hSmallBall (hKernel i))
  apply (row_slice_smallest_failure_probability_le_source_distances hn ζ hδ hδOne hρ hr).trans
  apply (add_le_add hAlmost (div_le_div_of_nonneg_right hCount (mul_pos hδ hnR).le)).trans_eq
  congr 1
  field_simp [hδ.ne', hnR.ne']

end CircularLaw
