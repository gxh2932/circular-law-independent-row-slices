import CircularLaw.BernoulliRowExposure

/-!
# Bernoulli minimum-value reduction with the scalar estimate discharged

The actual fresh row gives the inverse-square-root degree bound without
conditioning on row cardinalities. Only the square and leave-one-out
almost-constant failure probabilities remain in the minimum reduction.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem shifted_bernoulli_normal_scalar_probability_le {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (ζ : ℂ) (i : Fin n)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(∑ j, weightedBernoulliValue (shiftedBernoulliUnitNormal ζ sample i j)
          (sample (i, j))) - ζ * shiftedBernoulliUnitNormal ζ sample i i‖ ≤
        ρ / Real.sqrt n} ≤
      bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) +
        (sparseBernoulliMatrixLaw n d).real {sample |
          ¬sourceNonAlmostConstant δ ρ (shiftedBernoulliUnitNormal ζ sample i)} := by
  rw [sparseBernoulliMatrixLaw_eq hn (by omega)]
  let B : (BernoulliRowPastIndex i → Bool) → (Fin n → Bool) → Prop := fun past fresh =>
    ‖(∑ j, weightedBernoulliValue (bernoulliExposedUnitNormal ζ i past j) (fresh j)) -
        ζ * bernoulliExposedUnitNormal ζ i past i‖ ≤ ρ / Real.sqrt n
  let G : (BernoulliRowPastIndex i → Bool) → Prop := fun past =>
    sourceNonAlmostConstant δ ρ (bernoulliExposedUnitNormal ζ i past)
  have hBound := bernoulli_disjoint_fresh_probability_le_with_bad_event
    (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn (by omega))
    (bernoulliRowPastEmbedding i) (bernoulliRowFreshEmbedding i)
    (bernoulli_row_exposure_blocks_disjoint i) B G
    (div_nonneg bernoulli_scalar_small_ball_constant_pos.le (Real.sqrt_nonneg _))
    (fun past hPast => row_bernoulli_nonalmost_small_ball_half_degree hn hd hDegree hδ hρ
      (bernoulliExposedUnitNormal ζ i past) hPast (ζ * bernoulliExposedUnitNormal ζ i past i))
  have hEvent (sample : BernoulliSquareSample n) :
      B (fun a => sample (bernoulliRowPastEmbedding i a))
        (fun j => sample (bernoulliRowFreshEmbedding i j)) ↔
      ‖(∑ j, weightedBernoulliValue (shiftedBernoulliUnitNormal ζ sample i j)
          (sample (i, j))) - ζ * shiftedBernoulliUnitNormal ζ sample i i‖ ≤
        ρ / Real.sqrt n := by
    change ‖(∑ j, weightedBernoulliValue
        (bernoulliExposedUnitNormal ζ i (bernoulliRowPast i sample) j) (sample (i, j))) -
      ζ * bernoulliExposedUnitNormal ζ i (bernoulliRowPast i sample) i‖ ≤ _ ↔ _
    rw [← bernoulli_unit_normal_eq_exposed]
  have hBad (sample : BernoulliSquareSample n) :
      ¬G (fun a => sample (bernoulliRowPastEmbedding i a)) ↔
        ¬sourceNonAlmostConstant δ ρ (shiftedBernoulliUnitNormal ζ sample i) := by
    change ¬sourceNonAlmostConstant δ ρ
      (bernoulliExposedUnitNormal ζ i (bernoulliRowPast i sample)) ↔ _
    rw [← bernoulli_unit_normal_eq_exposed]
  simpa only [hEvent, hBad, bernoulliSquareMatrixLaw] using hBound

theorem shifted_bernoulli_row_distance_probability_with_proved_small_ball {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (ζ : ℂ) (i : Fin n)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      finiteRowDistance (complexConjugateRows (fullShiftedBernoulliMatrix ζ sample)) i ≤
        ρ / Real.sqrt n} ≤
      bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) +
        (sparseBernoulliMatrixLaw n d).real {sample |
          bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ} := by
  have hDistance : (sparseBernoulliMatrixLaw n d).real {sample |
      finiteRowDistance (complexConjugateRows (fullShiftedBernoulliMatrix ζ sample)) i ≤
        ρ / Real.sqrt n} ≤
      (sparseBernoulliMatrixLaw n d).real {sample |
        ‖(∑ j, weightedBernoulliValue (shiftedBernoulliUnitNormal ζ sample i j)
            (sample (i, j))) - ζ * shiftedBernoulliUnitNormal ζ sample i i‖ ≤
          ρ / Real.sqrt n} := by
    apply measureReal_mono (h₂ := by finiteness)
    intro sample hSample
    exact (shifted_bernoulli_unit_normal_row_form_le_distance ζ sample i).trans hSample
  apply hDistance.trans
  apply (shifted_bernoulli_normal_scalar_probability_le hn hd hDegree ζ i hδ hρ).trans
  apply add_le_add (le_refl _)
  apply measureReal_mono (h₂ := by finiteness)
  intro sample hSample
  exact shifted_bernoulli_unit_normal_almost_implies_kernel_failure ζ sample i δ ρ hSample

theorem bernoulli_smallest_probability_of_almost_constant_bounds {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (ζ : ℂ) {δ ρ η κ : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ)
    (hKernel : ∀ i : Fin n, (sparseBernoulliMatrixLaw n d).real {sample |
      bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ} ≤ η)
    (hAlmost : (sparseBernoulliMatrixLaw n d).real {sample |
      sourceAlmostConstantAdjointFailure (fullShiftedBernoulliMatrix ζ sample) δ ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤ κ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      squareSmallestSingularFailure (fullShiftedBernoulliMatrix ζ sample)
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)} ≤
      κ + (bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) + η) / δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDistance (i : Fin n) :
      (sparseBernoulliMatrixLaw n d).real {sample |
        finiteRowDistance (complexConjugateRows (fullShiftedBernoulliMatrix ζ sample)) i ≤
          ρ / Real.sqrt n} ≤ bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) + η :=
    (shifted_bernoulli_row_distance_probability_with_proved_small_ball hn hd hDegree ζ i hδ hρ).trans
      (add_le_add (le_refl _) (hKernel i))
  apply (square_smallest_failure_probability_le_source_distances
    (sparseBernoulliMatrixLaw n d) hn (fullShiftedBernoulliMatrix ζ)
    hδ hδOne hρ (div_nonneg hρ.le (Real.sqrt_nonneg n))).trans
  apply (add_le_add hAlmost (div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun i _ => hDistance i)) (mul_pos hδ hnR).le)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  field_simp

end CircularLaw
