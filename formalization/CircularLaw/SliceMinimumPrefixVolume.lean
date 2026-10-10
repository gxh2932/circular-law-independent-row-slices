import CircularLaw.BernoulliPrefixRegularizationRemoval
import CircularLaw.SmallestSingularFailureTransfer

/-!
# Prefix volume comparison using only the row-slice minimum estimate

The actual Bernoulli logarithmic tails remove its ridge. A row-slice
minimum failure bound removes the other ridge, so the checked regularized
comparison supplies the unregularized comparison without a common minimum.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem square_singular_lower_bound_outside_failure {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ)
    (hGood : ¬squareSmallestSingularFailure A τ) :
    ∀ j, τ ≤ orderedSquareSingularValues A j := by
  intro j
  exact (lt_of_not_ge (fun h => hGood ⟨j, h⟩)).le

theorem ridge_scale_tendsto_zero_of_bounded_cutoff (τ : ℕ → ℝ)
    (hτ : ∀ᶠ n : ℕ in atTop, 0 ≤ τ n ∧ τ n ≤ 1) :
    Tendsto (fun n : ℕ => τ n / n) atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).inv_tendsto_atTop
  apply squeeze_zero' _ _ hInv
  · filter_upwards [hτ] with n hτn
    exact div_nonneg hτn.1 (Nat.cast_nonneg n)
  · filter_upwards [hτ] with n hτn
    simpa only [one_div] using div_le_div_of_nonneg_right hτn.2 (Nat.cast_nonneg n)

theorem independent_slice_retained_regularized_log_removal (d m : ℕ → ℕ)
    (f : ∀ n, Fin (m n) ↪ Fin n) (ζ : ℕ → ℂ) (τ : ℕ → ℝ)
    (hτ : ∀ᶠ n : ℕ in atTop, 0 < τ n)
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) rows) (τ n)})
      atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => (regularizedRowPotential (matrixRowRestriction
          (fullShiftedSliceMatrix (ζ n) samples.1) (f n)) (τ n / n) -
        matrixRowLogVolume (matrixRowRestriction
          (fullShiftedSliceMatrix (ζ n) samples.1) (f n))) / n) 0 := by
  have hBad : Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      {samples | squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) samples.1) (τ n)})
      atTop (𝓝 0) := by
    apply hMin.congr'
    exact Eventually.of_forall (fun n => (independent_square_slice_event_real n (d n)
      (fun rows => squareSmallestSingularFailure (fullShiftedSliceMatrix (ζ n) rows) (τ n))).symm)
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).inv_tendsto_atTop
  have hError : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      mul_inv_rev, inv_pow, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      (hInv.pow 2).mul_const (2 : ℝ)⁻¹
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hBad
  filter_upwards [hτ, eventually_gt_atTop 0, hError.eventually (gt_mem_nhds hε)]
    with n hτn hn hSmall
  apply measureReal_mono (h₂ := by finiteness)
  intro samples hLarge
  by_contra hGood
  have hLower := square_singular_lower_bound_outside_failure
    (fullShiftedSliceMatrix (ζ n) samples.1) (τ n) hGood
  have hRemoval := row_restriction_regularized_log_removal
    (fullShiftedSliceMatrix (ζ n) samples.1) (f n) hn hτn (hLower _)
  simp only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg hRemoval.1] at hLarge
  exact (not_lt_of_ge hRemoval.2) (hSmall.trans hLarge)

theorem independent_prefix_volume_comparison_of_slice_minimum (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (a : ℝ) (z : ℂ) (hz : z ≠ 0) (τ : ℕ → ℝ)
    (hτ : ∀ᶠ n : ℕ in atTop, 0 < τ n)
    (hRidge : Tendsto (fun n : ℕ => τ n / n) atTop (𝓝 0))
    (hRegularized : VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixPotentialDifference n (d n) a
        (z * (Real.sqrt (d n : ℝ) : ℂ)) (τ n / n)) 0)
    (hMin : Tendsto (fun n => (rowSliceMatrixLaw n (d n)).real
      {rows | squareSmallestSingularFailure
        (fullShiftedSliceMatrix (z * (Real.sqrt (d n : ℝ) : ℂ)) rows) (τ n)}) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n => independentPrefixVolumeDifference n (d n) a
        (z * (Real.sqrt (d n : ℝ) : ℂ))) 0 := by
  let m := fun n => n - hermitizationDeletionCount n (d n) a
  let f := fun n => hermitizationPrefixEmbedding n (d n) a
  have hPositive : ∀ᶠ n : ℕ in atTop, 0 < τ n / n := by
    filter_upwards [hτ, eventually_gt_atTop 0] with n hτn hn
    exact div_pos hτn (by exact_mod_cast hn)
  have hA := independent_slice_retained_regularized_log_removal d m f
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) τ hτ hMin
  have hB := independent_bernoulli_retained_regularized_log_removal
    d hDegree hSparse z hz m f (fun n => τ n / n) hPositive hRidge
  have hSub := varying_probability_sub (fun n => independentSquareComparisonLaw n (d n)) hRegularized hA
  simp only [sub_self] at hSub
  have hAdd := varying_probability_add (fun n => independentSquareComparisonLaw n (d n)) hSub hB
  simp only [add_zero] at hAdd
  convert hAdd using 1
  funext n samples
  dsimp [independentPrefixVolumeDifference, independentPrefixPotentialDifference, f]
  ring

end CircularLaw
