import CircularLaw.RegularizedReferenceTailProbability
import CircularLaw.RowRestrictionLogVolume
import CircularLaw.IndependentBernoulliLogTails

/-!
# Actual Bernoulli prefix regularization removal from logarithmic tails

The normalized square singular array lies below the corresponding raw
singular array and every retained row singular value. Its proved tail
convergence therefore removes every positive ridge scale tending to zero.
The extended full-log theorem also gives vanishing singular-matrix probability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology NNReal

namespace CircularLaw

def rowRestrictionTailEmbedding {m n : ℕ} (hmn : m ≤ n) : Fin (Fintype.card (Fin m)) ↪ Fin n where
  toFun j := ⟨j.val + (n - m), by
    have hj : j.val < m := by simpa only [Fintype.card_fin] using j.isLt
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val + (n - m) = j.val + (n - m) at hv
    omega

theorem bernoulli_normalized_singular_le_raw {n d : ℕ} (hd : 0 < d) (z : ℂ)
    (x : BernoulliSquareSample n) (j : Fin n) :
    orderedSquareSingularValues (normalizedShiftedBernoulliMatrix d z x) j ≤
      orderedSquareSingularValues (bernoulliSquareMatrix x - (z * (Real.sqrt (d : ℝ) : ℂ)) • 1) j := by
  rw [bernoulli_raw_shift_eq_sqrt_smul hd, ordered_square_singular_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hRoot : (1 : ℝ) ≤ Real.sqrt d := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hRoot
    (orderedSquareSingularValues_nonneg (normalizedShiftedBernoulliMatrix d z x) j)

theorem bernoulli_retained_regularized_log_removal (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    (m : ℕ → ℕ) (f : ∀ n, Fin (m n) ↪ Fin n) (η : ℕ → ℝ)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n) (hηLimit : Tendsto η atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => (regularizedRowPotential (matrixRowRestriction
          (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n)) (η n) -
        matrixRowLogVolume (matrixRowRestriction
          (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n))) / n) 0 := by
  have hmn (n : ℕ) : m n ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (f n) (f n).injective
  apply regularized_row_log_removal_of_reference_tail
    (fun n => sparseBernoulliMatrixLaw n (d n)) m _
    (fun n => rowRestrictionTailEmbedding (hmn n)) (bernoulliSingularArray d z) η hη hηLimit
  · filter_upwards [hDegree.eventually_ge_atTop 1] with n hd
    intro x j
    let i : Fin (m n) := ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
    let l := rowRestrictionTailEmbedding (hmn n) j
    have hRaw := bernoulli_normalized_singular_le_raw (by omega : 0 < d n) z x l
    have hRetained := ambient_singular_value_le_row_restriction
      (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n) i l rfl
    exact hRaw.trans hRetained
  · intro ε hε
    obtain ⟨T0, _, hTail⟩ := empirical_negative_log_UI_threshold
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z)
      (bernoulli_shifted_weak_convergence d hDegree hSparse z)
      (bernoulli_shifted_full_log_convergence d z hDegree hSparse hz)
      (gaussian_shifted_limit_finite_logarithmic_integral z)
      (bernoulliSingularArray_second_moment_bounded d z hDegree hSparse) hε
    exact ⟨max 1 T0, le_max_left _ _, hTail _ (le_max_right _ _)⟩

theorem bernoulli_raw_det_zero_probability_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1).det = 0}) atTop (𝓝 0) := by
  have hZero := empirical_zero_probability_tendsto (fun n => sparseBernoulliMatrixLaw n (d n))
    (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z)
    (bernoulli_shifted_full_log_convergence d z hDegree hSparse hz)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hZero
  filter_upwards [hDegree.eventually_ge_atTop 1] with n hd
  apply measureReal_mono (h₂ := by finiteness)
  intro x hDet
  by_contra hNoZero
  obtain ⟨j, hj⟩ := (square_singular_has_zero_iff_det_zero
    (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)).mpr hDet
  have hValue : orderedSquareSingularValues
      (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) j = 0 :=
    congrArg (fun t : ℝ≥0 => (t : ℝ)) hj
  have hPositive : 0 < bernoulliSingularArray d z n x j :=
    lt_of_le_of_ne (zero_le _) (fun h => hNoZero ⟨j, h.symm⟩)
  have hRaw := bernoulli_normalized_singular_le_raw (by omega : 0 < d n) z x j
  rw [hValue] at hRaw
  have hPositiveR : (0 : ℝ) < bernoulliSingularArray d z n x j := by exact_mod_cast hPositive
  exact (not_le_of_gt hPositiveR) hRaw

theorem independent_bernoulli_retained_regularized_log_removal (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    (m : ℕ → ℕ) (f : ∀ n, Fin (m n) ↪ Fin n) (η : ℕ → ℝ)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n) (hηLimit : Tendsto η atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => (regularizedRowPotential (matrixRowRestriction
          (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n)) (η n) -
        matrixRowLogVolume (matrixRowRestriction
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n))) / n) 0 := by
  intro ε hε
  have hBern := (bernoulli_retained_regularized_log_removal
    d hDegree hSparse z hz m f η hη hηLimit) ε hε
  apply hBern.congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact (independent_square_bernoulli_event_real hd.2 (fun x => ε <
    |(regularizedRowPotential (matrixRowRestriction
        (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n)) (η n) -
      matrixRowLogVolume (matrixRowRestriction
        (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1) (f n))) / n - 0|)).symm

theorem independent_bernoulli_raw_det_zero_probability_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      {samples | (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1).det = 0}) atTop (𝓝 0) := by
  apply (bernoulli_raw_det_zero_probability_tendsto_zero d hDegree hSparse z hz).congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact (independent_square_bernoulli_event_real hd.2 (fun x =>
    (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1).det = 0)).symm

end CircularLaw
