import CircularLaw.GaussianNegativeLogClipping
import CircularLaw.GaussianShiftedLimitProperties
import CircularLaw.EmpiricalPositiveLogConvergence
import CircularLaw.GaussianShiftFullRank
import CircularLaw.GaussianZeroLogValue
import CircularLaw.SpectralLogConvergence

/-!
# Actual shifted Gaussian logarithms converge in probability

Uniform negative clipping and bounded continuous weak tests give the
negative-part limit. The checked second-moment bound controls the
positive part. Full rank supplies the zero event, so the actual
extended empirical logarithm and spectral logarithmic potential have
the finite limiting value. Its circular identification is proved at zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_empirical_second_moment_bounded (z : ℂ) :
    VaryingBoundedInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (fun t => (t : ℝ) ^ 2)) := by
  have h := gaussian_second_moment_bounded_in_probability z
  have hEq : (fun n : ℕ => gaussianSingularSecondMoment (n := n) z) =
      (fun n x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (fun t => (t : ℝ) ^ 2)) := by
    funext n x
    rw [gaussianSingularSecondMoment, gaussianSingularMeasure, squareSingularMeasure,
      empiricalNonnegativeMeasure_integral]
  rw [hEq] at h
  exact h

theorem gaussian_negative_log_mean_converges (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog)
      (∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z) := by
  apply varying_probability_of_error_bound gaussianSquareMatrixLaw
  intro epsilon hEpsilon delta hDelta
  obtain ⟨T0, hT0, hError⟩ := gaussian_negative_log_clipping_error_threshold z
    (show 0 < epsilon / 3 by linarith)
  have hClose : ∀ᶠ T : ℕ in atTop,
      |(∫ t, clippedNegativeLog T t ∂gaussianShiftedSingularLimit z) -
        ∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z| < epsilon / 3 := by
    have h := (clippedNegativeLog_integral_tendsto (gaussian_shifted_limit_finite_logarithmic_integral z)).eventually
      (Metric.ball_mem_nhds _ (by linarith : 0 < epsilon / 3))
    simpa only [Metric.mem_ball, Real.dist_eq] using h
  have hBig : ∀ᶠ T : ℕ in atTop, T0 ≤ (T : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop T0)
  obtain ⟨T, hCloseT, hBigT⟩ := (hClose.and hBig).exists
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hGap := (hError T hBigT).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < delta / 2))
  have hClip := ((empirical_weak_clipped_negative (gaussian_shifted_weak_convergence z) hT)
    (epsilon / 3) (by linarith)).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < delta / 2))
  filter_upwards [hGap, hClip] with n hnGap hnClip
  have hSubset : {x : GaussianSquareSample n | epsilon <
      |empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
        hermitizationNegativeLog - ∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z|} ⊆
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ∨
        epsilon / 3 < empiricalNonnegativeMean
          (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog -
          empiricalNonnegativeMean
            (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (clippedNegativeLog T)} ∪
      {x | epsilon / 3 < |empiricalNonnegativeMean
          (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (clippedNegativeLog T) -
          ∫ t, clippedNegativeLog T t ∂gaussianShiftedSingularLimit z|} := by
    intro x hx
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at h
    have hPos (j : Fin n) :
        0 < squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j := by
      apply lt_of_le_of_ne (zero_le _)
      exact fun hj => h.1.1 ⟨j, hj.symm⟩
    have hGap0 := empirical_negative_log_clipping_bounds
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hPos hT
    have hAbs1 := abs_sub_le
      (empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
        hermitizationNegativeLog)
      (empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
        (clippedNegativeLog T))
      (∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z)
    rw [abs_of_nonneg hGap0] at hAbs1
    have hAbs2 := abs_sub_le
      (empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
        (clippedNegativeLog T))
      (∫ t, clippedNegativeLog T t ∂gaussianShiftedSingularLimit z)
      (∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z)
    change epsilon < |empiricalNonnegativeMean
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog -
        ∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z| at hx
    linarith [h.1.2, h.2]
  have hBound := (measureReal_mono (μ := gaussianSquareMatrixLaw n) hSubset).trans
    (measureReal_union_le _ _)
  exact hBound.trans_lt (by linarith)

theorem gaussian_log_mean_converges (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (fun t => Real.log (t : ℝ)))
      (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z) := by
  have hPos := empirical_positive_log_convergence gaussianSquareMatrixLaw
    (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
    (gaussianShiftedSingularLimit z) (gaussian_shifted_weak_convergence z)
    (gaussian_shifted_limit_log_integrable z) (gaussian_empirical_second_moment_bounded z)
  have h := varying_probability_sub gaussianSquareMatrixLaw hPos (gaussian_negative_log_mean_converges z)
  have hFunctions : (fun (n : ℕ) (x : GaussianSquareSample n) => empiricalNonnegativeMean
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationPositiveLog -
      empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) hermitizationNegativeLog) =
      (fun (n : ℕ) (x : GaussianSquareSample n) => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) (fun t => Real.log (t : ℝ))) := by
    funext n x
    exact (empirical_log_decomposition _).symm
  rw [hFunctions, ← hermitization_log_integral_decomposition (gaussian_shifted_limit_log_integrable z)] at h
  exact h

theorem gaussian_empirical_zero_event_null {n : ℕ} (hn : 0 < n) (z : ℂ) :
    gaussianSquareMatrixLaw n
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))} = 0 := by
  have hNoZero : ∀ᵐ x ∂gaussianSquareMatrixLaw n,
      ¬empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) := by
    filter_upwards [gaussian_normalized_shift_singular_values_pos_ae hn z] with x hx
    rintro ⟨j, hj⟩
    have hPos : 0 < squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j := by
      exact_mod_cast hx j
    exact hPos.ne' hj
  simpa only [not_not] using ae_iff.mp hNoZero

theorem gaussian_empirical_zero_probability_tendsto (z : ℂ) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))})
      atTop (𝓝 0) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [measureReal_def, gaussian_empirical_zero_event_null hn z, ENNReal.toReal_zero]

theorem gaussian_empirical_log_convergence (z : ℂ) :
    EmpiricalLogConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
      (gaussianShiftedSingularLimit z) :=
  empirical_log_convergence_of_real_and_zero_probability gaussianSquareMatrixLaw _ _
    (gaussian_log_mean_converges z) (gaussian_empirical_zero_probability_tendsto z)

theorem gaussian_zero_log_mean_converges :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x)) (fun t => Real.log (t : ℝ)))
      (-(1 / 2 : ℝ)) := by
  have h := gaussian_log_mean_converges 0
  rw [gaussian_zero_shift_log_integral_value] at h
  exact h

theorem gaussian_spectral_log_potential_converges (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => spectralLogPotential ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) z)
      (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z) :=
  (spectral_log_potential_convergence_of_singular_log gaussianSquareMatrixLaw
    (fun n x => (Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) z
    (gaussianShiftedSingularLimit z) (gaussian_empirical_log_convergence z)).1

end CircularLaw
