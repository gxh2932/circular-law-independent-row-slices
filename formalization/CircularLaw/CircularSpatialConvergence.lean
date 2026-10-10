import CircularLaw.CircularLogReconstruction

/-!
# Spatial convergence to the actual circular logarithmic potential

Energy bounded in probability supplies uniform spatial square control.
The checked spatial probability passage then tests the actual shifted
log determinants against compact functions, and reconstruction yields
convergence of every compact C2 eigenvalue test to the circular measure.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology Laplacian

namespace CircularLaw

theorem varying_bounded_probability_constant {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (c : ℝ) :
    VaryingBoundedInProbability μ (fun _ _ => c) := by
  intro δ hδ
  refine ⟨|c| + 1, by positivity, Eventually.of_forall (fun n => ?_)⟩
  have hEmpty : {ω : Ω n | |c| + 1 < |c|} = ∅ := by ext ω; simp
  simpa only [hEmpty, measureReal_empty] using hδ

theorem log_determinant_circular_difference_square_integrableOn {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => (normalizedLogDeterminant A z - circularLogPotential z) ^ 2)
      (Metric.closedBall 0 R) volume := by
  have hA := (normalized_log_determinant_squared_locallyIntegrable A).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hC := circular_log_potential_squared_locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hMeas := ((normalized_log_determinant_measurable A).sub
    circular_log_potential_continuous.measurable).pow_const 2
  apply ((hA.const_mul 2).add (hC.const_mul 2)).mono' hMeas.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (normalizedLogDeterminant A z - circularLogPotential z) ^ 2 ≤
    2 * (normalizedLogDeterminant A z) ^ 2 + 2 * (circularLogPotential z) ^ 2
  nlinarith [sq_nonneg (normalizedLogDeterminant A z + circularLogPotential z)]

theorem log_determinant_circular_difference_square_integral_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant A z - circularLogPotential z) ^ 2) ≤
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant A z) ^ 2) +
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (circularLogPotential z) ^ 2) := by
  have hA := (normalized_log_determinant_squared_locallyIntegrable A).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hC := circular_log_potential_squared_locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hBound : (∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant A z - circularLogPotential z) ^ 2) ≤
      ∫ z : ℂ in Metric.closedBall 0 R,
        2 * (normalizedLogDeterminant A z) ^ 2 + 2 * (circularLogPotential z) ^ 2 := by
    apply setIntegral_mono_on (log_determinant_circular_difference_square_integrableOn A R)
      ((hA.const_mul 2).add (hC.const_mul 2)) measurableSet_closedBall
    intro z _
    change (normalizedLogDeterminant A z - circularLogPotential z) ^ 2 ≤
      2 * (normalizedLogDeterminant A z) ^ 2 + 2 * (circularLogPotential z) ^ 2
    nlinarith [sq_nonneg (normalizedLogDeterminant A z + circularLogPotential z)]
  rw [integral_add (hA.const_mul 2) (hC.const_mul 2), integral_const_mul,
    integral_const_mul] at hBound
  exact hBound

theorem log_determinant_circular_spatial_square_bounded_in_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n)) :
    VaryingBoundedInProbability μ (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant (A n ω) z - circularLogPotential z) ^ 2) := by
  have hA := normalized_log_determinant_spatial_square_bounded_in_probability_of_energy μ A R hEnergy
  have hC := varying_bounded_probability_constant μ
    (∫ z : ℂ in Metric.closedBall 0 R, (circularLogPotential z) ^ 2)
  have hSum := varying_bounded_probability_add μ
    (varying_bounded_probability_const_mul μ hA 2) (varying_bounded_probability_const_mul μ hC 2)
  apply varying_bounded_probability_of_abs_le μ hSum
  apply Eventually.of_forall
  intro n ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)),
    abs_of_nonneg (by positivity : 0 ≤
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant (A n ω) z) ^ 2) +
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (circularLogPotential z) ^ 2))]
  exact log_determinant_circular_difference_square_integral_bound _ R

theorem log_determinant_circular_spatial_test_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n))
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z) (circularLogPotential z))
    (R : ℝ) (ψ : ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ z, |ψ z| ≤ C)
    (hSupport : ∀ z, z ∉ Metric.closedBall 0 R → ψ z = 0) :
    VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ,
      ψ z * (normalizedLogDeterminant (A n ω) z - circularLogPotential z)) 0 := by
  let ν : Measure ℂ := volume.restrict (Metric.closedBall 0 R)
  letI : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top⟩
  have hDisk : VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      ψ z * (normalizedLogDeterminant (A n ω) z - circularLogPotential z)) 0 := by
    apply spatial_bounded_test_integral_tendsto_zero_in_probability μ ν
      (fun n ω z => normalizedLogDeterminant (A n ω) z - circularLogPotential z)
      _ _ _ _ ψ C hC hψ
    · intro n
      exact (normalized_log_determinant_joint_measurable (A n) (hA n)).sub
        (circular_log_potential_continuous.measurable.comp measurable_snd)
    · intro n ω
      exact log_determinant_circular_difference_square_integrableOn _ R
    · filter_upwards [ae_restrict_of_ae hLog] with z hz
      simpa only [VaryingConvergesInProbability, sub_zero] using hz
    · exact log_determinant_circular_spatial_square_bounded_in_probability μ A R hEnergy
  have hEq : (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      ψ z * (normalizedLogDeterminant (A n ω) z - circularLogPotential z)) =
      (fun n ω => ∫ z : ℂ, ψ z * (normalizedLogDeterminant (A n ω) z - circularLogPotential z)) := by
    funext n ω
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [hSupport z hz, zero_mul]
  rw [hEq] at hDisk
  exact hDisk

theorem circular_compact_C2_test_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n))
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z) (circularLogPotential z))
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    VaryingConvergesInProbability μ (fun n ω =>
      (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
        ∫ z : ℂ, φ z ∂circularMeasure) 0 := by
  have hLapCont := planar_laplacian_continuous φ hφ
  have hLapSupport := planar_laplacian_compact_support φ hSupport hφ
  obtain ⟨C, hBound⟩ := hLapSupport.exists_bound_of_continuous hLapCont
  obtain ⟨R, hR⟩ := hLapSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hZero : ∀ z, z ∉ Metric.closedBall 0 R → (Δ φ) z = 0 := by
    intro z hz
    exact image_eq_zero_of_notMem_tsupport (fun h => hz (hR h))
  have hProb := log_determinant_circular_spatial_test_convergence μ A hA hEnergy hLog
    R (Δ φ) (max C 0) (le_max_right _ _) (fun z => (hBound z).trans (le_max_left _ _)) hZero
  intro ε hε
  apply varying_probability_event_of_subset μ _ (hProb ((2 * Real.pi) * ε) (by positivity))
  intro n ω hω
  change (2 * Real.pi) * ε < |(∫ z : ℂ,
    (Δ φ) z * (normalizedLogDeterminant (A n ω) z - circularLogPotential z)) - 0|
  rw [log_determinant_circular_test_difference _ φ hφ hSupport, sub_zero, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  change ε < |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
    (∫ z : ℂ, φ z ∂circularMeasure) - 0| at hω
  rw [sub_zero] at hω
  exact mul_lt_mul_of_pos_left hω (by positivity)

end CircularLaw
