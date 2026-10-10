import CircularLaw.SpectralLogSquareBound
import CircularLaw.SpatialProbabilityConvergence
import CircularLaw.VaryingProbabilityBounded
import Mathlib.Topology.Instances.Matrix

/-!
# The spatial probability passage in the replacement principle

The functions are the actual normalized shifted log determinants.
Their spatial square-integral control is derived from normalized matrix
energy. The hypotheses are precisely measurable matrix families, energy
bounded in probability and almost-everywhere pointwise log-difference
convergence; no spatial convergence is supplied as an assumption.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology

namespace CircularLaw

/-- The actual finite-dimensional matrix topology supplies its Borel law. -/
instance squareMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

instance squareMatrixBorelSpace (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

instance squareMatrixSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := by
  change SecondCountableTopology (Fin n → Fin n → ℂ)
  infer_instance

theorem normalized_log_determinant_measurable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Measurable (normalizedLogDeterminant A) := by
  have hShift : Continuous (fun z : ℂ => A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    fun_prop
  exact (Real.measurable_log.comp hShift.matrix_det.measurable.norm).div_const _

theorem normalized_log_determinant_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (A : Ω → Matrix (Fin n) (Fin n) ℂ) (hA : Measurable A) :
    Measurable (fun p : Ω × ℂ => normalizedLogDeterminant (A p.1) p.2) := by
  have hShift : Measurable (fun p : Ω × ℂ => A p.1 - p.2 •
      (1 : Matrix (Fin n) (Fin n) ℂ)) :=
    (hA.comp measurable_fst).sub (measurable_snd.smul_const _)
  have hDetFun : Measurable (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) :=
    (continuous_id.matrix_det : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.det)).measurable
  have hDet : Measurable (fun p : Ω × ℂ => (A p.1 - p.2 •
      (1 : Matrix (Fin n) (Fin n) ℂ)).det) :=
    hDetFun.comp hShift
  exact (Real.measurable_log.comp hDet.norm).div_const _

theorem log_determinant_difference_square_integrableOn {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => (normalizedLogDeterminant A z - normalizedLogDeterminant B z) ^ 2)
      (Metric.closedBall 0 R) volume := by
  have hA := (normalized_log_determinant_squared_locallyIntegrable A).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hB := (normalized_log_determinant_squared_locallyIntegrable B).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hMeas := ((normalized_log_determinant_measurable A).sub
    (normalized_log_determinant_measurable B)).pow_const 2
  apply ((hA.const_mul 2).add (hB.const_mul 2)).mono' hMeas.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp
  nlinarith [sq_nonneg (normalizedLogDeterminant A z + normalizedLogDeterminant B z)]

theorem log_determinant_difference_square_integral_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant A z - normalizedLogDeterminant B z) ^ 2) ≤
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant A z) ^ 2) +
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant B z) ^ 2) := by
  have hA := (normalized_log_determinant_squared_locallyIntegrable A).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hB := (normalized_log_determinant_squared_locallyIntegrable B).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hInt := (hA.const_mul 2).add (hB.const_mul 2)
  have hBound : (∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant A z - normalizedLogDeterminant B z) ^ 2) ≤
      ∫ z : ℂ in Metric.closedBall 0 R,
        2 * (normalizedLogDeterminant A z) ^ 2 + 2 * (normalizedLogDeterminant B z) ^ 2 := by
    apply setIntegral_mono_on (log_determinant_difference_square_integrableOn A B R)
      hInt measurableSet_closedBall
    intro z _
    change (normalizedLogDeterminant A z - normalizedLogDeterminant B z) ^ 2 ≤
      2 * (normalizedLogDeterminant A z) ^ 2 + 2 * (normalizedLogDeterminant B z) ^ 2
    nlinarith [sq_nonneg (normalizedLogDeterminant A z + normalizedLogDeterminant B z)]
  rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul,
    integral_const_mul] at hBound
  exact hBound

theorem log_determinant_difference_spatial_square_bounded_in_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n)) :
    VaryingBoundedInProbability μ (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) ^ 2) := by
  have hA := normalized_log_determinant_spatial_square_bounded_in_probability_of_energy μ A R hEnergyA
  have hB := normalized_log_determinant_spatial_square_bounded_in_probability_of_energy μ B R hEnergyB
  have hSum := varying_bounded_probability_add μ
    (varying_bounded_probability_const_mul μ hA 2) (varying_bounded_probability_const_mul μ hB 2)
  apply varying_bounded_probability_of_abs_le μ hSum
  apply Eventually.of_forall
  intro n ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)),
    abs_of_nonneg (by positivity : 0 ≤
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant (A n ω) z) ^ 2) +
      2 * (∫ z : ℂ in Metric.closedBall 0 R, (normalizedLogDeterminant (B n ω) z) ^ 2))]
  exact log_determinant_difference_square_integral_bound _ _ R

theorem log_determinant_spatial_absolute_difference_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (R : ℝ) :
    VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      |normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z|) 0 := by
  let ν : Measure ℂ := volume.restrict (Metric.closedBall 0 R)
  letI : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top⟩
  apply spatial_absolute_integral_tendsto_zero_in_probability μ ν
    (fun n ω z => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)
  · intro n
    exact (normalized_log_determinant_joint_measurable (A n) (hA n)).sub
      (normalized_log_determinant_joint_measurable (B n) (hB n))
  · intro n ω
    exact log_determinant_difference_square_integrableOn _ _ R
  · exact ae_restrict_of_ae hLog
  · exact log_determinant_difference_spatial_square_bounded_in_probability μ A B R hEnergyA hEnergyB

theorem log_determinant_spatial_test_difference_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (R : ℝ) (φ : ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ z, |φ z| ≤ C) :
    VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      φ z * (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)) 0 := by
  let ν : Measure ℂ := volume.restrict (Metric.closedBall 0 R)
  letI : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top⟩
  apply spatial_bounded_test_integral_tendsto_zero_in_probability μ ν
    (fun n ω z => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)
    _ _ _ _ φ C hC hφ
  · intro n
    exact (normalized_log_determinant_joint_measurable (A n) (hA n)).sub
      (normalized_log_determinant_joint_measurable (B n) (hB n))
  · intro n ω
    exact log_determinant_difference_square_integrableOn _ _ R
  · exact ae_restrict_of_ae hLog
  · exact log_determinant_difference_spatial_square_bounded_in_probability μ A B R hEnergyA hEnergyB

theorem log_determinant_compact_test_difference_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (R : ℝ) (φ : ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ z, |φ z| ≤ C)
    (hSupport : ∀ z, z ∉ Metric.closedBall 0 R → φ z = 0) :
    VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ,
      φ z * (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)) 0 := by
  have hIntegral : (fun n ω => ∫ z : ℂ in Metric.closedBall 0 R,
      φ z * (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)) =
      (fun n ω => ∫ z : ℂ,
        φ z * (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)) := by
    funext n ω
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [hSupport z hz, zero_mul]
  rw [← hIntegral]
  exact log_determinant_spatial_test_difference_convergence μ A B hA hB
    hEnergyA hEnergyB hLog R φ C hC hφ

theorem spectral_log_potential_compact_test_difference_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (R : ℝ) (φ : ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ z, |φ z| ≤ C)
    (hSupport : ∀ z, z ∉ Metric.closedBall 0 R → φ z = 0) :
    VaryingConvergesInProbability μ (fun n ω => ∫ z : ℂ,
      φ z * (spectralLogPotential (A n ω) z - spectralLogPotential (B n ω) z)) 0 := by
  have hIntegral : (fun n ω => ∫ z : ℂ,
      φ z * (spectralLogPotential (A n ω) z - spectralLogPotential (B n ω) z)) =
      (fun n ω => ∫ z : ℂ,
        φ z * (normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z)) := by
    funext n ω
    apply integral_congr_ae
    filter_upwards [spectral_log_potential_eq_log_determinant_ae (A n ω),
      spectral_log_potential_eq_log_determinant_ae (B n ω)] with z hzA hzB
    rw [hzA, hzB]
  rw [hIntegral]
  exact log_determinant_compact_test_difference_convergence μ A B hA hB
    hEnergyA hEnergyB hLog R φ C hC hφ hSupport

end CircularLaw
