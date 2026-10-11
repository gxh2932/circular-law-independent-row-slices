import CircularLaw.PlanarLogFundamentalSolution
import CircularLaw.LogDeterminantSpatialConvergence

/-!
# Reconstruction of actual eigenvalue test integrals

Finite sums retain every algebraic root multiplicity. The logarithmic
fundamental solution therefore reconstructs the actual empirical spectral
measure, and the spatial probability passage gives C2 compact-test
convergence from the replacement principle's energy and log hypotheses.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology Laplacian

namespace CircularLaw

theorem multiset_log_laplacian_test_integrable (s : Multiset ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    Integrable (fun z : ℂ => (s.map (fun w => Real.log ‖z - w‖)).sum * (Δ φ) z) volume := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_mul]
    exact (planar_log_laplacian_test_integrable φ hφ hSupport w).add ih

theorem multiset_log_laplacian_test_integral (s : Multiset ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, (s.map (fun w => Real.log ‖z - w‖)).sum * (Δ φ) z) =
      (2 * Real.pi) * (s.map φ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_mul]
    rw [integral_add (planar_log_laplacian_test_integrable φ hφ hSupport w)
      (multiset_log_laplacian_test_integrable s φ hφ hSupport),
      planar_log_fundamental_solution φ hφ hSupport w, ih]
    ring

theorem spectral_log_laplacian_test_integrable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    Integrable (fun z : ℂ => spectralLogPotential A z * (Δ φ) z) volume := by
  simpa only [smul_eq_mul] using
    (spectral_log_potential_locallyIntegrable A).integrable_smul_right_of_hasCompactSupport
      (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)

theorem spectral_log_reconstructs_test_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, spectralLogPotential A z * (Δ φ) z) =
      (2 * Real.pi) * (∫ w : ℂ, φ w ∂empiricalSpectralMeasure A) := by
  have hPotential : spectralLogPotential A = fun z =>
      (A.charpoly.roots.map (fun w => Real.log ‖z - w‖)).sum / n := by
    funext z
    exact empiricalSpectralMeasure_integral A (fun w => Real.log ‖z - w‖)
  rw [hPotential, empiricalSpectralMeasure_integral]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, multiset_log_laplacian_test_integral A.charpoly.roots φ hφ hSupport]
  ring

theorem log_determinant_reconstructs_test_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, normalizedLogDeterminant A z * (Δ φ) z) =
      (2 * Real.pi) * (∫ w : ℂ, φ w ∂empiricalSpectralMeasure A) := by
  rw [← spectral_log_reconstructs_test_integral A φ hφ hSupport]
  apply integral_congr_ae
  filter_upwards [spectral_log_potential_eq_log_determinant_ae A] with z hz
  rw [hz]

theorem spectral_log_reconstructs_test_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, (Δ φ) z * (spectralLogPotential A z - spectralLogPotential B z)) =
      (2 * Real.pi) * ((∫ w : ℂ, φ w ∂empiricalSpectralMeasure A) -
        ∫ w : ℂ, φ w ∂empiricalSpectralMeasure B) := by
  simp_rw [mul_sub, mul_comm ((Δ φ) _)]
  rw [integral_sub (spectral_log_laplacian_test_integrable A φ hφ hSupport)
    (spectral_log_laplacian_test_integrable B φ hφ hSupport),
    spectral_log_reconstructs_test_integral A φ hφ hSupport,
    spectral_log_reconstructs_test_integral B φ hφ hSupport]

theorem replacement_compact_C2_test_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    VaryingConvergesInProbability μ (fun n ω =>
      (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
        ∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)) 0 := by
  have hLapCont := planar_laplacian_continuous φ hφ
  have hLapSupport := planar_laplacian_compact_support φ hSupport hφ
  obtain ⟨C, hBound⟩ := hLapSupport.exists_bound_of_continuous hLapCont
  obtain ⟨R, hR⟩ := hLapSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hZero : ∀ z, z ∉ Metric.closedBall 0 R → (Δ φ) z = 0 := by
    intro z hz
    exact image_eq_zero_of_notMem_tsupport (fun h => hz (hR h))
  have hProb := spectral_log_potential_compact_test_difference_convergence μ A B hA hB
    hEnergyA hEnergyB hLog R (Δ φ) (max C 0) (le_max_right _ _)
    (fun z => (hBound z).trans (le_max_left _ _)) hZero
  intro ε hε
  apply varying_probability_event_of_subset μ _ (hProb ((2 * Real.pi) * ε) (by positivity))
  intro n ω hω
  change (2 * Real.pi) * ε < |(∫ z : ℂ,
    (Δ φ) z * (spectralLogPotential (A n ω) z - spectralLogPotential (B n ω) z)) - 0|
  rw [spectral_log_reconstructs_test_difference _ _ φ hφ hSupport, sub_zero, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  change ε < |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
    (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)) - 0| at hω
  rw [sub_zero] at hω
  exact mul_lt_mul_of_pos_left hω (by positivity)

end CircularLaw
