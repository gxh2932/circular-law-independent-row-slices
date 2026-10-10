import CircularLaw.BLFiniteApproximation

/-!
# Integral error from approximation on a disk

A bounded-Lipschitz test has bound one and its smooth approximant bound
two. Their integral error is at most the disk approximation error plus
three times the actual outer spectral mass.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped Topology

namespace CircularLaw

theorem bl_integral_disk_approximation_bound (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : BLTest) (φ : ℂ → ℝ) (hf : Integrable f.val ν) (hφ : Integrable φ ν)
    (hBound : ∀ z, |φ z| ≤ 2) (R η : ℝ) (hη : 0 ≤ η)
    (hApprox : ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η) :
    |(∫ z : ℂ, f.val z ∂ν) - ∫ z : ℂ, φ z ∂ν| ≤
      η + 3 * ν.real {z | R ≤ ‖z‖} := by
  let tail : Set ℂ := {z | R ≤ ‖z‖}
  have hTail : MeasurableSet tail := measurableSet_le measurable_const measurable_norm
  have hEnv : Integrable (fun z => η + tail.indicator (fun _ => (3 : ℝ)) z) ν :=
    (integrable_const η).add ((integrable_const 3).indicator hTail)
  have hPointwise : ∀ z : ℂ, |f.val z - φ z| ≤ η + tail.indicator (fun _ => (3 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ tail
    · rw [indicator_of_mem hz]
      exact (abs_sub _ _).trans (by linarith [f.2.1 z, hBound z])
    · rw [indicator_of_notMem hz, add_zero]
      apply hApprox z
      simp only [tail, mem_setOf_eq, not_le] at hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.le
  calc
    |(∫ z : ℂ, f.val z ∂ν) - ∫ z : ℂ, φ z ∂ν| = |∫ z : ℂ, f.val z - φ z ∂ν| := by
      rw [integral_sub hf hφ]
    _ ≤ ∫ z : ℂ, |f.val z - φ z| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, η + tail.indicator (fun _ => (3 : ℝ)) z ∂ν :=
      integral_mono (hf.sub hφ).norm hEnv hPointwise
    _ = η + 3 * ν.real tail := by
      rw [integral_add (integrable_const η) ((integrable_const 3).indicator hTail),
        integral_const, integral_indicator hTail, setIntegral_const]
      simp only [probReal_univ, smul_eq_mul]
      ring

theorem bl_spectral_integral_disk_approximation_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (f : BLTest) (φ : ℂ → ℝ)
    (hBound : ∀ z, |φ z| ≤ 2) (R η : ℝ) (hη : 0 ≤ η)
    (hApprox : ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η) :
    |(∫ z : ℂ, f.val z ∂empiricalSpectralMeasure A) -
      ∫ z : ℂ, φ z ∂empiricalSpectralMeasure A| ≤
      η + 3 * (empiricalSpectralMeasure A).real {z | R ≤ ‖z‖} := by
  letI : IsProbabilityMeasure (empiricalSpectralMeasure A) := ⟨empiricalSpectralMeasure_univ hn A⟩
  exact bl_integral_disk_approximation_bound _ f φ (empiricalSpectralMeasure_integrable A f.val)
    (empiricalSpectralMeasure_integrable A φ) hBound R η hη hApprox

end CircularLaw
