import CircularLaw.BLIntegralApproximation
import CircularLaw.BLFiniteSmoothFamily

/-! # Deterministic reduction of the full bounded-Lipschitz supremum to finite tests -/

noncomputable section
open Classical MeasureTheory Set
open scoped Topology ENNReal

namespace CircularLaw

theorem bl_spectral_test_difference_approximation {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (f : BLTest) (φ : ℂ → ℝ)
    (hBound : ∀ z, |φ z| ≤ 2) (R η : ℝ) (hη : 0 ≤ η)
    (hApprox : ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η) :
    |(∫ z : ℂ, f.val z ∂empiricalSpectralMeasure A) -
      ∫ z : ℂ, f.val z ∂empiricalSpectralMeasure B| ≤
      |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) -
        ∫ z : ℂ, φ z ∂empiricalSpectralMeasure B| + 2 * η +
      3 * (empiricalSpectralMeasure A).real {z | R ≤ ‖z‖} +
      3 * (empiricalSpectralMeasure B).real {z | R ≤ ‖z‖} := by
  have hA := bl_spectral_integral_disk_approximation_bound hn A f φ hBound R η hη hApprox
  have hB := bl_spectral_integral_disk_approximation_bound hn B f φ hBound R η hη hApprox
  have h1 := abs_sub_le (∫ z : ℂ, f.val z ∂empiricalSpectralMeasure A)
    (∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) (∫ z : ℂ, f.val z ∂empiricalSpectralMeasure B)
  have h2 := abs_sub_le (∫ z : ℂ, φ z ∂empiricalSpectralMeasure A)
    (∫ z : ℂ, φ z ∂empiricalSpectralMeasure B) (∫ z : ℂ, f.val z ∂empiricalSpectralMeasure B)
  rw [abs_sub_comm (∫ z : ℂ, φ z ∂empiricalSpectralMeasure B)] at h2
  linarith

theorem bounded_lipschitz_distance_finite_test_bound {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (s : Finset (ℂ → ℝ))
    (hBounds : ∀ φ ∈ s, ∀ z, |φ z| ≤ 2) (R η δ τ : ℝ) (hη : 0 ≤ η)
    (hCover : ∀ f : BLTest, ∃ φ ∈ s, ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η)
    (hTests : ∀ φ ∈ s, |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) -
      ∫ z : ℂ, φ z ∂empiricalSpectralMeasure B| ≤ δ)
    (hTailA : (empiricalSpectralMeasure A).real {z | R ≤ ‖z‖} ≤ τ)
    (hTailB : (empiricalSpectralMeasure B).real {z | R ≤ ‖z‖} ≤ τ) :
    boundedLipschitzDistance (empiricalSpectralMeasure A) (empiricalSpectralMeasure B) ≤
      ENNReal.ofReal (δ + 2 * η + 6 * τ) := by
  apply iSup_le
  intro f
  obtain ⟨φ, hφs, hApprox⟩ := hCover f
  apply ENNReal.ofReal_le_ofReal
  have h := bl_spectral_test_difference_approximation hn A B f φ (hBounds φ hφs) R η hη hApprox
  linarith [hTests φ hφs]

end CircularLaw
