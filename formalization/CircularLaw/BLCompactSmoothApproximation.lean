import CircularLaw.SpectralLogReconstruction
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Compact C2 approximation of bounded Lipschitz tests

Uniform smoothing of the actual test, followed by a smooth disk cutoff,
gives compact C2 tests bounded by two on the whole plane. The cutoff is
one on the prescribed disk, so the spatial approximation is unchanged.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped Topology ContDiff

namespace CircularLaw

theorem bltest_compact_smooth_approximation (f : BLTest) (R : ℝ) {η : ℝ}
    (hη : 0 < η) (hηSmall : η ≤ 1) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      (∀ z, |φ z| ≤ 2) ∧ ∀ z ∈ Metric.closedBall 0 R, |φ z - f.val z| < η := by
  obtain ⟨g, hg, hApprox⟩ := f.2.2.uniformContinuous.exists_contDiff_dist_le hη
  let b : ContDiffBump (0 : ℂ) :=
    ⟨max R 1, max R 1 + 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), by linarith⟩
  refine ⟨fun z => b z * g z, b.contDiff.mul
    (hg.of_le (by exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))), b.hasCompactSupport.mul_right,
    ?_, ?_⟩
  · intro z
    have hb : |b z| ≤ 1 := by rw [abs_of_nonneg b.nonneg]; exact b.le_one
    have hgBound : |g z| ≤ 2 := by
      have hDist : |g z - f.val z| < η := by simpa only [Real.dist_eq] using hApprox z
      have hAbs := abs_add_le (g z - f.val z) (f.val z)
      rw [sub_add_cancel] at hAbs
      linarith [f.2.1 z]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (by simpa using hgBound)
  · intro z hz
    have hb : b z = 1 := b.one_of_mem_closedBall
      ((Metric.closedBall_subset_closedBall (le_max_left R 1)) hz)
    change |b z * g z - f.val z| < η
    rw [hb, one_mul]
    simpa only [Real.dist_eq] using hApprox z

end CircularLaw
