import CircularLaw.BLFiniteApproximation

/-! # Finite compact C2 families covering every bounded Lipschitz test on a disk -/

noncomputable section
open Classical Set
open scoped Topology

namespace CircularLaw

theorem bltest_finite_smooth_disk_cover (R : ℝ) {η : ℝ} (hη : 0 < η) (hηSmall : η ≤ 1) :
    ∃ s : Finset (ℂ → ℝ),
      (∀ φ ∈ s, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ ∀ z, |φ z| ≤ 2) ∧
      ∀ f : BLTest, ∃ φ ∈ s, ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| < η := by
  obtain ⟨t, hCover⟩ := bltest_finite_disk_cover R (half_pos hη)
  choose ψ hSmooth hCompact hBound hApprox using
    (fun f : BLTest => bltest_compact_smooth_approximation f R (half_pos hη) (by linarith))
  refine ⟨t.image ψ, ?_, ?_⟩
  · intro φ hφ
    rcases Finset.mem_image.mp hφ with ⟨f, _, rfl⟩
    exact ⟨hSmooth f, hCompact f, hBound f⟩
  · intro f
    obtain ⟨g, hg, hfg⟩ := hCover f
    refine ⟨ψ g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, ?_⟩
    intro z hz
    have hgψ : |g.val z - ψ g z| < η / 2 := by
      rw [abs_sub_comm]
      exact hApprox g z hz
    exact (abs_sub_le (f.val z) (g.val z) (ψ g z)).trans_lt
      (by linarith [hfg z hz])

end CircularLaw
