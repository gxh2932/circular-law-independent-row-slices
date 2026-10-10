import CircularLaw.BLCompactSmoothApproximation
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# A finite family of actual bounded Lipschitz tests on each disk

Arzelà--Ascoli supplies compact closure of the restricted actual tests.
The finite cover has centers in that family, and lifting the centers
retains their global bound one and Lipschitz constant one.
-/

noncomputable section
open Classical Set
open scoped Topology BoundedContinuousFunction

namespace CircularLaw

def restrictedBLTest (R : ℝ) (f : BLTest) : (Metric.closedBall (0 : ℂ) R) →ᵇ ℝ where
  toFun z := f.val z
  continuous_toFun := f.2.2.continuous.comp continuous_subtype_val
  map_bounded' := ⟨2, fun x y => by
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [f.2.1 x, f.2.1 y])⟩

theorem restricted_bltest_lipschitz (R : ℝ) (f : BLTest) :
    LipschitzWith 1 (restrictedBLTest R f) := by
  simpa using f.2.2.comp (LipschitzWith.subtype_val (Metric.closedBall (0 : ℂ) R))

theorem restricted_bltest_compact_closure (R : ℝ) :
    IsCompact (closure (range (restrictedBLTest R))) := by
  letI : CompactSpace (Metric.closedBall (0 : ℂ) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) R)
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc
  · intro g z hg
    rcases hg with ⟨f, rfl⟩
    exact abs_le.mp (f.2.1 z)
  · apply (LipschitzWith.uniformEquicontinuous _ 1 _).equicontinuous
    intro g
    rcases g.2 with ⟨f, hf⟩
    simpa only [← hf] using restricted_bltest_lipschitz R f

theorem bltest_finite_disk_cover (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ s : Finset BLTest, ∀ f : BLTest, ∃ g ∈ s,
      ∀ z ∈ Metric.closedBall 0 R, |f.val z - g.val z| < η := by
  obtain ⟨t, htRange, htFinite, htCover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure (restricted_bltest_compact_closure R) hη
  letI : Fintype t := htFinite.fintype
  let c : t → BLTest := fun g => Classical.choose (htRange g.2)
  have hc : ∀ g : t, restrictedBLTest R (c g) = g.val := fun g =>
    Classical.choose_spec (htRange g.2)
  refine ⟨Finset.univ.image c, ?_⟩
  intro f
  have hCover := htCover (show restrictedBLTest R f ∈ range (restrictedBLTest R) from ⟨f, rfl⟩)
  rcases mem_iUnion.mp hCover with ⟨g, hg⟩
  rcases mem_iUnion.mp hg with ⟨hgt, hBall⟩
  let g' : t := ⟨g, hgt⟩
  refine ⟨c g', Finset.mem_image.mpr ⟨g', Finset.mem_univ _, rfl⟩, ?_⟩
  intro z hz
  have hDist := BoundedContinuousFunction.dist_coe_le_dist
    (f := restrictedBLTest R f) (g := g) (⟨z, hz⟩ : Metric.closedBall (0 : ℂ) R)
  have hcg : restrictedBLTest R (c g') = g := hc g'
  rw [← hcg] at hDist
  exact (show |f.val z - (c g').val z| ≤ dist (restrictedBLTest R f) (restrictedBLTest R (c g')) by
    simpa only [Real.dist_eq, restrictedBLTest] using hDist).trans_lt
      (by simpa only [hcg, Metric.mem_ball, dist_comm] using hBall)

end CircularLaw
