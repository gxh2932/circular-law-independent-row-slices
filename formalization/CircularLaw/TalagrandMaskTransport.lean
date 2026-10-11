import CircularLaw.TalagrandGeometry

/-!
# Transporting Talagrand distance through coordinate maps

A map of the coordinate alphabet can merge values, which only decreases
its disagreement masks and convex distance. Injectivity is unnecessary.
Set enlargement also decreases convex distance for nonempty sets.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {ι α β : Type*} [Fintype ι]

theorem talagrandConvexDistance_mono {A B : Set (ι → α)} (hA : A.Nonempty)
    (hAB : A ⊆ B) (x : ι → α) : talagrandConvexDistance B x ≤ talagrandConvexDistance A x :=
  Metric.infDist_le_infDist_of_subset (convexHull_mono (Set.image_mono hAB))
    (talagrandMaskHull_nonempty hA x)

def talagrandCoordinateMap (e : α → β) (x : ι → α) : ι → β := fun i => e (x i)

omit [Fintype ι] in
theorem talagrandMask_map_le (e : α → β) (x y : ι → α) (i : ι) :
    talagrandMask (talagrandCoordinateMap e x) (talagrandCoordinateMap e y) i ≤ talagrandMask x y i := by
  by_cases h : x i = y i
  · simp [talagrandCoordinateMap, h]
  · simp only [talagrandMask_apply, h, if_false]
    split_ifs <;> norm_num

theorem talagrandMaskHull_map_witness (e : α → β) {A : Set (ι → α)} {x : ι → α}
    {v : EuclideanSpace ℝ ι} (hv : v ∈ talagrandMaskHull A x) :
    ∃ u ∈ talagrandMaskHull (talagrandCoordinateMap e '' A) (talagrandCoordinateMap e x),
      ∀ i, u i ≤ v i := by
  obtain ⟨γ, hγ, w, y, hw, hSum, hy, hEq⟩ := talagrandMaskHull_weights hv
  letI := hγ
  let u := ∑ j, w j • talagrandMask (talagrandCoordinateMap e x) (talagrandCoordinateMap e (y j))
  have hu : u ∈ talagrandMaskHull (talagrandCoordinateMap e '' A) (talagrandCoordinateMap e x) :=
    (convex_convexHull ℝ _).sum_mem (fun j _ => hw j) hSum
      (fun j _ => subset_convexHull ℝ _ ⟨talagrandCoordinateMap e (y j), ⟨y j, hy j, rfl⟩, rfl⟩)
  refine ⟨u, hu, ?_⟩
  intro i
  rw [← hEq]
  simp only [u, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (talagrandMask_map_le e x (y j) i) (hw j))

theorem euclidean_real_norm_le_of_coordinates {u v : EuclideanSpace ℝ ι}
    (hu : ∀ i, 0 ≤ u i) (h : ∀ i, u i ≤ v i) : ‖u‖ ≤ ‖v‖ := by
  have hSq : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hu i) (h i) 2)
  nlinarith [norm_nonneg u, norm_nonneg v]

theorem talagrandConvexDistance_map_le (e : α → β) {A : Set (ι → α)} (hA : A.Nonempty)
    (x : ι → α) :
    talagrandConvexDistance (talagrandCoordinateMap e '' A) (talagrandCoordinateMap e x) ≤
      talagrandConvexDistance A x := by
  obtain ⟨v, hv, hDist⟩ := talagrandConvexDistance_attained hA x
  obtain ⟨u, hu, hCoordinates⟩ := talagrandMaskHull_map_witness e hv
  have hNorm := euclidean_real_norm_le_of_coordinates (talagrandMaskHull_coordinate_nonneg hu) hCoordinates
  rw [hDist]
  apply le_trans _ hNorm
  simpa only [talagrandConvexDistance, dist_zero_left] using
    Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ ι)) hu

end CircularLaw
