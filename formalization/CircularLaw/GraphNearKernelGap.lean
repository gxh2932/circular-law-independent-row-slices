import CircularLaw.GraphCoordinateGap

/-!
# Near-kernel vectors cannot have the graph coordinate gap

Actual coordinate counts give a lower bound on squared Euclidean norm.
The checked graph amplification therefore excludes a coordinate gap when
the matrix image has smaller energy. Graph budgets remain explicit.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem coordinate_spread_set_energy_lower {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) {t : ℝ} (ht : 0 ≤ t) :
    ((coordinateSpreadSet v t).card : ℝ) * t ^ 2 ≤ ‖v‖ ^ 2 := by
  calc
    ((coordinateSpreadSet v t).card : ℝ) * t ^ 2 =
        ∑ i ∈ coordinateSpreadSet v t, t ^ 2 := by simp
    _ ≤ ∑ i ∈ coordinateSpreadSet v t, ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ ht (norm_nonneg _)).mpr ((coordinate_spread_set_mem v t i).mp hi)
    _ ≤ ∑ i, ‖v i‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => sq_nonneg ‖v i‖)
    _ = ‖v‖ ^ 2 := (EuclideanSpace.norm_sq_eq v).symm

theorem image_spread_energy_lower {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) {β a b : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hSpread : b / 2 ≤ ((coordinateSpreadSet v (β * a / 2)).card : ℝ)) :
    b * β ^ 2 * a ^ 2 / 8 ≤ ‖v‖ ^ 2 := by
  have hThreshold : 0 ≤ β * a / 2 := by positivity
  have hEnergy := coordinate_spread_set_energy_lower v hThreshold
  have hMul := mul_le_mul_of_nonneg_right hSpread (sq_nonneg (β * a / 2))
  calc
    b * β ^ 2 * a ^ 2 / 8 = (b / 2) * (β * a / 2) ^ 2 := by ring
    _ ≤ ((coordinateSpreadSet v (β * a / 2)).card : ℝ) * (β * a / 2) ^ 2 := hMul
    _ ≤ ‖v‖ ^ 2 := hEnergy

set_option maxHeartbeats 1000000 in
theorem unique_neighbourhood_ordered_gap_energy_lower {ρ : Type*} [Fintype ρ]
    {m ell g : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) (hEll : 0 < ell) (hg : 0 < g)
    (hRank : ell + g ≤ m) {β d n b : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 4 ≤ d) (hn : 0 < n)
    (hEllN : (ell : ℝ) ≤ n) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hGap : orderedNormAt (fun j => v j) (ell + g) ≤
      orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7)
    (hUnique : b ≤ ((matrixUniqueNeighbourhood A e β
      (orderedPrefix (fun j => v j) ell)).card : ℝ))
    (hHeavy : ((matrixHeavyRows A ((d * n / (β * ell)) ^ 5 / β)).card : ℝ) ≤ b / 4)
    (hColumns : ((∑ j ∈ coordinateMiddleSet (orderedPrefix (fun j => v j) ell)
      (orderedPrefix (fun j => v j) (ell + g - 1)), ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) ≤ b / 4) :
    b * β ^ 2 * orderedNormAt (fun j => v j) ell ^ 2 / 8 ≤
      ‖(diagonalEmbeddedShift A e z).toEuclideanLin v‖ ^ 2 := by
  exact image_spread_energy_lower _ hβ.le (orderedNormAt_nonneg _ _)
    (unique_neighbourhood_ordered_image_spread A e z v hEll hg hRank hβ hβOne hd hn
      hEllN hz hzUpper hGap hUnique hHeavy hColumns)

set_option maxHeartbeats 1000000 in
theorem near_kernel_ordered_coordinate_no_gap {ρ : Type*} [Fintype ρ]
    {m ell g : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) (hEll : 0 < ell) (hg : 0 < g)
    (hRank : ell + g ≤ m) {β d n b : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 4 ≤ d) (hn : 0 < n)
    (hEllN : (ell : ℝ) ≤ n) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hUnique : b ≤ ((matrixUniqueNeighbourhood A e β
      (orderedPrefix (fun j => v j) ell)).card : ℝ))
    (hHeavy : ((matrixHeavyRows A ((d * n / (β * ell)) ^ 5 / β)).card : ℝ) ≤ b / 4)
    (hColumns : ((∑ j ∈ coordinateMiddleSet (orderedPrefix (fun j => v j) ell)
      (orderedPrefix (fun j => v j) (ell + g - 1)), ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) ≤ b / 4)
    (hSmall : ‖(diagonalEmbeddedShift A e z).toEuclideanLin v‖ ^ 2 <
      b * β ^ 2 * orderedNormAt (fun j => v j) ell ^ 2 / 8) :
    orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7 <
      orderedNormAt (fun j => v j) (ell + g) := by
  by_contra hNot
  have hGap := le_of_not_gt hNot
  have hEnergy := unique_neighbourhood_ordered_gap_energy_lower A e z v hEll hg hRank
    hβ hβOne hd hn hEllN hz hzUpper hGap hUnique hHeavy hColumns
  exact (not_lt_of_ge hEnergy) hSmall

end CircularLaw
