import CircularLaw.BernoulliLargeProjection

/-!
# Large-dimension row and column exposure bounds

The actual logarithmic failure events are bounded by the proved large
projection estimate. The needed scalar threshold comparison is retained
explicitly; basis existence and projection probability are supplied.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem bernoulli_large_subspace_projection_of_radius_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (hAmbient : Fintype.card ι ≤ n)
    (hd : 1 ≤ (n : ℝ) * p) (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (hLarge : (n : ℝ) * ((n : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ (Module.finrank ℂ V : ℝ))
    (u : EuclideanSpace ℂ ι) {κ R : ℝ} (hκ : 0 ≤ κ)
    (hRadius : R ≤ κ * Real.sqrt ((n : ℝ) * p) *
      (Module.finrank ℂ V : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ≤
      bernoulliLargeProjectionConstant * (κ + ((n : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  have hContainment :
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ <
        κ * Real.sqrt ((n : ℝ) * p) * (Module.finrank ℂ V : ℝ) ^ (3 / 2 : ℝ) *
          (n : ℝ) ^ (-3 / 2 : ℝ)} := fun _ hx => hx.trans_le hRadius
  exact (measureReal_mono (h₂ := by finiteness) hContainment).trans
    (bernoulli_large_subspace_projection p hp hpPos hHalf hn hAmbient hd V hLarge u hκ)

theorem bernoulli_row_log_failure_of_large_dimension {r n m L : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (hL : 0 < L) (hm : m ≤ L) (hd : 1 ≤ (L : ℝ) * p)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hOld : 0 < leadingRowSingularProduct A h)
    (hLarge : (L : ℝ) * ((L : ℝ) * p) ^ (-1 / 4 : ℝ) ≤
      (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ))
    (u : EuclideanSpace ℂ (Fin m)) {κ N δ : ℝ} (hκ : 0 ≤ κ) (hN : 0 < N)
    (hRadius : Real.exp (-N * δ) ≤ κ * Real.sqrt ((L : ℝ) * p) *
      (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) ^ (3 / 2 : ℝ) *
        (L : ℝ) ^ (-3 / 2 : ℝ)) :
    (bernoulliCubeLaw (Fin m) p hp).real
      {x | leadingRowLogPrefix A h / N + δ <
        insertedLeadingLogPrefix A h (bernoulliCubeVector x + u) / N} ≤
      bernoulliLargeProjectionConstant * (κ + ((L : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  have hFailure := row_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin m) p hp) A h (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN
  simp_rw [row_adjoint_bernoulli_shift] at hFailure
  exact hFailure.trans (bernoulli_large_subspace_projection_of_radius_le p hp hpPos hHalf hL
    (by simpa only [Fintype.card_fin] using hm) hd _ hLarge (rowAdjointVector u) hκ hRadius)

theorem bernoulli_column_log_failure_of_large_dimension {r n m L : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (hL : 0 < L) (hn : n ≤ L) (hd : 1 ≤ (L : ℝ) * p)
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (hOld : 0 < leadingRowSingularProduct A hRow)
    (hLarge : (L : ℝ) * ((L : ℝ) * p) ^ (-1 / 4 : ℝ) ≤
      (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) : ℝ))
    (u : EuclideanSpace ℂ (Fin n)) {κ N δ : ℝ} (hκ : 0 ≤ κ) (hN : 0 < N)
    (hRadius : Real.exp (-N * δ) ≤ κ * Real.sqrt ((L : ℝ) * p) *
      (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) : ℝ) ^
        (3 / 2 : ℝ) * (L : ℝ) ^ (-3 / 2 : ℝ)) :
    (bernoulliCubeLaw (Fin n) p hp).real
      {x | leadingRowLogPrefix A hRow / N + δ <
        insertedColumnLeadingLogPrefix A hNext (bernoulliCubeVector x + u) / N} ≤
      bernoulliLargeProjectionConstant * (κ + ((L : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  exact (column_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin n) p hp) A hRow hCol hNext
    (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN).trans
      (bernoulli_large_subspace_projection_of_radius_le p hp hpPos hHalf hL
        (by simpa only [Fintype.card_fin] using hn) hd _ hLarge u hκ hRadius)

end CircularLaw
