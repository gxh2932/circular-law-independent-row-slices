import CircularLaw.UniformBasisSpread
import CircularLaw.BernoulliExposureSmallBall

/-!
# Actual Bernoulli projection bounds for every nonzero subspace

The uniform spread basis is proved to exist. The probability estimates
therefore take the subspace and its dimension as data, with no unproved
basis-spread assumption. Radius compatibility remains explicit.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def subspaceSpreadRadius {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) : ℝ :=
  Real.sqrt (Module.finrank ℂ V : ℝ) / (64 * Fintype.card ι)

def subspaceSpreadCoordinateCount {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) : ℕ :=
  Nat.ceil ((Module.finrank ℂ V : ℝ) / 4096)

theorem subspace_spread_radius_pos {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V) :
    0 < subspaceSpreadRadius V := by
  have hn : 0 < Fintype.card ι := by
    have hLe := V.finrank_le
    rw [finrank_euclideanSpace] at hLe
    exact lt_of_lt_of_le hV hLe
  have hDim : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  have hCard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  exact div_pos (Real.sqrt_pos.mpr hDim) (mul_pos (by norm_num) hCard)

theorem subspace_spread_coordinate_count_pos {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V) :
    0 < subspaceSpreadCoordinateCount V := by
  apply Nat.ceil_pos.mpr
  have hDim : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  positivity

theorem exists_subspace_spread_basis {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V) :
    ∃ B : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V, ∀ j,
      (coordinateSpreadSet (B j : EuclideanSpace ℂ ι) (subspaceSpreadRadius V)).Nonempty ∧
      subspaceSpreadCoordinateCount V ≤
        (coordinateSpreadSet (B j : EuclideanSpace ℂ ι) (subspaceSpreadRadius V)).card := by
  obtain ⟨B, hB⟩ := exists_subspace_uniform_coordinate_spread V hV
  refine ⟨B, fun j => ?_⟩
  have hCard : subspaceSpreadCoordinateCount V ≤
      (coordinateSpreadSet (B j : EuclideanSpace ℂ ι) (subspaceSpreadRadius V)).card :=
    Nat.ceil_le.mpr (hB j)
  exact ⟨Finset.card_pos.mp ((subspace_spread_coordinate_count_pos V hV).trans_le hCard), hCard⟩

theorem bernoulli_projection_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    (u : EuclideanSpace ℂ ι) {t : ℝ} (ht : subspaceSpreadRadius V / 2 ≤ t) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Module.finrank ℂ V : ℝ) * t ^ 2 / 2} ≤
      2 * bernoulliScalarSmallBallConstant * (t / subspaceSpreadRadius V) /
        Real.sqrt ((subspaceSpreadCoordinateCount V : ℝ) * p) := by
  obtain ⟨B, hB⟩ := exists_subspace_spread_basis V hV
  simpa only [Fintype.card_fin] using
    bernoulli_projection_small_ball_of_uniform_spread p hp hpPos hHalf V B
      (by simpa using hV) u
      (fun j => coordinateSpreadSet (B j : EuclideanSpace ℂ ι) (subspaceSpreadRadius V))
      (fun j => (hB j).1) (subspace_spread_coordinate_count_pos V hV) (fun j => (hB j).2)
      (subspace_spread_radius_pos V hV)
      (fun j i hi => (coordinate_spread_set_mem _ _ i).mp hi) ht

theorem bernoulli_projection_norm_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    (u : EuclideanSpace ℂ ι) {t R : ℝ} (ht : subspaceSpreadRadius V / 2 ≤ t)
    (hR : 0 ≤ R) (hRadius : R ^ 2 ≤ (Module.finrank ℂ V : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ≤
      2 * bernoulliScalarSmallBallConstant * (t / subspaceSpreadRadius V) /
        Real.sqrt ((subspaceSpreadCoordinateCount V : ℝ) * p) := by
  have hContainment :
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Module.finrank ℂ V : ℝ) * t ^ 2 / 2} := by
    intro x hx
    have hNorm := norm_nonneg (V.starProjection (bernoulliCubeVector x + u))
    exact (sq_le_sq₀ hNorm hR |>.mpr hx.le).trans hRadius
  exact (measureReal_mono (h₂ := by finiteness) hContainment).trans
    (bernoulli_projection_small_ball p hp hpPos hHalf V hV u ht)

theorem bernoulli_row_log_failure_of_subspace_dimension {r n m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hOld : 0 < leadingRowSingularProduct A h)
    (hDim : 0 < Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin))
    (u : EuclideanSpace ℂ (Fin m)) {t N δ : ℝ} (hN : 0 < N)
    (ht : subspaceSpreadRadius (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) / 2 ≤ t)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤
      (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw (Fin m) p hp).real
      {x | leadingRowLogPrefix A h / N + δ <
        insertedLeadingLogPrefix A h (bernoulliCubeVector x + u) / N} ≤
      2 * bernoulliScalarSmallBallConstant *
        (t / subspaceSpreadRadius (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)) /
        Real.sqrt ((subspaceSpreadCoordinateCount
          (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) * p) := by
  have hFailure := row_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin m) p hp) A h (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN
  simp_rw [row_adjoint_bernoulli_shift] at hFailure
  exact hFailure.trans (bernoulli_projection_norm_small_ball
    p hp hpPos hHalf _ hDim (rowAdjointVector u) ht (Real.exp_pos _).le hRadius)

theorem bernoulli_column_log_failure_of_subspace_dimension {r n m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (hOld : 0 < leadingRowSingularProduct A hRow)
    (hDim : 0 < Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin))
    (u : EuclideanSpace ℂ (Fin n)) {t N δ : ℝ} (hN : 0 < N)
    (ht : subspaceSpreadRadius
      (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) / 2 ≤ t)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤ (Module.finrank ℂ
      (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw (Fin n) p hp).real
      {x | leadingRowLogPrefix A hRow / N + δ <
        insertedColumnLeadingLogPrefix A hNext (bernoulliCubeVector x + u) / N} ≤
      2 * bernoulliScalarSmallBallConstant * (t / subspaceSpreadRadius
        (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin)) /
        Real.sqrt ((subspaceSpreadCoordinateCount
          (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) : ℝ) * p) := by
  exact (column_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin n) p hp) A hRow hCol hNext
    (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN).trans
      (bernoulli_projection_norm_small_ball p hp hpPos hHalf _ hDim u ht (Real.exp_pos _).le hRadius)

end CircularLaw
