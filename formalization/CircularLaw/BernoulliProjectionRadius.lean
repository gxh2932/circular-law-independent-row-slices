import CircularLaw.BernoulliSubspaceSmallBall

/-!
# Projection small balls at the circular-law exposure scale

The scalar radius is enlarged by half the spread radius. This supplies
the scalar estimate at every requested projection radius. The resulting
bound has a linear radius term and an inverse square-root dimension term.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem subspace_spread_count_sqrt_lower {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (p : ℝ≥0) :
    Real.sqrt ((Module.finrank ℂ V : ℝ) * p) / 64 ≤
      Real.sqrt ((subspaceSpreadCoordinateCount V : ℝ) * p) := by
  have hCeil : (Module.finrank ℂ V : ℝ) / 4096 ≤
      (subspaceSpreadCoordinateCount V : ℝ) := Nat.le_ceil _
  have hProduct := mul_le_mul_of_nonneg_right hCeil p.coe_nonneg
  have hDim := Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ V)
  have hCount := Nat.cast_nonneg (α := ℝ) (subspaceSpreadCoordinateCount V)
  have hSquare := Real.sq_sqrt (mul_nonneg hDim p.coe_nonneg)
  have hCountSquare := Real.sq_sqrt (mul_nonneg hCount p.coe_nonneg)
  have hRoot := Real.sqrt_nonneg ((Module.finrank ℂ V : ℝ) * p)
  have hCountRoot := Real.sqrt_nonneg ((subspaceSpreadCoordinateCount V : ℝ) * p)
  nlinarith

theorem bernoulli_projection_radius_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    (u : EuclideanSpace ℂ ι) {κ : ℝ} (hκ : 0 ≤ κ) {n : ℕ} (hn : 0 < n) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ <
        κ * Real.sqrt (p : ℝ) * (Module.finrank ℂ V : ℝ) *
          Real.sqrt (Module.finrank ℂ V : ℝ) / n} ≤
      16384 * bernoulliScalarSmallBallConstant * κ * ((Fintype.card ι : ℝ) / n) +
        64 * bernoulliScalarSmallBallConstant /
          Real.sqrt ((Module.finrank ℂ V : ℝ) * p) := by
  let h : ℝ := Module.finrank ℂ V
  let ρ := subspaceSpreadRadius V
  let a : ℝ := 2 * κ * Real.sqrt (p : ℝ) * h / n
  let t := a + ρ / 2
  let R := κ * Real.sqrt (p : ℝ) * h * Real.sqrt h / n
  have hDim : 0 < h := by
    change 0 < (Module.finrank ℂ V : ℝ)
    exact_mod_cast hV
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRho : 0 < ρ := subspace_spread_radius_pos V hV
  have hA : 0 ≤ a := by positivity
  have hT : ρ / 2 ≤ t := by dsimp [t]; linarith
  have hRootSquare := Real.sq_sqrt hDim.le
  have hRadius : R ^ 2 ≤ h * t ^ 2 / 2 := by
    have hTLower : a ≤ t := by dsimp [t]; linarith
    have hTSquare := (sq_le_sq₀ hA (hA.trans hTLower)).mpr hTLower
    have hIdentity : R ^ 2 = h * a ^ 2 / 4 := by
      dsimp [R, a]
      field_simp
      nlinarith only [hRootSquare]
    rw [hIdentity]
    nlinarith [mul_nonneg hDim.le (sq_nonneg a)]
  have hBound := bernoulli_projection_norm_small_ball p hp hpPos hHalf V hV u hT
    (by dsimp [R]; positivity) hRadius
  have hRootPos : 0 < Real.sqrt (h * p) := Real.sqrt_pos.mpr (mul_pos hDim hpPos)
  have hNumerator : 0 ≤ 2 * bernoulliScalarSmallBallConstant * (t / ρ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
      (div_nonneg ((by positivity : 0 ≤ ρ / 2).trans hT) hRho.le)
  have hWeaker := div_le_div_of_nonneg_left hNumerator
    (div_pos hRootPos (by norm_num)) (subspace_spread_count_sqrt_lower V p)
  have hAmbient : 0 < (Fintype.card ι : ℝ) := by
    have hLe := V.finrank_le
    rw [finrank_euclideanSpace] at hLe
    exact_mod_cast lt_of_lt_of_le hV hLe
  have hRootDim : 0 < Real.sqrt h := Real.sqrt_pos.mpr hDim
  have hRootP : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpPos
  have hSimplify : 2 * bernoulliScalarSmallBallConstant * (t / ρ) /
      (Real.sqrt (h * p) / 64) =
      16384 * bernoulliScalarSmallBallConstant * κ * ((Fintype.card ι : ℝ) / n) +
        64 * bernoulliScalarSmallBallConstant / Real.sqrt (h * p) := by
    dsimp [t, a, ρ, subspaceSpreadRadius]
    change 2 * bernoulliScalarSmallBallConstant *
      ((2 * κ * Real.sqrt (p : ℝ) * h / n + (Real.sqrt h / (64 * Fintype.card ι)) / 2) /
        (Real.sqrt h / (64 * Fintype.card ι))) / (Real.sqrt (h * p) / 64) = _
    rw [Real.sqrt_mul hDim.le]
    field_simp
    ring_nf
    rw [hRootSquare]
    ring
  exact (hBound.trans hWeaker).trans_eq hSimplify

theorem bernoulli_projection_radius_bound_of_ambient_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V)
    (u : EuclideanSpace ℂ ι) {κ : ℝ} (hκ : 0 ≤ κ) {n : ℕ} (hn : 0 < n)
    (hAmbient : Fintype.card ι ≤ n) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ <
        κ * Real.sqrt (p : ℝ) * (Module.finrank ℂ V : ℝ) *
          Real.sqrt (Module.finrank ℂ V : ℝ) / n} ≤
      16384 * bernoulliScalarSmallBallConstant *
        (κ + 1 / Real.sqrt ((Module.finrank ℂ V : ℝ) * p)) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRatio : (Fintype.card ι : ℝ) / n ≤ 1 := by
    apply (div_le_one hnReal).mpr
    exact_mod_cast hAmbient
  have hCoef : 0 ≤ 16384 * bernoulliScalarSmallBallConstant * κ := by
    exact mul_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le) hκ
  have hBound := bernoulli_projection_radius_bound p hp hpPos hHalf V hV u hκ hn
  have hRatioBound := mul_le_mul_of_nonneg_left hRatio hCoef
  have hTail := div_nonneg bernoulli_scalar_small_ball_constant_pos.le
    (Real.sqrt_nonneg ((Module.finrank ℂ V : ℝ) * p))
  simp only [mul_one] at hRatioBound
  calc
    _ ≤ 16384 * bernoulliScalarSmallBallConstant * κ +
        64 * bernoulliScalarSmallBallConstant / Real.sqrt ((Module.finrank ℂ V : ℝ) * p) :=
      hBound.trans (add_le_add hRatioBound le_rfl)
    _ ≤ _ := by
      have hTarget : 16384 * bernoulliScalarSmallBallConstant *
          (κ + 1 / Real.sqrt ((Module.finrank ℂ V : ℝ) * p)) =
          16384 * bernoulliScalarSmallBallConstant * κ +
            16384 * (bernoulliScalarSmallBallConstant / Real.sqrt ((Module.finrank ℂ V : ℝ) * p)) := by
        ring
      rw [hTarget, mul_div_assoc]
      nlinarith

end CircularLaw
