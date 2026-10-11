import CircularLaw.SeparatedBlockPairTail
import CircularLaw.RowSliceScalarSmallBall

/-!
# Direct slice small balls from large separated blocks

The scalar Bernoulli comparison applies only to the independent fair
choices within an exact pair sample. Its genuine pair-count failure
probability is supplied by the relative occupancy theorem above.
-/

noncomputable section
open Classical

namespace CircularLaw

def separatedBlockSmallBallCoefficient (μ : ℝ) : ℝ :=
  2 * bernoulliScalarSmallBallConstant / Real.sqrt μ + 2 * Real.exp (-μ / 48)

theorem separated_block_small_ball_coefficient_nonneg (μ : ℝ) :
    0 ≤ separatedBlockSmallBallCoefficient μ := by
  unfold separatedBlockSmallBallCoefficient
  have hC := bernoulli_scalar_small_ball_constant_pos.le
  positivity

theorem row_slice_separated_blocks_small_ball {n d : ℕ} (hd : 0 < d) (hSize : 2 * d ≤ n)
    (L R : Finset (Fin n)) (hLeft : L.Nonempty) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (y : Fin n → ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ / 2 ≤ r)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, ρ ≤ dist (y l) (y j)) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ r) ≤
      4 * bernoulliScalarSmallBallConstant * (r / ρ) /
        Real.sqrt (((d : ℝ) / n) * L.card) +
          2 * Real.exp (-(((d : ℝ) / n) * L.card) / 48) := by
  have hn : 0 < n := by omega
  let μ := ((d : ℝ) / n) * L.card
  have hμ : 0 < μ := by
    dsimp only [μ]
    exact mul_pos (div_pos (by exact_mod_cast hd) (by exact_mod_cast hn))
      (by exact_mod_cast Finset.card_pos.mpr hLeft)
  have hRoot : Real.sqrt ((μ / 8) / 2) = Real.sqrt μ / 4 := by
    rw [show (μ / 8) / 2 = μ / 16 by ring, Real.sqrt_div hμ.le]
    norm_num
  have hCoefficient : bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((μ / 8) / 2) =
      4 * bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt μ := by
    rw [hRoot, div_div_eq_mul_div]
    ring
  have h := row_slice_small_ball_le_real_pair_failure hSize y hρ hr
    (by positivity : 0 < μ / 8) z
  rw [hCoefficient] at h
  apply h.trans
  apply add_le_add le_rfl
  exact (uniformProbability_mono (fun _ he => he.le)).trans
    (paired_separated_block_count_relative_lower_tail hn hSize L R hR y ρ hSep)

theorem row_slice_separated_blocks_small_ball_quadratic {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (L R : Finset (Fin n))
    (hLeft : L.Nonempty) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (y : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, ρ ≤ dist (y l) (y j))
    {σ : ℝ} (hσ : 1 ≤ σ) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ σ * (ρ / 2)) ≤
      separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card) * σ ^ 2 := by
  have hRatio : (σ * (ρ / 2)) / ρ = σ / 2 := by field_simp
  have h := row_slice_separated_blocks_small_ball hd hSize L R hLeft hR y hρ
    (by nlinarith : ρ / 2 ≤ σ * (ρ / 2)) hSep z
  rw [hRatio] at h
  have hσSquare : σ ≤ σ ^ 2 := by nlinarith
  have hσSquareOne : 1 ≤ σ ^ 2 := by nlinarith
  have hA : 0 ≤ 2 * bernoulliScalarSmallBallConstant /
      Real.sqrt (((d : ℝ) / n) * L.card) := by
    have hC := bernoulli_scalar_small_ball_constant_pos.le
    positivity
  have hFirst := mul_le_mul_of_nonneg_left hσSquare hA
  have hTail := mul_le_mul_of_nonneg_left hσSquareOne
    (by positivity : 0 ≤ 2 * Real.exp (-(((d : ℝ) / n) * L.card) / 48))
  unfold separatedBlockSmallBallCoefficient
  apply h.trans
  convert add_le_add hFirst hTail using 1 <;> ring

end CircularLaw
