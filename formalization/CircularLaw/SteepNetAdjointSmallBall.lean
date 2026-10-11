import CircularLaw.OrderedAdjointSmallBall
import CircularLaw.SteepNetSmallBall

/-!
# Actual adjoint small balls for the finite steep grids

The ordered gap survives every constant shift. The net union charges
the exact cardinalities and the selected-row conditioning factor.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem steep_net_fixed_vector_adjoint {n d rank next : ℕ} {cap : ℝ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank)
    (hRankNext : rank ≤ next) (hFit : next + rank ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ steepNonconstantNet n d rank next cap) (w ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ rank *
        (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ n := by
  have hBound := row_slice_ordered_adjoint_small_ball hd hDegree hRank hRankNext hFit u w ζ
    (by norm_num : (0 : ℝ) < 1 / 3) (le_refl (1 : ℝ)) (by
      simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using
        steepNonconstantNet_ordered_gap hRank hRankNext hFit u hu)
  apply (uniformProbability_mono ?_).trans (by simpa only [one_pow, mul_one] using hBound)
  intro rows hSmall
  have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hSquare
  convert hSquare using 1
  ring

theorem steep_net_adjoint_union_probability {n d rank next : ℕ} {cap : ℝ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank)
    (hRankNext : rank ≤ next) (hFit : next + rank ≤ n) (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ steepNonconstantNet n d rank next cap, ∃ w ∈ C,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3) ≤
      ((steepNonconstantNet n d rank next cap).card : ℝ) * C.card *
        ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ rank *
          (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ n) := by
  apply (uniformProbability_finset_exists_le (steepNonconstantNet n d rank next cap) _).trans
  calc
    _ ≤ ∑ _u ∈ steepNonconstantNet n d rank next cap,
        (C.card : ℝ) * ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ rank *
          (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ n) := by
      apply Finset.sum_le_sum
      intro u hu
      apply (uniformProbability_finset_exists_le C _).trans
      calc
        _ ≤ ∑ _w ∈ C, (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ rank *
            (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
              Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ n :=
          Finset.sum_le_sum (fun w _ => steep_net_fixed_vector_adjoint hd hDegree hRank hRankNext hFit u hu w ζ)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CircularLaw
