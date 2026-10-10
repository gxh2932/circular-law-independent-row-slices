import CircularLaw.RowSliceFullAdjointSmallBall
import CircularLaw.OrderedBlockGeometry

/-!
# Ordered gaps give large adjoint coefficients after every constant shift

Two separated equal-size blocks force one entire block to have large
shifted coefficients. Only that block pays the row-conditioning cost.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem separated_blocks_large_shifted_coefficients {n k : ℕ}
    (L R : Finset (Fin n)) (hL : L.card = k) (hR : R.card = k)
    (y : Fin n → ℂ) (c : ℂ) {t : ℝ}
    (hSep : ∀ i ∈ L, ∀ j ∈ R, 2 * t < dist (y i) (y j)) :
    ∃ I : Finset (Fin n), I.card = k ∧ ∀ i ∈ I, t ≤ ‖y i + c‖ := by
  by_cases hLarge : ∀ i ∈ L, t ≤ ‖y i + c‖
  · exact ⟨L, hL, hLarge⟩
  · push_neg at hLarge
    obtain ⟨i, hi, hSmall⟩ := hLarge
    refine ⟨R, hR, ?_⟩
    intro j hj
    have hNorm : dist (y i) (y j) ≤ ‖y i + c‖ + ‖y j + c‖ := by
      rw [dist_eq_norm]
      have hEq : y i - y j = (y i + c) - (y j + c) := by ring
      rw [hEq]
      exact norm_sub_le _ _
    have hGap := hSep i hi j hj
    linarith

theorem row_slice_ordered_adjoint_small_ball {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hRankTail : rank ≤ tail)
    (hFit : tail + rank ≤ n) (y : Fin n → ℂ) (c ζ : ℂ) {t τ : ℝ}
    (ht : 0 < t) (hτ : 1 ≤ τ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 * t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => y i + c))‖ ^ 2 ≤ τ ^ 2 * t ^ 2 * n) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ rank *
        (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((rank : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ n := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * rank ≤ n by omega) (0 : Fin 1)
  have hL : L.card = rank := orderedRankBlock_card _ _ _ _
  have hR : R.card = rank := orderedRankBlock_card _ _ _ _
  obtain ⟨I, hCard, hLarge⟩ := separated_blocks_large_shifted_coefficients L R hL hR y c (by
    intro i hi j hj
    exact norm_ordered_blocks_separated y tail ⟨rank - 1, by omega⟩
      (by omega : 1 * rank ≤ n) (by omega : tail + 1 * rank ≤ n)
      (by change 1 * rank ≤ rank - 1 + 1; omega)
      hGap (0 : Fin 1) i hi j hj)
  have hI : I.Nonempty := Finset.card_pos.mp (by omega)
  have hBound := row_slice_full_adjoint_small_ball hd hDegree I hI
    (WithLp.toLp 2 (fun i => y i + c)) ht hLarge hτ ζ
  simpa only [hCard] using hBound

end CircularLaw
