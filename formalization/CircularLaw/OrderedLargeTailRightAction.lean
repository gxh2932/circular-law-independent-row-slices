import CircularLaw.SeparatedBlockRightAction
import CircularLaw.OrderedBlockGeometry

/-!
# Right action with a large ordered tail

The low block contains every rank at or after the tail offset. Its
cardinality, rather than a second equal-size block, gives the direct
separated-pair estimate needed for the third steep class.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem norm_ordered_top_large_tail_separated {n rank tail : ℕ}
    (hRank : 0 < rank) (hRankFit : rank ≤ n) (hTailFit : tail ≤ n)
    (y : Fin n → ℂ) {t : ℝ}
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩)
    (l : Fin n) (hl : l ∈ orderedRankBlock (normOrderPerm y) 0
      (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1))
    (j : Fin n) (hj : j ∈ orderedRankBlock (normOrderPerm y) tail
      (show tail + 1 * (n - tail) ≤ n by omega) (0 : Fin 1)) :
    t < dist (y l) (y j) := by
  have hL := orderedRankBlock_rank_bounds (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1) hl
  have hR := orderedRankBlock_rank_bounds (normOrderPerm y) tail
    (show tail + 1 * (n - tail) ≤ n by omega) (0 : Fin 1) hj
  have hRankOrder : (normOrderPerm y).symm l ≤ ⟨rank - 1, by omega⟩ :=
    Fin.le_iff_val_le_val.mpr (by change ((normOrderPerm y).symm l).val ≤ rank - 1; omega)
  have hNorm := orderedNorm_antitone y hRankOrder
  have hSep := (hGap ((normOrderPerm y).symm j) hR.1).trans_le hNorm
  rw [orderedNorm_of_rank, orderedNorm_of_rank] at hSep
  simpa only [show (2 : ℝ) * (t / 2) = t by ring] using
    norm_gap_implies_equal_block_separation (r := t / 2) (by
      simpa only [show (2 : ℝ) * (t / 2) = t by ring] using hSep)

theorem row_slice_ordered_large_tail_right_action_norm_small_ball {n d K rank tail : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (hRank : 0 < rank) (hRankFit : rank ≤ n)
    (hTail : 4 * tail ≤ n) (hRows : (n : ℝ) / 2 ≤ K) (y : Fin n → ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩)
    (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤ Real.sqrt n / 3) ≤
      (8 * Real.exp 1 * separatedBlockSmallBallCoefficient ((rank : ℝ) * ((d : ℝ) / n))) ^ K := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * (n - tail) ≤ n by omega) (0 : Fin 1)
  have hL : L.Nonempty := orderedRankBlock_nonempty _ _ _ hRank _
  have hR : 3 * (n : ℝ) / 4 ≤ R.card := by
    rw [show R.card = n - tail from orderedRankBlock_card _ _ _ _,
      Nat.cast_sub (by omega : tail ≤ n)]
    have hTailR : 4 * (tail : ℝ) ≤ n := by exact_mod_cast hTail
    linarith
  have h := row_slice_separated_blocks_right_action_norm_small_ball hd hSize L R hL hR
    hRows y (fun l hl j hj => (norm_ordered_top_large_tail_separated hRank hRankFit
      (by omega : tail ≤ n) y hGap l hl j hj).le) V
  rw [show L.card = rank from orderedRankBlock_card _ _ _ _, mul_comm ((d : ℝ) / n)] at h
  exact h

theorem row_slice_retained_ordered_large_tail_right_action_norm_small_ball {n d rank tail : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (hRank : 0 < rank) (hRankFit : rank ≤ n)
    (hTail : 4 * tail ≤ n) (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card)
    (y : Fin n → ℂ) (c ζ : ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt n / 3) ≤
      (8 * Real.exp 1 * separatedBlockSmallBallCoefficient ((rank : ℝ) * ((d : ℝ) / n))) ^ I.card := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * (n - tail) ≤ n by omega) (0 : Fin 1)
  have hL : L.Nonempty := orderedRankBlock_nonempty _ _ _ hRank _
  have hR : 3 * (n : ℝ) / 4 ≤ R.card := by
    rw [show R.card = n - tail from orderedRankBlock_card _ _ _ _,
      Nat.cast_sub (by omega : tail ≤ n)]
    have hTailR : 4 * (tail : ℝ) ≤ n := by exact_mod_cast hTail
    linarith
  have h := row_slice_retained_separated_blocks_right_action_norm_small_ball hd hSize L R hL hR
    I hRows y c ζ (fun l hl j hj => (norm_ordered_top_large_tail_separated hRank hRankFit
      (by omega : tail ≤ n) y hGap l hl j hj).le)
  rw [show L.card = rank from orderedRankBlock_card _ _ _ _, mul_comm ((d : ℝ) / n)] at h
  exact h

end CircularLaw
