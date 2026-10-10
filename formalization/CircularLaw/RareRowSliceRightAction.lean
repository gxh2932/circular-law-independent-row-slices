import CircularLaw.RareRowSliceSmallBall
import CircularLaw.RareSmallBallTensorization
import CircularLaw.FullMatrixFixedNet
import CircularLaw.OrderedBlockGeometry
import CircularLaw.FiniteLawTransport

/-!
# Rare right-action estimates for independent fixed-degree rows

Tensorization uses the direct row-slice scalar estimate. The resulting
exponential costs no conditioning factor and applies to an arbitrary
deterministic shift, hence to every retained shifted matrix.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem row_slice_ordered_rare_linear_form_small_ball {n d rank tail : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRank : 0 < rank) (hRankTail : rank ≤ tail) (hFit : tail + rank ≤ n)
    (hRare : rank = 1 ∨ (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (y : Fin n → ℂ) {t : ℝ} (ht : 0 < t)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ t / 3) ≤
      1 - (rank : ℝ) * ((d : ℝ) / n) / 2 := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * rank ≤ n by omega) (0 : Fin 1)
  apply row_slice_rare_equal_halves_small_ball hn hd hDegree hRank hRare L R
    (orderedRankBlock_top_tail_disjoint _ tail (by omega) (by omega) (by omega) 0 0)
    (orderedRankBlock_card _ _ _ _) (orderedRankBlock_card _ _ _ _) y ht
  intro l hl j hj
  have h := norm_ordered_blocks_separated y tail ⟨rank - 1, by omega⟩
    (by omega : 1 * rank ≤ n) (by omega : tail + 1 * rank ≤ n)
    (by change 1 * rank ≤ rank - 1 + 1; omega)
    (r := t / 2) (by simpa only [show 2 * (t / 2) = t by ring] using hGap)
    (0 : Fin 1) l hl j hj
  simpa only [show 2 * (t / 2) = t by ring] using h.le

theorem row_slice_rare_right_action_squared_small_ball {n d K m : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hm : 0 < m)
    (hRare : m = 1 ∨ (m : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (L R : Finset (Fin n)) (hDis : Disjoint L R) (hL : L.card = m) (hR : R.card = m)
    (y : Fin n → ℂ) {t : ℝ} (ht : 0 < t)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, t ≤ dist (y l) (y j)) (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      (∑ i, ‖rowLinearForm (rows i) y + V i‖ ^ 2) ≤
        t ^ 2 * ((m : ℝ) * ((d : ℝ) / n)) * K / 72) ≤
      Real.exp (-((m : ℝ) * ((d : ℝ) / n)) * K / 8) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty (by omega : d ≤ n)
  let ν := finiteUniformMeasure (RowSlice n d)
  let μ := Measure.pi (fun _ : Fin K => ν)
  let f := fun S : RowSlice n d => rowLinearForm S y
  rw [← finiteUniformMeasure_real, finiteUniformMeasure_pi]
  have h := finite_rare_small_ball_tensorization μ (fun i rows => f (rows i))
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)) ht
    (fun i => -V i) (by
      intro i
      have hLaw := finite_law_event_real (measurable_pi_apply i)
        (measurePreserving_eval (fun _ : Fin K => ν) i).map_eq
        (fun S : RowSlice n d => ‖f S - (-V i)‖ ≤ t / 3)
      rw [hLaw, finiteUniformMeasure_real]
      exact row_slice_rare_equal_halves_small_ball hn hd hDegree hm hRare
        L R hDis hL hR y ht hSep (-V i))
  simpa only [f, sub_neg_eq_add] using h

theorem row_slice_ordered_rare_right_action_norm_decay {n d K rank tail : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRank : 0 < rank) (hRankTail : rank ≤ tail) (hFit : tail + rank ≤ n)
    (hRare : rank = 1 ∨ (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (hRows : (n : ℝ) / 2 ≤ K) (y : Fin n → ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩)
    (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤ Real.sqrt ((rank : ℝ) * d) / 30) ≤
      Real.exp (-(rank : ℝ) * d / 16) := by
  let L := orderedRankBlock (normOrderPerm y) 0
    (show 0 + 1 * rank ≤ n by omega) (0 : Fin 1)
  let R := orderedRankBlock (normOrderPerm y) tail
    (show tail + 1 * rank ≤ n by omega) (0 : Fin 1)
  have hSep : ∀ l ∈ L, ∀ j ∈ R, (2 / 3 : ℝ) ≤ dist (y l) (y j) := by
    intro l hl j hj
    have h := norm_ordered_blocks_separated y tail ⟨rank - 1, by omega⟩
      (by omega : 1 * rank ≤ n) (by omega : tail + 1 * rank ≤ n)
      (by change 1 * rank ≤ rank - 1 + 1; omega)
      (r := 1 / 3) (by simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap)
      (0 : Fin 1) l hl j hj
    simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using h.le
  have hTensor := row_slice_rare_right_action_squared_small_ball hn hd hDegree hRank hRare
    L R (orderedRankBlock_top_tail_disjoint _ tail (by omega) (by omega) (by omega) 0 0)
    (orderedRankBlock_card _ _ _ _) (orderedRankBlock_card _ _ _ _) y
    (by norm_num : (0 : ℝ) < 2 / 3) hSep V
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hDensity : (rank : ℝ) * ((d : ℝ) / n) * ((n : ℝ) / 2) = (rank : ℝ) * d / 2 := by
    field_simp
  have hRowsMul := mul_le_mul_of_nonneg_left hRows
    (by positivity : 0 ≤ (rank : ℝ) * ((d : ℝ) / n))
  rw [hDensity] at hRowsMul
  apply (uniformProbability_mono ?_).trans (hTensor.trans ?_)
  · intro rows hSmall
    have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (rank : ℝ) * d)] at hSquare
    change ‖(WithLp.toLp 2 (fun i => rowLinearForm (rows i) y + V i) :
      EuclideanSpace ℂ (Fin K))‖ ^ 2 ≤ _ at hSquare
    rw [EuclideanSpace.norm_sq_eq] at hSquare
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) rank) (Nat.cast_nonneg (α := ℝ) d)]
  · apply Real.exp_le_exp.mpr
    linarith

theorem row_slice_retained_ordered_rare_right_action_norm_decay {n d rank tail : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRank : 0 < rank) (hRankTail : rank ≤ tail) (hFit : tail + rank ≤ n)
    (hRare : rank = 1 ∨ (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (y : Fin n → ℂ) (c ζ : ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30) ≤
      Real.exp (-(rank : ℝ) * d / 16) := by
  have h := full_matrix_retained_probability_bound (by omega : d ≤ n) I y
    (fun i => (d : ℂ) * c - ζ * (y i.val + c))
    (fun V => row_slice_ordered_rare_right_action_norm_decay hn hd hDegree
      hRank hRankTail hFit hRare hRows y hGap V)
  have hAction (rows : RowSliceMatrix n d) :
      (WithLp.toLp 2 (fun i : I => rowLinearForm (rows i.val) y +
        ((d : ℂ) * c - ζ * (y i.val + c))) : EuclideanSpace ℂ I) =
      (retainedShiftedMatrix I ζ rows).toEuclideanLin (WithLp.toLp 2 (fun j => y j + c)) := by
    ext i
    change _ = (retainedShiftedMatrix I ζ rows).mulVec (fun j => y j + c) i
    rw [retainedShiftedMatrix_mulVec, rowLinearForm_add_const]
    ring
  simpa only [indexedSliceMatrixVectorL2Norm, hAction] using h

theorem rare_steep_net_retained_right_action_union_probability {n d rank tail : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRank : 0 < rank) (hRankTail : rank ≤ tail) (hFit : tail + rank ≤ n)
    (hRare : rank = 1 ∨ (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card)
    (N : Finset (Fin n → ℂ))
    (hGap : ∀ u ∈ N, ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm u j < orderedNorm u ⟨rank - 1, by omega⟩)
    (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ N, ∃ w ∈ C, ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
        (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30) ≤
      (N.card : ℝ) * C.card * Real.exp (-(rank : ℝ) * d / 16) := by
  apply (uniformProbability_finset_exists_le N _).trans
  calc
    _ ≤ ∑ _u ∈ N, (C.card : ℝ) * Real.exp (-(rank : ℝ) * d / 16) := by
      apply Finset.sum_le_sum
      intro u hu
      apply (uniformProbability_finset_exists_le C _).trans
      calc
        _ ≤ ∑ _w ∈ C, Real.exp (-(rank : ℝ) * d / 16) :=
          Finset.sum_le_sum (fun w _ => row_slice_retained_ordered_rare_right_action_norm_decay
            hn hd hDegree hRank hRankTail hFit hRare I hRows u w ζ (hGap u hu))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CircularLaw
