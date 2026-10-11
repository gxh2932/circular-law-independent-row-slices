import CircularLaw.RareRowSliceSelectedAdjoint
import CircularLaw.RowSliceFullAdjointSmallBall
import CircularLaw.OrderedAdjointSmallBall

/-!
# Rare-coefficient small balls for the actual full shifted slice adjoint

Fixing every unselected row absorbs its contribution into the center.
The original row-slice law is retained, and only the chosen large
coefficients pay the conditioning loss. Ordered gaps give such a
chosen family after every constant shift of the vector.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem row_slice_full_rare_adjoint_decay {n d : ℕ} (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (I : Finset (Fin n)) (hRare : (I.card : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (x : EuclideanSpace ℂ (Fin n)) {t : ℝ} (ht : 0 < t)
    (hLarge : ∀ i ∈ I, t ≤ ‖x i‖) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ^ 2 ≤
        t ^ 2 * (I.card : ℝ) * d / 72) ≤ Real.exp (-(I.card : ℝ) * d / 16) := by
  haveI : Nonempty (RowSlice n d) := rowSlice_nonempty (by omega)
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ I) (fun _ => RowSlice n d)
  let center := fun rest : {i : Fin n // i ∉ I} → RowSlice n d => fun j : Fin n =>
    star ζ * x j - ∑ i : {i : Fin n // i ∉ I}, rowEntry (rest i) j * x i.val
  have hCoord (selected : I → RowSlice n d) (rest : {i : Fin n // i ∉ I} → RowSlice n d)
      (j : Fin n) :
      (fullShiftedSliceMatrix ζ (e.symm (selected, rest))).conjTranspose.toEuclideanLin x j =
        (∑ i : I, rowEntry (selected i) j * x i.val) - center rest j := by
    have hSelected : ∀ i : I, e.symm (selected, rest) i.val = selected i := by
      intro i
      simp only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, dif_pos i.property]
    have hRest : ∀ i : {i : Fin n // i ∉ I}, e.symm (selected, rest) i.val = rest i := by
      intro i
      simp only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, dif_neg i.property]
    rw [shifted_slice_adjoint_apply_eq_full_sum,
      ← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ I)
        (fun i => rowEntry (e.symm (selected, rest) i) j * x i)]
    simp_rw [hSelected, hRest]
    dsimp [center]
    simp only [Finset.attach_eq_univ]
    ring_nf
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr
    · ext i
      simp
    · intro i _
      rfl
  rw [← uniformProbability_reindex e.symm, uniformProbability_prod_fubini]
  calc
    _ ≤ finiteMean (fun _ : {i : Fin n // i ∉ I} → RowSlice n d =>
        Real.exp (-(I.card : ℝ) * d / 16)) := by
      apply finiteMean_mono
      intro rest
      have hBound := row_slice_selected_rows_rare_adjoint_decay (ι := I) hd hDegree
        (by simpa only [Fintype.card_coe] using hRare) hCost
        (fun i => x i.val) ht (fun i => hLarge i.val i.property) (center rest)
      apply (uniformProbability_mono ?_).trans (by simpa only [Fintype.card_coe] using hBound)
      intro selected hSmall
      rw [EuclideanSpace.norm_sq_eq] at hSmall
      simpa only [hCoord] using hSmall
    _ = _ := finiteMean_const _

theorem row_slice_ordered_rare_adjoint_decay {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hRankTail : rank ≤ tail)
    (hFit : tail + rank ≤ n) (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (y : Fin n → ℂ) (c ζ : ℂ) {t : ℝ} (ht : 0 < t)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 * t + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => y i + c))‖ ^ 2 ≤
          t ^ 2 * (rank : ℝ) * d / 72) ≤ Real.exp (-(rank : ℝ) * d / 16) := by
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
  have hBound := row_slice_full_rare_adjoint_decay hd hDegree I
    (by simpa only [hCard] using hRare) hCost (WithLp.toLp 2 (fun i => y i + c)) ht hLarge ζ
  simpa only [hCard] using hBound

end CircularLaw
