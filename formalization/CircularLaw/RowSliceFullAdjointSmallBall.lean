import CircularLaw.RowSliceSelectedAdjointSmallBall
import CircularLaw.LLYColumnAction
import CircularLaw.FiniteProductFibers

/-!
# Selected-row small balls for the actual full shifted adjoint

Fixing all other rows turns their contribution into a deterministic
center. Thus only the selected large coefficients pay conditioning loss.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators

namespace CircularLaw

theorem shifted_slice_adjoint_apply_eq_full_sum {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    (fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j =
      (∑ i, rowEntry (rows i) j * x i) - star ζ * x j := by
  rw [shifted_slice_adjoint_apply_eq_column_sum]
  simp [rowSliceColumnSupport, rowEntry, Finset.sum_filter]

theorem row_slice_full_adjoint_small_ball {n d : ℕ} (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (I : Finset (Fin n)) (hI : I.Nonempty) (x : EuclideanSpace ℂ (Fin n))
    {t τ : ℝ} (ht : 0 < t) (hLarge : ∀ i ∈ I, t ≤ ‖x i‖) (hτ : 1 ≤ τ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ^ 2 ≤ τ ^ 2 * t ^ 2 * n) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ I.card *
        (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((I.card : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ n := by
  haveI : Nonempty (RowSlice n d) := rowSlice_nonempty (by omega)
  haveI : Nonempty I := by obtain ⟨i, hi⟩ := hI; exact ⟨⟨i, hi⟩⟩
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ I) (fun _ => RowSlice n d)
  let center := fun rest : {i : Fin n // i ∉ I} → RowSlice n d => fun j : Fin n =>
    star ζ * x j - ∑ i : {i : Fin n // i ∉ I}, rowEntry (rest i) j * x i.val
  have hCoord (selected : I → RowSlice n d) (rest : {i : Fin n // i ∉ I} → RowSlice n d) (j : Fin n) :
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
        (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ I.card *
          (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((I.card : ℝ) * ((d : ℝ) / n))) * τ ^ 2) ^ n) := by
      apply finiteMean_mono
      intro rest
      have hBound := row_slice_selected_rows_adjoint_small_ball (ι := I) hd hDegree
        (fun i => x i.val) Finset.univ Finset.univ_nonempty ht
        (fun i _ => hLarge i.val i.property) hτ (center rest)
      apply (uniformProbability_mono ?_).trans (by simpa only [Finset.card_univ, Fintype.card_coe] using hBound)
      intro selected hSmall
      rw [EuclideanSpace.norm_sq_eq] at hSmall
      simpa only [hCoord] using hSmall
    _ = _ := finiteMean_const _

end CircularLaw
