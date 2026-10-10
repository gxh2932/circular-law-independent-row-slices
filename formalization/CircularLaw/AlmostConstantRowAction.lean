import CircularLaw.AlmostConstantGeometry
import CircularLaw.EqualBlock

/-!
# Row action near a constant vector

The estimate applies to the actual fixed-size support. Close coordinates
give a small centered error, and the remaining selected coordinates are
controlled by their load. The source parameters give the literal `d/2`
lower bound, including the diagonal spectral shift.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem centered_row_error_bound {n d : ℕ} (S : RowSlice n d) (F : Finset (Fin n))
    (x : Fin n → ℂ) (c : ℂ) {θ B M : ℝ} (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hClose : ∀ j ∈ S.val ∩ F, ‖x j - c‖ ≤ θ * B)
    (hFar : ∀ j ∈ S.val \ F, ‖x j - c‖ ≤ M * B) :
    ‖rowLinearForm S (fun j => x j - c)‖ ≤
      (d : ℝ) * θ * B + ((S.val \ F).card : ℝ) * M * B := by
  have hCard : ((S.val ∩ F).card : ℝ) ≤ d := by
    exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left : S.val ∩ F ⊆ S.val)).trans_eq
      S.property
  rw [rowLinearForm_eq_support_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ = (∑ j ∈ S.val \ F, ‖x j - c‖) + ∑ j ∈ S.val ∩ F, ‖x j - c‖ := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S.val F), Finset.sdiff_union_inter]
    _ ≤ (∑ _j ∈ S.val \ F, M * B) + ∑ _j ∈ S.val ∩ F, θ * B :=
      add_le_add (Finset.sum_le_sum hFar) (Finset.sum_le_sum hClose)
    _ = ((S.val \ F).card : ℝ) * (M * B) + ((S.val ∩ F).card : ℝ) * (θ * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((S.val \ F).card : ℝ) * (M * B) + (d : ℝ) * (θ * B) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hCard (mul_nonneg hθ hB))
    _ = _ := by ring

theorem centered_shifted_row_lower {n d : ℕ} (S : RowSlice n d) (x : Fin n → ℂ)
    (c ζ : ℂ) (i : Fin n) {E B : ℝ}
    (hError : ‖rowLinearForm S (fun j => x j - c)‖ ≤ E) (hIndex : ‖x i‖ ≤ B) :
    (d : ℝ) * ‖c‖ - E - ‖ζ‖ * B ≤ ‖rowLinearForm S x - ζ * x i‖ := by
  have hCenter : rowLinearForm S x = rowLinearForm S (fun j => x j - c) + (d : ℂ) * c := by
    simpa only [sub_add_cancel] using rowLinearForm_add_const S (fun j => x j - c) c
  have hTriangle := norm_add_le ((d : ℂ) * c - ζ * x i +
    rowLinearForm S (fun j => x j - c))
      (ζ * x i - rowLinearForm S (fun j => x j - c))
  have hCancel : ((d : ℂ) * c - ζ * x i + rowLinearForm S (fun j => x j - c)) +
      (ζ * x i - rowLinearForm S (fun j => x j - c)) = (d : ℂ) * c := by ring
  rw [hCancel, norm_mul, Complex.norm_natCast] at hTriangle
  have hRest := norm_sub_le (ζ * x i) (rowLinearForm S (fun j => x j - c))
  rw [norm_mul] at hRest
  have hDiagonal := mul_le_mul_of_nonneg_left hIndex (norm_nonneg ζ)
  have hMain : (d : ℂ) * c - ζ * x i + rowLinearForm S (fun j => x j - c) =
      rowLinearForm S x - ζ * x i := by rw [hCenter]; ring
  rw [hMain] at hTriangle
  linarith

theorem source_almost_constant_row_lower {n d k : ℕ} (hn : 0 < n)
    (S : RowSlice n d) (F : Finset (Fin n)) (x : Fin n → ℂ) (c ζ : ℂ) (i : Fin n)
    {θ B : ℝ} (hθ : 0 ≤ θ) (hθSmall : θ ≤ 1 / 100) (hB : 0 ≤ B)
    (hCenter : (1 - θ) * B ≤ ‖c‖) (hIndex : ‖x i‖ ≤ B)
    (hClose : ∀ j ∈ S.val ∩ F, ‖x j - c‖ ≤ θ * B)
    (hFar : ∀ j ∈ S.val \ F, ‖x j - c‖ ≤ (13 + θ) * B)
    (hBadLoad : ((S.val \ F).card : ℝ) ≤ 32 * (k : ℝ) * d / n)
    (hScale : (k : ℝ) ≤ (n : ℝ) / 1000) (hShift : ‖ζ‖ ≤ (d : ℝ) / 20) :
    (d : ℝ) / 2 * B ≤ ‖rowLinearForm S x - ζ * x i‖ := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hError := centered_row_error_bound S F x c hθ hB hClose hFar
  have hLower := centered_shifted_row_lower S x c ζ i hError hIndex
  have hLoad : ((S.val \ F).card : ℝ) ≤ (4 / 125 : ℝ) * d := by
    apply hBadLoad.trans
    apply (div_le_iff₀ hN).mpr
    have hScaleD := mul_le_mul_of_nonneg_right hScale hd
    nlinarith
  have hErrorLoad := mul_le_mul_of_nonneg_right hLoad (show (0 : ℝ) ≤ (13 + θ) * B by positivity)
  have hCenterD := mul_le_mul_of_nonneg_left hCenter hd
  have hShiftB := mul_le_mul_of_nonneg_right hShift hB
  have hThetaD := mul_le_mul_of_nonneg_left hθSmall hd
  have hThetaDB := mul_le_mul_of_nonneg_right hThetaD hB
  have hCoefficient : (d : ℝ) / 2 * B ≤
      (d : ℝ) * ((1 - θ) * B) - ((d : ℝ) * θ * B + (4 / 125 : ℝ) * d * (13 + θ) * B) -
        (d : ℝ) / 20 * B := by nlinarith [mul_nonneg hd hB]
  nlinarith

end CircularLaw
