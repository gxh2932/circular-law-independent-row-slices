import CircularLaw.AlmostConstantRowAction

/-!
# Almost-constant action on a support of variable cardinality

Column supports need not have exactly d entries. This estimate keeps
their actual close-coordinate count and the sum of the bad moduli.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem support_constant_center_decomposition {n : ℕ} (S F : Finset (Fin n))
    (x : Fin n → ℂ) (c : ℂ) :
    (∑ j ∈ S, x j) = ((S ∩ F).card : ℂ) * c +
      (∑ j ∈ S ∩ F, (x j - c)) + ∑ j ∈ S \ F, x j := by
  have hInter : (∑ j ∈ S ∩ F, x j) =
      ((S ∩ F).card : ℂ) * c + ∑ j ∈ S ∩ F, (x j - c) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hSum := Finset.sum_union (f := x) (Finset.disjoint_sdiff_inter S F)
  rw [Finset.sdiff_union_inter] at hSum
  calc
    _ = (∑ j ∈ S \ F, x j) + ∑ j ∈ S ∩ F, x j := hSum
    _ = _ := by rw [hInter]; ring

theorem support_shifted_almost_constant_lower {n : ℕ} (S F : Finset (Fin n))
    (x : Fin n → ℂ) (c ζ : ℂ) (i : Fin n) :
    ((S ∩ F).card : ℝ) * ‖c‖ - (∑ j ∈ S ∩ F, ‖x j - c‖) -
      (∑ j ∈ S \ F, ‖x j‖) - ‖ζ‖ * ‖x i‖ ≤ ‖(∑ j ∈ S, x j) - ζ * x i‖ := by
  have hDecomp := support_constant_center_decomposition S F x c
  have hIdentity : (((∑ j ∈ S, x j) - ζ * x i) + ζ * x i -
      (∑ j ∈ S ∩ F, (x j - c))) - (∑ j ∈ S \ F, x j) = ((S ∩ F).card : ℂ) * c := by
    rw [hDecomp]
    ring
  have hTriangle : ((S ∩ F).card : ℝ) * ‖c‖ ≤
      ‖(∑ j ∈ S, x j) - ζ * x i‖ + ‖ζ‖ * ‖x i‖ +
        (∑ j ∈ S ∩ F, ‖x j - c‖) + (∑ j ∈ S \ F, ‖x j‖) := by
    calc
      _ = ‖((S ∩ F).card : ℂ) * c‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖(((∑ j ∈ S, x j) - ζ * x i) + ζ * x i -
          (∑ j ∈ S ∩ F, (x j - c))) - (∑ j ∈ S \ F, x j)‖ := congrArg norm hIdentity.symm
      _ ≤ ‖((∑ j ∈ S, x j) - ζ * x i) + ζ * x i -
          (∑ j ∈ S ∩ F, (x j - c))‖ + ‖∑ j ∈ S \ F, x j‖ := norm_sub_le _ _
      _ ≤ (‖((∑ j ∈ S, x j) - ζ * x i) + ζ * x i‖ +
          ‖∑ j ∈ S ∩ F, (x j - c)‖) + ‖∑ j ∈ S \ F, x j‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (‖(∑ j ∈ S, x j) - ζ * x i‖ + ‖ζ * x i‖ +
          (∑ j ∈ S ∩ F, ‖x j - c‖)) + ∑ j ∈ S \ F, ‖x j‖ := by
        exact add_le_add (add_le_add (norm_add_le _ _) (norm_sum_le _ _)) (norm_sum_le _ _)
      _ = _ := by rw [norm_mul]
  linarith only [hTriangle]

theorem support_almost_constant_fifth_lower {n d : ℕ} (S F : Finset (Fin n))
    (x : Fin n → ℂ) (c ζ : ℂ) (i : Fin n)
    (hClose : ∀ j ∈ S ∩ F, ‖x j - c‖ ≤ ‖c‖ / 4)
    (hCount : 4 * (d : ℝ) / 5 ≤ (S ∩ F).card)
    (hBad : (∑ j ∈ S \ F, ‖x j‖) ≤ (d : ℝ) / 5 * ‖c‖)
    (hIndex : ‖x i‖ ≤ 5 / 4 * ‖c‖) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    (d : ℝ) / 5 * ‖c‖ ≤ ‖(∑ j ∈ S, x j) - ζ * x i‖ := by
  have hLower := support_shifted_almost_constant_lower S F x c ζ i
  have hError : (∑ j ∈ S ∩ F, ‖x j - c‖) ≤ ((S ∩ F).card : ℝ) * (‖c‖ / 4) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hClose
  have hCountC := mul_le_mul_of_nonneg_right hCount (norm_nonneg c)
  have hShiftC : ‖ζ‖ * ‖x i‖ ≤ (d : ℝ) / 5 * ‖c‖ := by
    calc
      _ ≤ (4 * (d : ℝ) / 25) * (5 / 4 * ‖c‖) :=
        mul_le_mul hShift hIndex (norm_nonneg _) (by positivity)
      _ = _ := by ring
  nlinarith only [hLower, hError, hCountC, hBad, hShiftC]

end CircularLaw
