import CircularLaw.WitnessCountTail

/-!
# A unique-coordinate witness forces a nonzero shifted row action

The estimate keeps the exact degree and constant shift. The row index is
outside the forbidden coordinate set, just as in the Section 4 witnesses.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem unique_witness_action_lower {n d : ℕ} (S : RowSlice n d)
    (J : Finset (Fin n)) (j i : Fin n)
    (hUnique : S.val ∩ J = {j}) (hiJ : i ∉ J)
    (x : Fin n → ℂ) (c ζ : ℂ) {b : ℝ}
    (hTail : ∀ k : Fin n, k ∉ J → ‖x k‖ ≤ b) :
    ‖x j‖ - (((d : ℝ) - 1 + ‖ζ‖) * b + ((d : ℝ) + ‖ζ‖) * ‖c‖) ≤
      ‖shiftedRowAction S x c ζ i‖ := by
  have hjS : j ∈ S.val := by
    have h : j ∈ S.val ∩ J := by rw [hUnique]; simp
    exact (Finset.mem_inter.mp h).1
  have hOther : ∀ k ∈ S.val.erase j, k ∉ J := by
    intro k hk hkJ
    have hInter : k ∈ S.val ∩ J :=
      Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hk).2, hkJ⟩
    rw [hUnique] at hInter
    exact (Finset.mem_erase.mp hk).1 (Finset.mem_singleton.mp hInter)
  have hSum : ‖∑ k ∈ S.val.erase j, x k‖ ≤ ((d : ℝ) - 1) * b := by
    calc
      _ ≤ ∑ k ∈ S.val.erase j, ‖x k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ S.val.erase j, b :=
        Finset.sum_le_sum (fun k hk => hTail k (hOther k hk))
      _ = _ := by
        have hDegree : 1 ≤ d := by
          rw [← S.property]
          exact Finset.card_pos.mpr ⟨j, hjS⟩
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hjS, S.property,
          Nat.cast_sub hDegree, Nat.cast_one]
  have hRest : ‖(∑ k ∈ S.val.erase j, x k) + (d : ℂ) * c - ζ * (x i + c)‖ ≤
      ((d : ℝ) - 1 + ‖ζ‖) * b + ((d : ℝ) + ‖ζ‖) * ‖c‖ := by
    calc
      _ ≤ ‖(∑ k ∈ S.val.erase j, x k) + (d : ℂ) * c‖ + ‖ζ * (x i + c)‖ :=
        norm_sub_le _ _
      _ ≤ (‖∑ k ∈ S.val.erase j, x k‖ + ‖(d : ℂ) * c‖) + ‖ζ * (x i + c)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ (((d : ℝ) - 1) * b + (d : ℝ) * ‖c‖) + ‖ζ‖ * (b + ‖c‖) := by
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        apply add_le_add
        · exact add_le_add hSum (le_refl _)
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg ζ)
          exact (norm_add_le _ _).trans (add_le_add (hTail i hiJ) (le_refl _))
      _ = _ := by ring
  have hAction : shiftedRowAction S x c ζ i =
      x j + ((∑ k ∈ S.val.erase j, x k) + (d : ℂ) * c - ζ * (x i + c)) := by
    rw [shiftedRowAction, rowLinearForm_add_const, rowLinearForm_eq_support_sum,
      ← Finset.add_sum_erase _ _ hjS]
    abel
  rw [hAction]
  have hNorm := norm_add_le (x j + ((∑ k ∈ S.val.erase j, x k) +
    (d : ℂ) * c - ζ * (x i + c)))
      (-((∑ k ∈ S.val.erase j, x k) + (d : ℂ) * c - ζ * (x i + c)))
  simp only [add_neg_cancel_right, norm_neg] at hNorm
  linarith

theorem unique_witness_action_seven_tenths {n d : ℕ} (S : RowSlice n d)
    (J : Finset (Fin n)) (j i : Fin n)
    (hUnique : S.val ∩ J = {j}) (hiJ : i ∉ J)
    (x : Fin n → ℂ) (c ζ : ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hTail : ∀ k : Fin n, k ∉ J → ‖x k‖ ≤ b) (hTop : a ≤ ‖x j‖)
    (hJump : 4 * (d : ℝ) * b < a) (hCenter : ‖c‖ ≤ b / 10)
    (hSpectral : ‖ζ‖ ≤ (d : ℝ) / 20) :
    (7 / 10 : ℝ) * a ≤ ‖shiftedRowAction S x c ζ i‖ ∧
      0 < ‖shiftedRowAction S x c ζ i‖ := by
  have hLower := unique_witness_action_lower S J j i hUnique hiJ x c ζ hTail
  have hCost : ((d : ℝ) - 1 + ‖ζ‖) * b + ((d : ℝ) + ‖ζ‖) * ‖c‖ ≤
      (6 / 5 : ℝ) * d * b := by
    have hCenterScaled := mul_le_mul_of_nonneg_left hCenter
      (add_nonneg (Nat.cast_nonneg d) (norm_nonneg ζ))
    have hSpectralScaled := mul_le_mul_of_nonneg_right hSpectral hb
    nlinarith
  have hPositive : 0 < a := lt_of_le_of_lt (by positivity) hJump
  have hResult : (7 / 10 : ℝ) * a ≤ ‖shiftedRowAction S x c ζ i‖ := by nlinarith
  exact ⟨hResult, lt_of_lt_of_le (mul_pos (by norm_num) hPositive) hResult⟩

end CircularLaw
