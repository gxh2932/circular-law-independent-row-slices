import CircularLaw.MiroshnikovStep

/-!
# Miroshnikov's finite-sum cube estimate

Strong induction on the number of summands closes the localized removal
recurrence. Every measure is an actual probability law; the estimate is
uniform over arbitrary finite nonempty families.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

universe u

theorem cube_sum_miroshnikov {ι : Type u} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (hm : 1 ≤ Fintype.card ι) {r α : ℝ} (hr : 0 < r) (hα : α < 1 / 2)
    (hBound : ∀ i, cubeConcentration (μ i) r ≤ α) :
    cubeConcentration (productSumLaw μ) r ≤
      miroshnikovConstant * α / Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  have hStrong : ∀ m : ℕ, ∀ (κ : Type u) [Fintype κ],
      ∀ (ν : κ → Measure ℂ) [∀ i, IsProbabilityMeasure (ν i)],
      Fintype.card κ = m → 1 ≤ m →
      (∀ i, cubeConcentration (ν i) r ≤ α) →
      cubeConcentration (productSumLaw ν) r ≤
        miroshnikovConstant * α / Real.sqrt (m : ℝ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro κ _ ν _ hCard hm hBounds
      haveI : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
      let q₀ : κ := Classical.arbitrary κ
      have hαNonneg : 0 ≤ α := (cubeConcentration_nonneg (ν q₀) r).trans (hBounds q₀)
      have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hRootPos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmPos
      by_cases hSmall : m ≤ 2
      · have hRoot : Real.sqrt (m : ℝ) ≤ miroshnikovConstant := by
          have hmReal : (m : ℝ) ≤ 2 := by exact_mod_cast hSmall
          exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩ : Real.sqrt (m : ℝ) ≤ 2).trans
            miroshnikovConstant_ge_two
        exact (cubeConcentration_sum_le_summand ν q₀ r).trans
          ((hBounds q₀).trans ((le_div_iff₀ hRootPos).mpr (by
            have h := mul_le_mul_of_nonneg_right hRoot hαNonneg
            nlinarith)))
      · have hmThree : 3 ≤ m := by omega
        obtain ⟨q, hStep⟩ := miroshnikov_cube_removal_step ν (by omega) hr hα hBounds
        have hSubCard := card_remove_one q
        have hSubLt : Fintype.card {i : κ // i ≠ q} < m := by omega
        have hSubPos : 1 ≤ Fintype.card {i : κ // i ≠ q} := by omega
        have hInd := ih _ hSubLt {i : κ // i ≠ q}
          (fun i : {i : κ // i ≠ q} => ν i.val) rfl hSubPos (fun i => hBounds i.val)
        rw [hSubCard, hCard] at hInd
        rw [hCard] at hStep
        have hPredPos : (0 : ℝ) < (m - 1 : ℕ) := by
          exact_mod_cast (show 0 < m - 1 by omega)
        have hPredRootPos : 0 < Real.sqrt (m - 1 : ℕ) := Real.sqrt_pos.mpr hPredPos
        have hCoefficient : miroshnikovStepConstant + miroshnikovConstant / 2 ≤
            (3 / 4) * miroshnikovConstant := by
          unfold miroshnikovConstant
          linarith
        have hNumerator := mul_le_mul_of_nonneg_right hCoefficient hαNonneg
        have hDiv := div_le_div_of_nonneg_right hNumerator hPredRootPos.le
        have hFirst : cubeConcentration (productSumLaw ν) r ≤
            (3 / 4) * (miroshnikovConstant * α) / Real.sqrt (m - 1 : ℕ) := by
          calc
            _ ≤ miroshnikovStepConstant * α / Real.sqrt (m - 1 : ℕ) +
                (1 / 2) * (miroshnikovConstant * α / Real.sqrt (m - 1 : ℕ)) :=
              hStep.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hInd (by norm_num)))
            _ = (miroshnikovStepConstant + miroshnikovConstant / 2) * α /
                Real.sqrt (m - 1 : ℕ) := by ring
            _ ≤ _ := by convert hDiv using 1; ring
        apply hFirst.trans
        apply (div_le_div_iff₀ hPredRootPos hRootPos).mpr
        have hNumeratorNonneg : 0 ≤ miroshnikovConstant * α :=
          mul_nonneg (by linarith [miroshnikovConstant_ge_two]) hαNonneg
        have h := mul_le_mul_of_nonneg_left (sqrt_predecessor_three_quarters hmThree)
          hNumeratorNonneg
        convert h using 1
        ring
  exact hStrong (Fintype.card ι) ι μ rfl hm hBound

end CircularLaw
