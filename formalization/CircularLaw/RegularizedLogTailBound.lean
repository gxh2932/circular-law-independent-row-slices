import CircularLaw.RegularizedRowLogRemoval
import CircularLaw.EmpiricalLogGeometry

/-!
# Removing row regularization using the actual negative logarithmic tail

A positive reference value below each row singular value controls its
regularization error. This applies to every injected subset of an
ambient singular array, without a common smallest-value threshold.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators NNReal

namespace CircularLaw

theorem regularized_scalar_log_error_tail_bound {s η T : ℝ} (hs : 0 < s)
    (hη : 0 ≤ η) (hT : 1 ≤ T) (hScale : η ≤ Real.exp (-T))
    (t : ℝ≥0) (ht : 0 < t) (hLower : (t : ℝ) ≤ s) :
    0 ≤ (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) - Real.log s ∧
      (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) - Real.log s ≤
        η ^ 2 / (2 * Real.exp (-T) ^ 2) +
          2 * (if T < hermitizationNegativeLog t then hermitizationNegativeLog t else 0) := by
  have hTail : 0 ≤ if T < hermitizationNegativeLog t then hermitizationNegativeLog t else 0 := by
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hConstant : 0 ≤ η ^ 2 / (2 * Real.exp (-T) ^ 2) := by positivity
  refine ⟨(regularized_scalar_log_error_bounds hs le_rfl η).1, ?_⟩
  by_cases hLarge : Real.exp (-T) ≤ s
  · have h := (regularized_scalar_log_error_bounds (Real.exp_pos (-T)) hLarge η).2
    linarith only [h, hTail]
  · have hSmall := lt_of_not_ge hLarge
    have hFloorOne : Real.exp (-T) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith only [hT] : -T ≤ 0)
    have hsOne := hSmall.le.trans hFloorOne
    have hηOne := hScale.trans hFloorOne
    have hSum : η ^ 2 + s ^ 2 ≤ 2 := by nlinarith only [hη, hηOne, hs, hsOne]
    have hLog := Real.log_le_sub_one_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg η) (sq_pos_of_pos hs))
    have hHalf : (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) ≤ 1 := by
      linarith only [hLog, hSum]
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hLogSmall := Real.log_lt_log htR (hLower.trans_lt hSmall)
    rw [Real.log_exp] at hLogSmall
    have hLogOrder := Real.log_le_log htR hLower
    have hNeg : 0 ≤ -Real.log (t : ℝ) := by linarith only [hT, hLogSmall]
    have hTailEq : hermitizationNegativeLog t = -Real.log (t : ℝ) := by
      exact max_eq_left hNeg
    have hTailLarge : T < hermitizationNegativeLog t := by rw [hTailEq]; linarith only [hLogSmall]
    rw [if_pos hTailLarge, hTailEq]
    nlinarith only [hHalf, hLogOrder, hLogSmall, hT, hConstant]

theorem injected_negative_log_tail_sum_bound {m n : ℕ} (e : Fin m ↪ Fin n)
    (s : Fin n → ℝ≥0) (T : ℝ) :
    (∑ j : Fin m, if T < hermitizationNegativeLog (s (e j)) then
      hermitizationNegativeLog (s (e j)) else 0) ≤
      ∑ j : Fin n, if T < hermitizationNegativeLog (s j) then hermitizationNegativeLog (s j) else 0 := by
  let g : Fin n → ℝ := fun j => if T < hermitizationNegativeLog (s j) then hermitizationNegativeLog (s j) else 0
  have hNonneg (j : Fin n) : 0 ≤ g j := by
    dsimp [g]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  change (∑ j : Fin m, g (e j)) ≤ ∑ j : Fin n, g j
  calc
    _ = ∑ j ∈ Finset.univ.image e, g j :=
      (Finset.sum_image (fun i _ j _ h => e.injective h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hNonneg j)

theorem regularized_row_log_removal_reference_tail {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (A : Matrix ι κ ℂ) (e : Fin (Fintype.card ι) ↪ Fin n) (hn : 0 < n)
    (s : Fin n → ℝ≥0) (hPositive : ∀ j, 0 < s j)
    (hLower : ∀ j, (s (e j) : ℝ) ≤ orderedMatrixSingularValues A j)
    {η T : ℝ} (hη : 0 < η) (hT : 1 ≤ T) (hScale : η ≤ Real.exp (-T)) :
    0 ≤ (regularizedRowPotential A η - matrixRowLogVolume A) / n ∧
      (regularizedRowPotential A η - matrixRowLogVolume A) / n ≤
        η ^ 2 / (2 * Real.exp (-T) ^ 2) + 2 * empiricalNegativeLogTail s T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hScalar (j : Fin (Fintype.card ι)) := regularized_scalar_log_error_tail_bound
    ((by exact_mod_cast hPositive (e j) : (0 : ℝ) < s (e j)).trans_le (hLower j))
    hη.le hT hScale (s (e j)) (hPositive (e j)) (hLower j)
  rw [regularized_row_potential_eq_singular_log_sum A hη, matrixRowLogVolume, ← Finset.sum_sub_distrib]
  refine ⟨div_nonneg (Finset.sum_nonneg (fun j _ => (hScalar j).1)) hnR.le, ?_⟩
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hScalar j).2)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hSum
  have hTail := mul_le_mul_of_nonneg_left (injected_negative_log_tail_sum_bound e s T)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hCardN : (Fintype.card ι : ℝ) ≤ n := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective)
  have hCard := mul_le_mul_of_nonneg_right hCardN
    (by positivity : 0 ≤ η ^ 2 / (2 * Real.exp (-T) ^ 2))
  have hBound : (∑ j : Fin (Fintype.card ι),
      ((1 / 2 : ℝ) * Real.log (η ^ 2 + orderedMatrixSingularValues A j ^ 2) -
        Real.log (orderedMatrixSingularValues A j))) ≤
      (n : ℝ) * (η ^ 2 / (2 * Real.exp (-T) ^ 2)) +
        2 * (∑ j : Fin n, if T < hermitizationNegativeLog (s j) then hermitizationNegativeLog (s j) else 0) := by
    linarith only [hSum, hTail, hCard]
  apply (div_le_div_of_nonneg_right hBound hnR.le).trans_eq
  unfold empiricalNegativeLogTail empiricalNonnegativeMean finiteMean
  simp only [Fintype.card_fin]
  field_simp

end CircularLaw
