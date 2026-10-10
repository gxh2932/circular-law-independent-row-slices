import CircularLaw.SquareSingularSecondMoment
import CircularLaw.EmpiricalPrefixMeans
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Positive logarithmic tails from the actual matrix energy

The finite concavity estimate applies before degree normalization, where
the matrix energy can grow like n*d. It retains the exact integer prefix
length and also covers an empty prefix.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem positive_log_le_half_log_one_add_sq {s : ℝ} (hs : 0 ≤ s) :
    max (Real.log s) 0 ≤ (1 / 2 : ℝ) * Real.log (1 + s ^ 2) := by
  have hNonneg : 0 ≤ Real.log (1 + s ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg s])
  by_cases hOne : s ≤ 1
  · rw [max_eq_right (Real.log_nonpos hs hOne)]
    positivity
  · have hsPos : 0 < s := by linarith
    have hLog := Real.log_le_log (sq_pos_of_pos hsPos) (by linarith : s ^ 2 ≤ 1 + s ^ 2)
    rw [Real.log_pow] at hLog
    norm_num only [Nat.cast_ofNat] at hLog
    rw [max_eq_left (Real.log_nonneg (by linarith : 1 ≤ s))]
    linarith

theorem finite_positive_log_energy_bound {r : ℕ} (s : Fin r → ℝ)
    (hs : ∀ j, 0 ≤ s j) :
    (∑ j, max (Real.log (s j)) 0) ≤
      (r : ℝ) / 2 * Real.log (1 + (∑ j, s j ^ 2) / r) := by
  by_cases hr : r = 0
  · subst r
    simp
  have hrPos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hJ := ConcaveOn.le_map_sum (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi)
    (t := Finset.univ) (w := fun _ : Fin r => (r : ℝ)⁻¹)
    (p := fun j => 1 + s j ^ 2)
    (fun _ _ => inv_nonneg.mpr hrPos.le)
    (by simp [hr]) (fun j _ => by change 0 < 1 + s j ^ 2; positivity)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have hAverage : (r : ℝ)⁻¹ * (∑ j : Fin r, (1 + s j ^ 2)) =
      1 + (∑ j, s j ^ 2) / r := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  rw [hAverage] at hJ
  have hSum : (∑ j, Real.log (1 + s j ^ 2)) ≤
      (r : ℝ) * Real.log (1 + (∑ j, s j ^ 2) / r) := by
    have h := mul_le_mul_of_nonneg_left hJ hrPos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hrPos.ne', one_mul] using h
  calc
    _ ≤ ∑ j, (1 / 2 : ℝ) * Real.log (1 + s j ^ 2) :=
      Finset.sum_le_sum (fun j _ => positive_log_le_half_log_one_add_sq (hs j))
    _ = (1 / 2 : ℝ) * ∑ j, Real.log (1 + s j ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) * ((r : ℝ) * Real.log (1 + (∑ j, s j ^ 2) / r)) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by ring

theorem square_positive_log_prefix_energy_bound {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hrn : r ≤ n) :
    (∑ j : Fin r, max (Real.log (orderedSquareSingularValues A (Fin.castLE hrn j))) 0) / n ≤
      ((r : ℝ) / (2 * n)) * Real.log (1 + squareMatrixEnergy A / r) := by
  have hPrefix : (∑ j : Fin r, orderedSquareSingularValues A (Fin.castLE hrn j) ^ 2) ≤
      squareMatrixEnergy A := by
    rw [← retainedPrefixIndices_sum hrn (fun j => orderedSquareSingularValues A j ^ 2),
      ← square_singular_values_sum_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => sq_nonneg _)
  have hLog := Real.log_le_log (by positivity :
      0 < 1 + (∑ j : Fin r, orderedSquareSingularValues A (Fin.castLE hrn j) ^ 2) / r)
    (add_le_add_right (div_le_div_of_nonneg_right hPrefix (Nat.cast_nonneg r)) 1)
  have hFinite := finite_positive_log_energy_bound
    (fun j : Fin r => orderedSquareSingularValues A (Fin.castLE hrn j))
    (fun j => orderedSquareSingularValues_nonneg A (Fin.castLE hrn j))
  calc
    _ ≤ ((r : ℝ) / 2 * Real.log
      (1 + (∑ j : Fin r, orderedSquareSingularValues A (Fin.castLE hrn j) ^ 2) / r)) / n :=
      div_le_div_of_nonneg_right hFinite (Nat.cast_nonneg n)
    _ ≤ ((r : ℝ) / 2 * Real.log (1 + squareMatrixEnergy A / r)) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLog (by positivity)) (Nat.cast_nonneg n)
    _ = _ := by ring

end CircularLaw
