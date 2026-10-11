import CircularLaw.RowNegativeSecondMoment
import Mathlib.Order.Interval.Finset.Fin

/-!
# Counting inverse singular-value moments

For a decreasing positive list, every tail term contributes at least
the inverse square of its first term. Combined with the checked negative
second moment, this gives the manuscript's surviving-matrix lower bound.
Lean indices here start at zero: index `j` is manuscript singular value
`s_(j+1)` and the tail has exactly `k-j` entries.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators

namespace CircularLaw

theorem antitone_inverse_square_tail {k : ℕ} (s : Fin k → ℝ)
    (hs : Antitone s) (hPos : ∀ i, 0 < s i) (j : Fin k) :
    (k - j.val : ℕ) / (s j ^ 2 : ℝ) ≤ ∑ i, (s i ^ 2)⁻¹ := by
  calc
    _ = ∑ _i ∈ Finset.Ici j, (s j ^ 2)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ici, div_eq_mul_inv]
    _ ≤ ∑ i ∈ Finset.Ici j, (s i ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hSq : s i ^ 2 ≤ s j ^ 2 := pow_le_pow_left₀ (hPos i).le (hs (Finset.mem_Ici.mp hi)) 2
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos (hPos i)) hSq
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)

theorem antitone_inverse_moment_square_bound {k : ℕ} (s : Fin k → ℝ)
    (hs : Antitone s) (hPos : ∀ i, 0 < s i) {r : ℝ} (hr : 0 < r)
    (hMoment : (∑ i, (s i ^ 2)⁻¹) ≤ (k : ℝ) / r ^ 2) (j : Fin k) :
    r ^ 2 * ((k - j.val : ℕ) : ℝ) / k ≤ s j ^ 2 := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (antitone_inverse_square_tail s hs hPos j).trans hMoment
  have hCross := (div_le_div_iff₀ (sq_pos_of_pos (hPos j)) (sq_pos_of_pos hr)).mp h
  apply (div_le_iff₀ hkR).mpr
  nlinarith

theorem antitone_inverse_moment_sqrt_bound {k : ℕ} (s : Fin k → ℝ)
    (hs : Antitone s) (hPos : ∀ i, 0 < s i) {r : ℝ} (hr : 0 < r)
    (hMoment : (∑ i, (s i ^ 2)⁻¹) ≤ (k : ℝ) / r ^ 2) (j : Fin k) :
    r * Real.sqrt (((k - j.val : ℕ) : ℝ) / k) ≤ s j := by
  have hSquare := antitone_inverse_moment_square_bound s hs hPos hr hMoment j
  have hRatio : (0 : ℝ) ≤ ((k - j.val : ℕ) : ℝ) / k := by positivity
  have hLeft : (r * Real.sqrt (((k - j.val : ℕ) : ℝ) / k)) ^ 2 =
      r ^ 2 * ((k - j.val : ℕ) : ℝ) / k := by
    rw [mul_pow, Real.sq_sqrt hRatio]
    ring
  have hSq : (r * Real.sqrt (((k - j.val : ℕ) : ℝ) / k)) ^ 2 ≤ s j ^ 2 := by
    rw [hLeft]
    exact hSquare
  nlinarith [Real.sqrt_nonneg (((k - j.val : ℕ) : ℝ) / k), hPos j]

theorem antitone_inverse_moment_degree_bound {k d : ℕ} (s : Fin k → ℝ)
    (hs : Antitone s) (hPos : ∀ i, 0 < s i) {r : ℝ} (hr : 0 < r)
    (hMoment : (∑ i, (s i ^ 2)⁻¹) ≤ (k : ℝ) / r ^ 2) (j : Fin k) (hd : 0 < d)
    (hTail : k ≤ (k - j.val) * d ^ 2) : r / d ≤ s j := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hTailR : (k : ℝ) ≤ ((k - j.val : ℕ) : ℝ) * (d : ℝ) ^ 2 := by exact_mod_cast hTail
  have hSquare := antitone_inverse_moment_square_bound s hs hPos hr hMoment j
  have hCross : r ^ 2 * ((k - j.val : ℕ) : ℝ) ≤ s j ^ 2 * k :=
    (div_le_iff₀ hkR).mp hSquare
  have hProduct := mul_le_mul_of_nonneg_left hTailR (sq_nonneg r)
  have hProduct2 := mul_le_mul_of_nonneg_right hCross (sq_nonneg (d : ℝ))
  have hFinal : r ^ 2 ≤ s j ^ 2 * (d : ℝ) ^ 2 := by nlinarith
  apply (div_le_iff₀ hdR).mpr
  apply (sq_le_sq₀ hr.le (mul_pos (hPos j) hdR).le).mp
  simpa only [mul_pow] using hFinal

theorem surviving_rows_singular_value_sqrt_bound {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i)
    (j : Fin (Fintype.card H)) :
    r * Real.sqrt (((Fintype.card H - j.val : ℕ) : ℝ) / H.card) ≤
      retainedRowSingularValues H ζ rows j := by
  simpa only [Fintype.card_coe] using
    antitone_inverse_moment_sqrt_bound (retainedRowSingularValues H ζ rows)
      (retainedRowSingularValues_antitone H ζ rows)
      (fun j => retainedRowSingularValues_pos_of_distances H ζ rows (fun i hi => hr.trans_le (hDistance i hi)) j)
      hr (by simpa only [Fintype.card_coe] using surviving_rows_negative_second_moment_bound H ζ rows hr hDistance) j

theorem surviving_rows_singular_value_degree_bound {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) {r : ℝ} (hr : 0 < r)
    (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i)
    (j : Fin (Fintype.card H)) (hd : 0 < d)
    (hTail : Fintype.card H ≤ (Fintype.card H - j.val) * d ^ 2) :
    r / d ≤ retainedRowSingularValues H ζ rows j := by
  apply antitone_inverse_moment_degree_bound (retainedRowSingularValues H ζ rows)
    (retainedRowSingularValues_antitone H ζ rows)
    (fun j => retainedRowSingularValues_pos_of_distances H ζ rows (fun i hi => hr.trans_le (hDistance i hi)) j)
    hr _ j hd hTail
  simpa only [Fintype.card_coe] using surviving_rows_negative_second_moment_bound H ζ rows hr hDistance

end CircularLaw
