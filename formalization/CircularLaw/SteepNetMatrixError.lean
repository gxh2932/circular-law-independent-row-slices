import CircularLaw.SteepNetCardinality
import CircularLaw.EqualBlock

/-!
# Actual shifted matrix error for the steep-class approximants

The support has exactly `d` coordinates in every row. Consequently a
coordinate error `eps` gives row error at most `(d+|zeta|)*eps` and an
L2 error at most that quantity times `sqrt(n)`. The source spectral
window and the checked grid resolution give `2*(1+Z0)*sqrt(n/d)`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem rowLinearForm_norm_le_uniform {n d : ℕ} (S : RowSlice n d)
    (v : Fin n → ℂ) {ε : ℝ} (hBound : ∀ j, ‖v j‖ ≤ ε) :
    ‖rowLinearForm S v‖ ≤ (d : ℝ) * ε := by
  rw [rowLinearForm_eq_support_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ S.val, ε := Finset.sum_le_sum (fun j _ => hBound j)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, S.property]

theorem retainedShiftedMatrix_coordinate_error {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (v : Fin n → ℂ) {ε : ℝ} (hBound : ∀ j, ‖v j‖ ≤ ε) (i : I) :
    ‖(retainedShiftedMatrix I ζ rows).mulVec v i‖ ≤ ((d : ℝ) + ‖ζ‖) * ε := by
  rw [retainedShiftedMatrix_mulVec]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  have hRow := rowLinearForm_norm_le_uniform (rows i.val) v hBound
  have hIndex := mul_le_mul_of_nonneg_left (hBound i.val) (norm_nonneg ζ)
  linarith

theorem euclidean_norm_le_uniform {ι : Type*} [Fintype ι]
    (v : ι → ℂ) {B : ℝ} (hB : 0 ≤ B) (hBound : ∀ i, ‖v i‖ ≤ B) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * B := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : ι, B ^ 2 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hBound i) 2)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem retainedShiftedMatrix_l2_error {n d : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (v : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hBound : ∀ j, ‖v j‖ ≤ ε) :
    ‖(WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec v) : EuclideanSpace ℂ I)‖ ≤
      Real.sqrt n * ((d : ℝ) + ‖ζ‖) * ε := by
  have hCard : (Fintype.card I : ℝ) ≤ n := by
    rw [Fintype.card_coe]
    exact_mod_cast (Finset.card_le_univ I).trans_eq (Fintype.card_fin n)
  have hFactor : 0 ≤ ((d : ℝ) + ‖ζ‖) * ε := by positivity
  apply (euclidean_norm_le_uniform _ hFactor
    (retainedShiftedMatrix_coordinate_error I ζ rows v hBound)).trans
  have hRoot := Real.sqrt_le_sqrt hCard
  convert mul_le_mul_of_nonneg_right hRoot hFactor using 1
  ring

theorem shifted_vector_net_coordinate_error {n : ℕ} (x u : Fin n → ℂ) (c w : ℂ)
    {δ : ℝ} (hX : ∀ j, ‖x j - u j‖ ≤ δ) (hC : ‖c - w‖ ≤ δ) :
    ∀ j, ‖(x j + c) - (u j + w)‖ ≤ 2 * δ := by
  intro j
  rw [show (x j + c) - (u j + w) = (x j - u j) + (c - w) by ring]
  exact (norm_add_le _ _).trans (by linarith [hX j])

theorem source_shifted_net_matrix_error {n d : ℕ} (hd : 0 < d)
    {Z₀ : ℝ} (hZ : 0 ≤ Z₀) (I : Finset (Fin n)) (ζ : ℂ)
    (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) (rows : RowSliceMatrix n d)
    (x u : Fin n → ℂ) (c w : ℂ)
    (hX : ∀ j, ‖x j - u j‖ ≤ steepNetError d) (hC : ‖c - w‖ ≤ steepNetError d) :
    ‖(WithLp.toLp 2 ((retainedShiftedMatrix I ζ rows).mulVec
      (fun j => (x j + c) - (u j + w))) : EuclideanSpace ℂ I)‖ ≤
        2 * (1 + Z₀) * Real.sqrt ((n : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hRootLe : Real.sqrt d ≤ (d : ℝ) := by
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hdR.le).mp
    rw [Real.sq_sqrt hdR.le]
    nlinarith
  have hShiftD : ‖ζ‖ ≤ Z₀ * (d : ℝ) :=
    hShift.trans (mul_le_mul_of_nonneg_left hRootLe hZ)
  have hD : (d : ℝ) + ‖ζ‖ ≤ (1 + Z₀) * d := by linarith
  have hδ : 0 ≤ steepNetError d :=
    div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg d) (3 / 2))
  have hError := retainedShiftedMatrix_l2_error I ζ rows
    (fun j => (x j + c) - (u j + w))
      (mul_nonneg (by norm_num) hδ)
      (shifted_vector_net_coordinate_error x u c w hX hC)
  apply hError.trans
  calc
    _ ≤ Real.sqrt n * ((1 + Z₀) * d) * (2 * steepNetError d) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num) hδ)
      exact mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _)
    _ = 2 * (1 + Z₀) * (Real.sqrt n / Real.sqrt d) := by
      rw [steepNetError, degree_three_halves_eq hd]
      field_simp
    _ = _ := by rw [Real.sqrt_div (Nat.cast_nonneg n)]

end CircularLaw
