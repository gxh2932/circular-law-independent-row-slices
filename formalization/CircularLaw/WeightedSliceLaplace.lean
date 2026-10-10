import CircularLaw.Hypergeometric
import CircularLaw.Marginal

/-!
# Weighted exponential moments of an exact row slice

Expanding a product over subsets and using the checked containment
probabilities bounds all positive factors by the Bernoulli product.
Complementing the exact slice gives the same bound for negative tilts.
Coordinates within a row are never assumed independent.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def weightedSliceSum {n d : ℕ} (M : Finset (Fin n)) (w : Fin n → ℝ)
    (s : RowSlice n d) : ℝ := ∑ j ∈ M, if j ∈ s.val then w j else 0

theorem finiteMean_slice_weighted_product_le {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ j ∈ M, 0 ≤ a j) :
    finiteMean (fun s : RowSlice n d => ∏ j ∈ M, (1 + if j ∈ s.val then a j else 0)) ≤
      ∏ j ∈ M, (1 + ((d : ℝ) / n) * a j) := by
  have hExpand (s : RowSlice n d) :
      (∏ j ∈ M, (1 + if j ∈ s.val then a j else 0)) =
        ∑ T ∈ M.powerset, if T ⊆ s.val then (∏ j ∈ T, a j) else 0 := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ⊆ s.val
    · rw [if_pos hT]
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_pos (hT hj)]
    · rw [if_neg hT]
      obtain ⟨j, hj, hjNot⟩ := Finset.not_subset.mp hT
      exact Finset.prod_eq_zero hj (if_neg hjNot)
  simp_rw [hExpand]
  rw [finiteMean_finset_sum]
  calc
    _ = ∑ T ∈ M.powerset, (∏ j ∈ T, a j) *
        uniformProbability (fun s : RowSlice n d => T ⊆ s.val) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← finiteMean_indicator, ← finiteMean_const_mul]
      congr 1
      funext s
      split_ifs <;> simp only [mul_one, mul_zero]
    _ ≤ ∑ T ∈ M.powerset, (∏ j ∈ T, ((d : ℝ) / n) * a j) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hNonneg : 0 ≤ ∏ j ∈ T, a j := Finset.prod_nonneg (fun j hj =>
        ha j ((Finset.mem_powerset.mp hT) hj))
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (slice_containment_probability_le hn hd T) hNonneg
    _ = _ := (Finset.prod_one_add M).symm

theorem weightedSliceSum_laplace_product (n d : ℕ) (M : Finset (Fin n)) (w : Fin n → ℝ)
    (s : RowSlice n d) (tilt : ℝ) :
    Real.exp (tilt * weightedSliceSum M w s) =
      ∏ j ∈ M, (1 + if j ∈ s.val then Real.exp (tilt * w j) - 1 else 0) := by
  unfold weightedSliceSum
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ s.val <;> simp only [hj, if_true, if_false, mul_zero, Real.exp_zero]
  · ring
  · norm_num

theorem finiteMean_slice_weighted_laplace_nonneg {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ j ∈ M, 0 ≤ w j)
    {tilt : ℝ} (htilt : 0 ≤ tilt) :
    finiteMean (fun s : RowSlice n d => Real.exp (tilt * weightedSliceSum M w s)) ≤
      ∏ j ∈ M, (1 + ((d : ℝ) / n) * (Real.exp (tilt * w j) - 1)) := by
  simp_rw [weightedSliceSum_laplace_product n d M w]
  apply finiteMean_slice_weighted_product_le hn hd
  intro j hj
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg htilt (hw j hj)))

def rowSliceComplementEquiv {n d : ℕ} (hd : d ≤ n) : RowSlice n d ≃ RowSlice n (n - d) where
  toFun s := ⟨Finset.univ \ s.val, by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, s.property]⟩
  invFun s := ⟨Finset.univ \ s.val, by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, s.property]
    omega⟩
  left_inv s := by
    apply Subtype.ext
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  right_inv s := by
    apply Subtype.ext
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

theorem weightedSliceSum_complement {n d : ℕ} (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (s : RowSlice n d) :
    weightedSliceSum M w (rowSliceComplementEquiv hd s) =
      (∑ j ∈ M, w j) - weightedSliceSum M w s := by
  unfold weightedSliceSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (if j ∈ Finset.univ \ s.val then w j else 0) = w j - (if j ∈ s.val then w j else 0)
  by_cases hj : j ∈ s.val <;> simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hj,
    not_true_eq_false, not_false_eq_true, if_true, if_false, sub_self, sub_zero]

theorem finiteMean_slice_weighted_laplace_nonpos {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ j ∈ M, 0 ≤ w j)
    {tilt : ℝ} (htilt : tilt ≤ 0) :
    finiteMean (fun s : RowSlice n d => Real.exp (tilt * weightedSliceSum M w s)) ≤
      ∏ j ∈ M, (1 + ((d : ℝ) / n) * (Real.exp (tilt * w j) - 1)) := by
  let e := rowSliceComplementEquiv hd
  have hRewrite (s : RowSlice n d) : Real.exp (tilt * weightedSliceSum M w s) =
      Real.exp (tilt * ∑ j ∈ M, w j) * Real.exp (-tilt * weightedSliceSum M w (e s)) := by
    rw [weightedSliceSum_complement, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hRewrite]
  rw [finiteMean_const_mul, finiteMean_reindex e
    (fun s : RowSlice n (n - d) => Real.exp (-tilt * weightedSliceSum M w s))]
  have hUpper := finiteMean_slice_weighted_laplace_nonneg hn (Nat.sub_le n d) M w hw
    (by linarith : 0 ≤ -tilt)
  apply (mul_le_mul_of_nonneg_left hUpper (Real.exp_nonneg _)).trans_eq
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hExp : Real.exp (tilt * w j) ≠ 0 := (Real.exp_pos _).ne'
  rw [show -tilt * w j = -(tilt * w j) by ring, Real.exp_neg, Nat.cast_sub hd]
  field_simp
  ring

theorem finiteMean_slice_weighted_laplace {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ j ∈ M, 0 ≤ w j) (tilt : ℝ) :
    finiteMean (fun s : RowSlice n d => Real.exp (tilt * weightedSliceSum M w s)) ≤
      ∏ j ∈ M, (1 + ((d : ℝ) / n) * (Real.exp (tilt * w j) - 1)) := by
  by_cases htilt : 0 ≤ tilt
  · exact finiteMean_slice_weighted_laplace_nonneg hn hd M w hw htilt
  · exact finiteMean_slice_weighted_laplace_nonpos hn hd M w hw (le_of_not_ge htilt)

theorem finiteMean_weightedSliceSum {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) :
    finiteMean (weightedSliceSum M w : RowSlice n d → ℝ) = ((d : ℝ) / n) * ∑ j ∈ M, w j := by
  unfold weightedSliceSum
  rw [finiteMean_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hPoint : (fun s : RowSlice n d => if j ∈ s.val then w j else 0) =
      (fun s => w j * (if j ∈ s.val then (1 : ℝ) else 0)) := by
    funext s
    split_ifs <;> simp only [mul_one, mul_zero]
  rw [hPoint, finiteMean_const_mul, finiteMean_indicator, row_coordinate_probability hd hdn j, mul_comm]

theorem finiteMean_slice_weighted_laplace_exp {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ j ∈ M, 0 ≤ w j) (tilt : ℝ) :
    finiteMean (fun s : RowSlice n d => Real.exp (tilt * weightedSliceSum M w s)) ≤
      Real.exp (((d : ℝ) / n) * ∑ j ∈ M, (Real.exp (tilt * w j) - 1)) := by
  have hp : (d : ℝ) / n ≤ 1 := (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    (by exact_mod_cast hd)
  have hpNonneg : 0 ≤ (d : ℝ) / n := div_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg n)
  apply (finiteMean_slice_weighted_laplace hn hd M w hw tilt).trans
  calc
    _ ≤ ∏ j ∈ M, Real.exp (((d : ℝ) / n) * (Real.exp (tilt * w j) - 1)) := by
      apply Finset.prod_le_prod
      · intro j _
        have hPositive := mul_nonneg hpNonneg (Real.exp_nonneg (tilt * w j))
        nlinarith only [hp, hPositive]
      · intro j _
        have h := Real.add_one_le_exp (((d : ℝ) / n) * (Real.exp (tilt * w j) - 1))
        linarith only [h]
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

theorem finiteMean_slice_centered_laplace_exp {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (M : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ j ∈ M, 0 ≤ w j) (tilt : ℝ) :
    finiteMean (fun s : RowSlice n d =>
      Real.exp (tilt * (weightedSliceSum M w s - ((d : ℝ) / n) * ∑ j ∈ M, w j))) ≤
      Real.exp (((d : ℝ) / n) * ∑ j ∈ M, (Real.exp (tilt * w j) - 1 - tilt * w j)) := by
  have hPoint (s : RowSlice n d) :
      Real.exp (tilt * (weightedSliceSum M w s - ((d : ℝ) / n) * ∑ j ∈ M, w j)) =
        Real.exp (-tilt * ((d : ℝ) / n) * ∑ j ∈ M, w j) *
          Real.exp (tilt * weightedSliceSum M w s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hPoint]
  rw [finiteMean_const_mul]
  apply (mul_le_mul_of_nonneg_left (finiteMean_slice_weighted_laplace_exp hn hd M w hw tilt)
    (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end CircularLaw
