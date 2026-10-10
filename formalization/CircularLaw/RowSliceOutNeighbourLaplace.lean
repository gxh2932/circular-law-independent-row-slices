import CircularLaw.RowSliceOutNeighbours

/-!
# Exponential moments of actual out-neighbour counts

Positive products of empty-column indicators expand over column subsets.
The exact-slice void bound supplies the Bernoulli product comparison.
Complementing the occupied count then gives its negative-tilt bound.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem finiteMean_out_neighbour_empty_product_le {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) (M : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ j ∈ M, 0 ≤ a j) :
    finiteMean (fun rows : Fin m → RowSlice n d =>
      ∏ j ∈ M, (1 + if j ∉ rowSliceOutNeighbours S rows then a j else 0)) ≤
        ∏ j ∈ M, (1 + ((1 - (d : ℝ) / n) ^ S.card) * a j) := by
  have hExpand (rows : Fin m → RowSlice n d) :
      (∏ j ∈ M, (1 + if j ∉ rowSliceOutNeighbours S rows then a j else 0)) =
        ∑ T ∈ M.powerset, if T ⊆ Finset.univ \ rowSliceOutNeighbours S rows then
          (∏ j ∈ T, a j) else 0 := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ⊆ Finset.univ \ rowSliceOutNeighbours S rows
    · rw [if_pos hT]
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_pos (Finset.mem_sdiff.mp (hT hj)).2]
    · rw [if_neg hT]
      obtain ⟨j, hj, hjNot⟩ := Finset.not_subset.mp hT
      have hjOut : j ∈ rowSliceOutNeighbours S rows := by
        by_contra h
        exact hjNot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h⟩)
      exact Finset.prod_eq_zero hj (if_neg (not_not.mpr hjOut))
  simp_rw [hExpand]
  rw [finiteMean_finset_sum]
  calc
    _ = ∑ T ∈ M.powerset, (∏ j ∈ T, a j) *
        uniformProbability (fun rows : Fin m → RowSlice n d =>
          T ⊆ Finset.univ \ rowSliceOutNeighbours S rows) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← finiteMean_indicator, ← finiteMean_const_mul]
      congr 1
      funext rows
      split_ifs <;> simp only [mul_one, mul_zero]
    _ ≤ ∑ T ∈ M.powerset, ∏ j ∈ T, ((1 - (d : ℝ) / n) ^ S.card) * a j := by
      apply Finset.sum_le_sum
      intro T hT
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hNonneg : 0 ≤ ∏ j ∈ T, a j := Finset.prod_nonneg
        (fun j hj => ha j ((Finset.mem_powerset.mp hT) hj))
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (row_slice_out_neighbour_void_probability hn hd S T) hNonneg
    _ = _ := (Finset.prod_one_add M).symm

theorem out_neighbour_empty_laplace_product {m n d : ℕ} (S : Finset (Fin m))
    (rows : Fin m → RowSlice n d) (tilt : ℝ) :
    Real.exp (tilt * ((Finset.univ \ rowSliceOutNeighbours S rows).card : ℝ)) =
      ∏ j : Fin n, (1 + if j ∉ rowSliceOutNeighbours S rows then Real.exp tilt - 1 else 0) := by
  have hCount : ((Finset.univ \ rowSliceOutNeighbours S rows).card : ℝ) =
      ∑ j : Fin n, if j ∉ rowSliceOutNeighbours S rows then (1 : ℝ) else 0 := by
    have hSet : Finset.univ \ rowSliceOutNeighbours S rows =
        Finset.univ.filter (fun j => j ∉ rowSliceOutNeighbours S rows) := by ext j; simp
    rw [hSet]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> norm_num
  rw [hCount, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ rowSliceOutNeighbours S rows
  · simp only [hj, not_true_eq_false, if_false, mul_zero, Real.exp_zero, add_zero]
  · simp only [hj, not_false_eq_true, if_true, mul_one]
    ring

theorem out_neighbour_negative_laplace_product {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) {tilt : ℝ} (htilt : 0 ≤ tilt) :
    finiteMean (fun rows : Fin m → RowSlice n d =>
      Real.exp (-tilt * ((rowSliceOutNeighbours S rows).card : ℝ))) ≤
        ((1 - (d : ℝ) / n) ^ S.card +
          (1 - (1 - (d : ℝ) / n) ^ S.card) * Real.exp (-tilt)) ^ n := by
  let q := (1 - (d : ℝ) / n) ^ S.card
  have hRewrite (rows : Fin m → RowSlice n d) :
      Real.exp (-tilt * ((rowSliceOutNeighbours S rows).card : ℝ)) =
        Real.exp (-tilt * n) *
          Real.exp (tilt * ((Finset.univ \ rowSliceOutNeighbours S rows).card : ℝ)) := by
    have hCard : (Finset.univ \ rowSliceOutNeighbours S rows).card +
        (rowSliceOutNeighbours S rows).card = n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (rowSliceOutNeighbours S rows))
    have hCardR : ((Finset.univ \ rowSliceOutNeighbours S rows).card : ℝ) +
        (rowSliceOutNeighbours S rows).card = n := by exact_mod_cast hCard
    rw [← Real.exp_add]
    congr 1
    linear_combination -tilt * hCardR
  simp_rw [hRewrite, out_neighbour_empty_laplace_product]
  rw [finiteMean_const_mul]
  apply (mul_le_mul_of_nonneg_left
    (finiteMean_out_neighbour_empty_product_le hn hd S Finset.univ
      (fun _ => Real.exp tilt - 1) (fun _ _ => sub_nonneg.mpr (Real.one_le_exp_iff.mpr htilt)))
    (Real.exp_nonneg _)).trans_eq
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show -tilt * (n : ℝ) = (n : ℝ) * -tilt by ring, Real.exp_nat_mul, ← mul_pow]
  congr 1
  change Real.exp (-tilt) * (1 + q * (Real.exp tilt - 1)) = q + (1 - q) * Real.exp (-tilt)
  have hExp : Real.exp (-tilt) * Real.exp tilt = 1 := by rw [← Real.exp_add]; simp
  linear_combination q * hExp

theorem out_neighbour_negative_laplace_exp {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) {tilt : ℝ} (htilt : 0 ≤ tilt) :
    finiteMean (fun rows : Fin m → RowSlice n d =>
      Real.exp (-tilt * ((rowSliceOutNeighbours S rows).card : ℝ))) ≤
        Real.exp (rowSliceOutNeighbourMean (n := n) d S * (Real.exp (-tilt) - 1)) := by
  let q := (1 - (d : ℝ) / n) ^ S.card
  have hp : 0 ≤ 1 - (d : ℝ) / n := by
    apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by exact_mod_cast hd)
  have hpOne : 1 - (d : ℝ) / n ≤ 1 := by
    have h : (0 : ℝ) ≤ (d : ℝ) / n := by positivity
    linarith
  have hq : 0 ≤ q := pow_nonneg hp _
  have hqOne : q ≤ 1 := pow_le_one₀ hp hpOne
  have hBase : 0 ≤ q + (1 - q) * Real.exp (-tilt) :=
    add_nonneg hq (mul_nonneg (sub_nonneg.mpr hqOne) (Real.exp_nonneg _))
  have hCompare : q + (1 - q) * Real.exp (-tilt) ≤
      Real.exp ((1 - q) * (Real.exp (-tilt) - 1)) := by
    have h := Real.add_one_le_exp ((1 - q) * (Real.exp (-tilt) - 1))
    nlinarith only [h]
  apply (out_neighbour_negative_laplace_product hn hd S htilt).trans
    ((pow_le_pow_left₀ hBase hCompare n).trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  unfold rowSliceOutNeighbourMean
  dsimp only [q]
  ring

end CircularLaw
