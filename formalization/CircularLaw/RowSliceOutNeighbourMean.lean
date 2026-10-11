import CircularLaw.RowSliceOutNeighbours

/-!
# Exact mean and degree calibration for occupied columns

The uniform product row law gives the literal probability that a column
is missed. A quadratic power estimate compares the actual mean to the
total number of outgoing edges, including integer ranks and degree zero.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem finite_uniform_complement_probability {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) : uniformProbability (fun x => ¬E x) = 1 - uniformProbability E := by
  have hPoint : (fun x : α => if ¬E x then (1 : ℝ) else 0) =
      (fun x => 1 - if E x then 1 else 0) := by
    funext x
    by_cases hx : E x <;> simp [hx]
  rw [← finiteMean_indicator, hPoint, finiteMean_sub, finiteMean_const, finiteMean_indicator]

theorem row_slice_coordinate_avoidance_probability {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (j : Fin n) : uniformProbability (fun s : RowSlice n d => j ∉ s.val) = 1 - (d : ℝ) / n := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [finite_uniform_complement_probability, row_coordinate_probability hd hdn]

theorem row_slice_out_neighbour_coordinate_void_probability {m n d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (S : Finset (Fin m)) (j : Fin n) :
    uniformProbability (fun rows : Fin m → RowSlice n d => j ∉ rowSliceOutNeighbours S rows) =
      (1 - (d : ℝ) / n) ^ S.card := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  let E := fun i : Fin m => fun s : RowSlice n d => i ∈ S → j ∉ s.val
  have hEvent : (fun rows : Fin m → RowSlice n d => j ∉ rowSliceOutNeighbours S rows) =
      (fun rows => ∀ i, E i (rows i)) := by
    funext rows
    apply propext
    simp only [mem_rowSliceOutNeighbours, not_exists, not_and, E]
  rw [hEvent, uniformProbability_pi]
  have hPoint (i : Fin m) : uniformProbability (E i) = if i ∈ S then 1 - (d : ℝ) / n else 1 := by
    by_cases hi : i ∈ S
    · simpa only [E, hi, true_implies, if_pos] using row_slice_coordinate_avoidance_probability hd hdn j
    · simp [E, hi, uniformProbability_true]
  simp_rw [hPoint]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

theorem finiteMean_rowSliceOutNeighbourCount {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (S : Finset (Fin m)) :
    finiteMean (fun rows : Fin m → RowSlice n d => ((rowSliceOutNeighbours S rows).card : ℝ)) =
      rowSliceOutNeighbourMean (n := n) d S := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hCoordinate (j : Fin n) : uniformProbability (fun rows : Fin m → RowSlice n d =>
      j ∈ rowSliceOutNeighbours S rows) = 1 - (1 - (d : ℝ) / n) ^ S.card := by
    have h := row_slice_out_neighbour_coordinate_void_probability hd hdn S j
    rw [finite_uniform_complement_probability] at h
    linarith
  have hCount (rows : Fin m → RowSlice n d) : ((rowSliceOutNeighbours S rows).card : ℝ) =
      ∑ j : Fin n, if j ∈ rowSliceOutNeighbours S rows then (1 : ℝ) else 0 := by
    simp
  simp_rw [hCount]
  rw [finiteMean_finset_sum]
  simp_rw [finiteMean_indicator, hCoordinate]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    rowSliceOutNeighbourMean]

theorem one_sub_pow_quadratic_upper {p : ℝ} (hp : 0 ≤ p) (hpOne : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ 1 - (k : ℝ) * p + (k : ℝ) * ((k : ℝ) - 1) / 2 * p ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hK : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk : k = 0
      · simp [hk]
      · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        exact mul_nonneg (Nat.cast_nonneg k) (by linarith)
    calc
      _ = (1 - p) ^ k * (1 - p) := pow_succ _ _
      _ ≤ (1 - (k : ℝ) * p + (k : ℝ) * ((k : ℝ) - 1) / 2 * p ^ 2) * (1 - p) :=
        mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hpOne)
      _ ≤ (1 - (k : ℝ) * p + (k : ℝ) * ((k : ℝ) - 1) / 2 * p ^ 2) * (1 - p) +
          ((k : ℝ) * ((k : ℝ) - 1) / 2) * p ^ 3 :=
        le_add_of_nonneg_right (mul_nonneg (div_nonneg hK (by norm_num)) (pow_nonneg hp 3))
      _ = _ := by push_cast; ring

theorem rowSliceOutNeighbourMean_bounds {m n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (S : Finset (Fin m)) :
    (d : ℝ) * S.card * (1 - (d : ℝ) * S.card / (2 * n)) ≤
      rowSliceOutNeighbourMean (n := n) d S ∧
      rowSliceOutNeighbourMean (n := n) d S ≤ (d : ℝ) * S.card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 ≤ (d : ℝ) / n := by positivity
  have hpOne : (d : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hdn)
  have hLower : 1 - (S.card : ℝ) * ((d : ℝ) / n) ≤ (1 - (d : ℝ) / n) ^ S.card := by
    have h := one_add_mul_le_pow (a := -((d : ℝ) / n)) (by linarith : -2 ≤ -((d : ℝ) / n)) S.card
    simpa only [mul_neg, ← sub_eq_add_neg] using h
  have hUpper : (1 - (d : ℝ) / n) ^ S.card ≤
      1 - (S.card : ℝ) * ((d : ℝ) / n) + (S.card : ℝ) ^ 2 / 2 * ((d : ℝ) / n) ^ 2 := by
    apply (one_sub_pow_quadratic_upper hp hpOne S.card).trans
    have hCoeff : (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 ≤ (S.card : ℝ) ^ 2 / 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _))
  unfold rowSliceOutNeighbourMean
  constructor
  · calc
      _ = (n : ℝ) * ((S.card : ℝ) * ((d : ℝ) / n) - (S.card : ℝ) ^ 2 / 2 * ((d : ℝ) / n) ^ 2) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hUpper]) hnR.le
  · calc
      _ ≤ (n : ℝ) * ((S.card : ℝ) * ((d : ℝ) / n)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hLower]) hnR.le
      _ = _ := by field_simp

end CircularLaw
