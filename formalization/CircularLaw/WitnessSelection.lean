import CircularLaw.ProductFiberNorm

/-!
# Selecting many rows with many singleton witnesses

Double counting the row/block incidence matrix gives the total witness
count. Keeping rows above `B*q/(4*n)` leaves at least `3*B/4` rows when
the total is at least `B*q` and each row has at most `q` witnesses.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def largeWitnessRows {ι : Type*} [Fintype ι] (b : ι → ℕ) (a : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => a ≤ (b i : ℝ))

theorem mem_largeWitnessRows {ι : Type*} [Fintype ι] (b : ι → ℕ) (a : ℝ) (i : ι) :
    i ∈ largeWitnessRows b a ↔ a ≤ (b i : ℝ) := by
  simp only [largeWitnessRows, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sum_witness_count_double_count {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (J : κ → Finset (Fin n)) (rows : ι → RowSlice n d) :
    (∑ i, (singletonWitnessMask J (rows i)).card) =
      ∑ q, (Finset.univ.filter (fun i => ((rows i).val ∩ J q).card = 1)).card := by
  simp only [singletonWitnessMask, Finset.card_filter]
  rw [Finset.sum_comm]

theorem sum_witness_count_lower {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (J : κ → Finset (Fin n)) (rows : ι → RowSlice n d) {B : ℝ}
    (hWitness : ∀ q, B ≤
      ((Finset.univ.filter (fun i => ((rows i).val ∩ J q).card = 1)).card : ℝ)) :
    B * Fintype.card κ ≤ ∑ i, ((singletonWitnessMask J (rows i)).card : ℝ) := by
  rw [← Nat.cast_sum, sum_witness_count_double_count, Nat.cast_sum]
  have h := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset κ)) => hWitness q)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h

theorem witness_sum_le_large_rows {ι : Type*} [Fintype ι] (b : ι → ℕ)
    {q a : ℝ} (ha : 0 ≤ a) (hMax : ∀ i, (b i : ℝ) ≤ q) :
    (∑ i, (b i : ℝ)) ≤ (largeWitnessRows b a).card * q + Fintype.card ι * a := by
  have hPoint (i : ι) : (b i : ℝ) ≤ (if a ≤ (b i : ℝ) then q else 0) + a := by
    by_cases hi : a ≤ (b i : ℝ)
    · simp only [hi, ↓reduceIte]
      linarith [hMax i]
    · simp only [hi, ↓reduceIte, zero_add]
      exact (lt_of_not_ge hi).le
  apply (Finset.sum_le_sum (fun i _ => hPoint i)).trans_eq
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp only [largeWitnessRows, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

theorem large_witness_rows_card_lower {ι : Type*} [Fintype ι]
    (b : ι → ℕ) {n q B : ℝ} (hn : 0 < n) (hq : 0 < q) (hB : 0 ≤ B)
    (hDimension : (Fintype.card ι : ℝ) ≤ n) (hMax : ∀ i, (b i : ℝ) ≤ q)
    (hSum : B * q ≤ ∑ i, (b i : ℝ)) :
    (3 / 4 : ℝ) * B ≤ (largeWitnessRows b (B / (4 * n) * q)).card := by
  have ha : 0 ≤ B / (4 * n) * q := by positivity
  have hUpper := witness_sum_le_large_rows b ha hMax
  have hDim := mul_le_mul_of_nonneg_right hDimension ha
  have hCancel : n * (B / (4 * n) * q) = B * q / 4 := by field_simp
  rw [hCancel] at hDim
  have hScaled : ((3 / 4 : ℝ) * B) * q ≤
      ((largeWitnessRows b (B / (4 * n) * q)).card : ℝ) * q := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hq).mp hScaled

end CircularLaw
