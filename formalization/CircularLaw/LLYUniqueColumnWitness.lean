import CircularLaw.RowSliceOutExpansion
import CircularLaw.LLYColumnBadMass

/-!
# Unique column witnesses from actual row-neighbour expansion

At most twice the expansion deficit can be spent on outgoing edges
landing in columns hit more than once. The diagonal coordinate set is
then removed explicitly. The result is uniform over every nested pair
of row sets and supplies actual adjoint witnesses.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem nested_finite_unique_indicator_bound {ι : Type*} (A B : Finset ι) (hAB : A ⊆ B) :
    (A.card : ℝ) ≤ (if B.card = 1 ∧ A.Nonempty then (1 : ℝ) else 0) +
      2 * ((B.card : ℝ) - if B.Nonempty then 1 else 0) := by
  have hCard := Finset.card_le_card hAB
  by_cases hB : B.Nonempty
  · by_cases hOne : B.card = 1
    · by_cases hA : A.Nonempty
      · have hACard : A.card = 1 := by have h := hA.card_pos; omega
        simp only [hOne, hACard, Nat.cast_one, hA, hB, and_self, if_true, sub_self, mul_zero, add_zero, le_refl]
      · have hACard : A.card = 0 := by
          by_contra h
          exact hA (Finset.card_pos.mp (by omega))
        simp only [hOne, hACard, Nat.cast_zero, Nat.cast_one, hA, and_false, if_false,
          hB, if_true, sub_self, mul_zero, add_zero, le_refl]
    · have hBTwo : (2 : ℝ) ≤ B.card := by exact_mod_cast (by have h := hB.card_pos; omega : 2 ≤ B.card)
      have hCardR : (A.card : ℝ) ≤ B.card := by exact_mod_cast hCard
      simp only [hOne, false_and, if_false, hB, if_true, zero_add]
      linarith
  · have hBZero : B.card = 0 := by
      by_contra h
      exact hB (Finset.card_pos.mp (by omega))
    have hAZero : A.card = 0 := by omega
    simp only [hAZero, hBZero, Nat.cast_zero, zero_ne_one, false_and, if_false,
      hB, sub_zero, mul_zero, add_zero, le_refl]

theorem out_neighbour_iff_column_support_nonempty {n d : ℕ} (rows : RowSliceMatrix n d)
    (J : Finset (Fin n)) (j : Fin n) :
    j ∈ rowSliceOutNeighbours J rows ↔ (rowSliceColumnSupport rows j ∩ J).Nonempty := by
  rw [mem_rowSliceOutNeighbours]
  constructor
  · rintro ⟨i, hiJ, hiRow⟩
    exact ⟨i, Finset.mem_inter.mpr ⟨(rowSliceColumnSupport_mem rows j i).mpr hiRow, hiJ⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_inter.mp hi).2,
      (rowSliceColumnSupport_mem rows j i).mp (Finset.mem_inter.mp hi).1⟩

def rowSliceUniqueColumns {n d : ℕ} (L J : Finset (Fin n)) (rows : RowSliceMatrix n d) :
    Finset (Fin n) := Finset.univ.filter (fun j =>
      (rowSliceColumnSupport rows j ∩ J).card = 1 ∧ (rowSliceColumnSupport rows j ∩ L).Nonempty)

theorem row_slice_unique_columns_mass_bound {n d : ℕ} (L J : Finset (Fin n))
    (hLJ : L ⊆ J) (rows : RowSliceMatrix n d) :
    (d : ℝ) * L.card ≤ (rowSliceUniqueColumns L J rows).card +
      2 * ((d : ℝ) * J.card - (rowSliceOutNeighbours J rows).card) := by
  have hPoint (j : Fin n) : rowSliceColumnSubsetLoad rows L j ≤
      (if j ∈ rowSliceUniqueColumns L J rows then (1 : ℝ) else 0) +
        2 * (rowSliceColumnSubsetLoad rows J j - if j ∈ rowSliceOutNeighbours J rows then 1 else 0) := by
    rw [rowSliceColumnSubsetLoad_eq_inter_card, rowSliceColumnSubsetLoad_eq_inter_card]
    have h := nested_finite_unique_indicator_bound (rowSliceColumnSupport rows j ∩ L)
      (rowSliceColumnSupport rows j ∩ J) (fun i hi =>
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hLJ (Finset.mem_inter.mp hi).2⟩)
    simpa only [rowSliceUniqueColumns, Finset.mem_filter, Finset.mem_univ, true_and,
      out_neighbour_iff_column_support_nonempty] using h
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hPoint j)
  rw [rowSliceColumnSubsetLoad_sum] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_boole, rowSliceColumnSubsetLoad_sum] at h
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using h

theorem row_slice_unique_columns_expansion_count {n d : ℕ} (L J : Finset (Fin n))
    (hLJ : L ⊆ J) (rows : RowSliceMatrix n d) {ε : ℝ}
    (hExpansion : (1 - ε) * (d : ℝ) * J.card ≤ (rowSliceOutNeighbours J rows).card) :
    (d : ℝ) * L.card - 2 * ε * d * J.card ≤ (rowSliceUniqueColumns L J rows).card := by
  have h := row_slice_unique_columns_mass_bound L J hLJ rows
  nlinarith only [h, hExpansion]

theorem row_slice_unique_column_witness {n d : ℕ} (L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (rows : RowSliceMatrix n d) (j : Fin n) (hj : j ∈ rowSliceUniqueColumns L J rows) :
    ∃ i ∈ L, rowSliceColumnSupport rows j ∩ J = {i} := by
  obtain ⟨hCard, i, hi⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hCard
  have hiJ : i ∈ rowSliceColumnSupport rows j ∩ J :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hLJ (Finset.mem_inter.mp hi).2⟩
  have hiq : i = q := by rw [hq] at hiJ; exact Finset.mem_singleton.mp hiJ
  exact ⟨i, (Finset.mem_inter.mp hi).2, by simpa only [hiq] using hq⟩

def UniformUniqueColumnWitness {n d : ℕ} (s t : ℕ) (rows : RowSliceMatrix n d) : Prop :=
  ∀ L J : Finset (Fin n), L ⊆ J → L.card = s → J.card = t →
    (d : ℝ) * s / 2 ≤ (rowSliceUniqueColumns L J rows \ J).card

theorem uniform_unique_column_witness_of_expansion {n d s t : ℕ} (rows : RowSliceMatrix n d)
    {ε : ℝ} (hExpansion : RowSliceOutExpansion t ε rows)
    (hError : ε * t ≤ (s : ℝ) / 8) (hRatio : (t : ℝ) ≤ (d : ℝ) * s / 4) :
    UniformUniqueColumnWitness s t rows := by
  intro L J hLJ hL hJ
  have hCount := row_slice_unique_columns_expansion_count L J hLJ rows
    (by simpa only [hJ] using hExpansion J hJ)
  have hCard := Finset.card_sdiff_add_card_inter (rowSliceUniqueColumns L J rows) J
  have hInter := Finset.card_le_card (Finset.inter_subset_right (s₁ := rowSliceUniqueColumns L J rows) (s₂ := J))
  have hNat : (rowSliceUniqueColumns L J rows).card ≤ (rowSliceUniqueColumns L J rows \ J).card + J.card := by omega
  have hReal : ((rowSliceUniqueColumns L J rows).card : ℝ) ≤
      (rowSliceUniqueColumns L J rows \ J).card + J.card := by exact_mod_cast hNat
  have hErrorScaled := mul_le_mul_of_nonneg_left hError (Nat.cast_nonneg (α := ℝ) d)
  rw [hL, hJ] at hCount
  rw [hJ] at hReal
  nlinarith only [hCount, hReal, hErrorScaled, hRatio]

end CircularLaw
