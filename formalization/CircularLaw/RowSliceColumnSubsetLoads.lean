import CircularLaw.RowSliceMatrixDiscrepancy

/-!
# Deterministic column loads from any subset of fixed-degree rows

The total load is exactly d times the number of chosen rows. Counting
columns above a threshold therefore proves LLY26a Lemma 5.2 for every
actual sample and every row subset, also in rectangular dimensions.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceColumnSubsetLoad {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (j : Fin n) : ℝ := ∑ i ∈ J, rowEntryReal (rows i) j

def rowSliceHeavySubsetColumns {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => t ≤ rowSliceColumnSubsetLoad rows J j)

theorem rowSliceColumnSubsetLoad_eq_card {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (j : Fin n) :
    rowSliceColumnSubsetLoad rows J j = ((J.filter (fun i => j ∈ (rows i).val)).card : ℝ) := by
  simp only [rowSliceColumnSubsetLoad, rowEntryReal, Finset.sum_boole]

theorem rowSliceColumnSubsetLoad_nonneg {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (j : Fin n) : 0 ≤ rowSliceColumnSubsetLoad rows J j := by
  rw [rowSliceColumnSubsetLoad_eq_card]
  positivity

theorem rowSliceColumnSubsetLoad_sum {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) :
    (∑ j : Fin n, rowSliceColumnSubsetLoad rows J j) = (d : ℝ) * J.card := by
  have hRow (i : Fin m) : (∑ j : Fin n, rowEntryReal (rows i) j) = (d : ℝ) := by
    simpa only [rectangularSliceMatrixReal] using rectangularSliceMatrixReal_rowSum rows i
  unfold rowSliceColumnSubsetLoad
  rw [Finset.sum_comm]
  simp only [hRow, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem rowSliceHeavySubsetColumns_mass_bound {m n d : ℕ}
    (rows : Fin m → RowSlice n d) (J : Finset (Fin m)) (t : ℝ) :
    ((rowSliceHeavySubsetColumns rows J t).card : ℝ) * t ≤ (d : ℝ) * J.card := by
  calc
    _ = ∑ _j ∈ rowSliceHeavySubsetColumns rows J t, t := by simp
    _ ≤ ∑ j ∈ rowSliceHeavySubsetColumns rows J t, rowSliceColumnSubsetLoad rows J j := by
      exact Finset.sum_le_sum (fun _ hj => (Finset.mem_filter.mp hj).2)
    _ ≤ ∑ j : Fin n, rowSliceColumnSubsetLoad rows J j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => rowSliceColumnSubsetLoad_nonneg rows J j)
    _ = _ := rowSliceColumnSubsetLoad_sum rows J

theorem rowSliceHeavySubsetColumns_card_bound {m n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (hJ : J.Nonempty) {r : ℝ} (hr : 0 < r) :
    ((rowSliceHeavySubsetColumns rows J (r * d * J.card / n)).card : ℝ) ≤ (n : ℝ) / r := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMass : 0 < (d : ℝ) * J.card := mul_pos (by exact_mod_cast hd)
    (by exact_mod_cast hJ.card_pos)
  have h := rowSliceHeavySubsetColumns_mass_bound rows J (r * d * J.card / n)
  apply (le_div_iff₀ hr).mpr
  apply (mul_le_mul_iff_right₀ hMass).mp
  calc
    _ = (n : ℝ) * (((rowSliceHeavySubsetColumns rows J (r * d * J.card / n)).card : ℝ) *
        (r * d * J.card / n)) := by field_simp
    _ ≤ (n : ℝ) * ((d : ℝ) * J.card) := mul_le_mul_of_nonneg_left h hnR.le
    _ = _ := by ring

def ColumnSubsetLoadTheorem : Prop :=
  ∀ m n d : ℕ, 0 < n → 0 < d → ∀ rows : Fin m → RowSlice n d,
    ∀ J : Finset (Fin m), J.Nonempty → ∀ r : ℝ, 0 < r →
      ((rowSliceHeavySubsetColumns rows J (r * d * J.card / n)).card : ℝ) ≤ (n : ℝ) / r

theorem column_subset_load_theorem : ColumnSubsetLoadTheorem := by
  intro m n d hn hd rows J hJ r hr
  exact rowSliceHeavySubsetColumns_card_bound hn hd rows J hJ hr

end CircularLaw
