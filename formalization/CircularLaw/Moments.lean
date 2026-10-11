import CircularLaw.Marginal
import CircularLaw.Hypergeometric

/-!
# Entry moments and the variance normalization

The row-coordinate mean and variance follow from the exact slice marginal.
No independence between coordinates of the same row is needed.
-/

noncomputable section
namespace CircularLaw

def rowEntryReal {n d : ℕ} (s : RowSlice n d) (j : Fin n) : ℝ :=
  if j ∈ s.val then 1 else 0

theorem rowEntryReal_coe {n d : ℕ} (s : RowSlice n d) (j : Fin n) :
    (rowEntryReal s j : ℂ) = rowEntry s j := by
  simp only [rowEntryReal, rowEntry]
  split_ifs <;> simp

theorem rowEntryReal_sq {n d : ℕ} (s : RowSlice n d) (j : Fin n) :
    (rowEntryReal s j) ^ 2 = rowEntryReal s j := by
  simp only [rowEntryReal]
  split_ifs <;> norm_num

theorem row_entry_mean {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    finiteMean (fun s : RowSlice n d => rowEntryReal s j) = (d : ℝ) / n := by
  rw [show (fun s : RowSlice n d => rowEntryReal s j) =
      (fun s => if j ∈ s.val then (1 : ℝ) else 0) from rfl,
    finiteMean_indicator]
  exact row_coordinate_probability hd hdn j

theorem row_entry_variance {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    finiteMean (fun s : RowSlice n d => (rowEntryReal s j - (d : ℝ) / n) ^ 2) =
      ((d : ℝ) / n) * (1 - (d : ℝ) / n) := by
  haveI := rowSlice_nonempty hdn
  have hexpand (s : RowSlice n d) : (rowEntryReal s j - (d : ℝ) / n) ^ 2 =
      rowEntryReal s j - 2 * ((d : ℝ) / n) * rowEntryReal s j + ((d : ℝ) / n) ^ 2 := by
    nlinarith [rowEntryReal_sq s j]
  simp_rw [hexpand, finiteMean_add, finiteMean_sub, finiteMean_const_mul,
    finiteMean_const, row_entry_mean hd hdn j]
  ring

theorem bulkScaleSq_eq_n_mul_variance {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    bulkScaleSq n d = (n : ℝ) *
      finiteMean (fun s : RowSlice n d => (rowEntryReal s j - (d : ℝ) / n) ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hd hdn).ne'
  rw [row_entry_variance hd hdn j]
  unfold bulkScaleSq
  field_simp

end CircularLaw
