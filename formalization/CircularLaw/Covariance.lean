import CircularLaw.MeasureModel

/-!
# Dependence between coordinates in one row

The joint inclusion probability comes from counting supersets. Distinct
coordinates are negatively correlated; independence is only between rows.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem slice_containment_probability {n d : ℕ} (hd : d ≤ n)
    (T : Finset (Fin n)) :
    uniformProbability (fun s : RowSlice n d => T ⊆ s.val) =
      (d.choose T.card : ℝ) / n.choose T.card := by
  classical
  have hq : T.card ≤ n := by simpa using Finset.card_le_univ T
  have hcnd : (0 : ℝ) < n.choose d := by exact_mod_cast Nat.choose_pos hd
  have hcnq : (0 : ℝ) < n.choose T.card := by exact_mod_cast Nat.choose_pos hq
  by_cases hqd : T.card ≤ d
  · have hidentity : (n.choose d : ℝ) * d.choose T.card =
        n.choose T.card * (n - T.card).choose (d - T.card) := by
      exact_mod_cast (Nat.choose_mul (n := n) hqd)
    simp only [uniformProbability, card_slices_containing_set hqd,
      Nat.card_eq_fintype_card, card_rowSlice]
    apply (div_eq_div_iff hcnd.ne' hcnq.ne').mpr
    nlinarith [hidentity]
  · haveI : IsEmpty {s : RowSlice n d // T ⊆ s.val} := ⟨fun s => by
      have hc := Finset.card_le_card s.property
      rw [s.val.property] at hc
      exact hqd hc⟩
    rw [Nat.choose_eq_zero_of_lt (by omega : d < T.card)]
    simp [uniformProbability]

theorem row_pair_probability {n d : ℕ} (hd : d ≤ n) (i j : Fin n) (hij : i ≠ j) :
    uniformProbability (fun s : RowSlice n d => i ∈ s.val ∧ j ∈ s.val) =
      ((d : ℝ) * (d - 1)) / ((n : ℝ) * (n - 1)) := by
  classical
  have h := slice_containment_probability hd ({i, j} : Finset (Fin n))
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.card_pair hij] at h
  rw [h, Nat.cast_choose_two, Nat.cast_choose_two]
  have hn : 2 ≤ n := by
    simpa only [Finset.card_pair hij, Fintype.card_fin] using
      Finset.card_le_univ ({i, j} : Finset (Fin n))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp

theorem row_entry_pair_mean {n d : ℕ} (hd : d ≤ n) (i j : Fin n) (hij : i ≠ j) :
    finiteMean (fun s : RowSlice n d => rowEntryReal s i * rowEntryReal s j) =
      ((d : ℝ) * (d - 1)) / ((n : ℝ) * (n - 1)) := by
  classical
  have he : (fun s : RowSlice n d => rowEntryReal s i * rowEntryReal s j) =
      (fun s => if i ∈ s.val ∧ j ∈ s.val then (1 : ℝ) else 0) := by
    funext s
    by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val <;> simp [rowEntryReal, hi, hj]
  rw [he, finiteMean_indicator]
  exact row_pair_probability hd i j hij

theorem row_entry_covariance {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    finiteMean (fun s : RowSlice n d =>
      (rowEntryReal s i - (d : ℝ) / n) * (rowEntryReal s j - (d : ℝ) / n)) =
      -(((d : ℝ) / n) * (1 - (d : ℝ) / n)) / ((n : ℝ) - 1) := by
  haveI := rowSlice_nonempty hdn
  have he (s : RowSlice n d) :
      (rowEntryReal s i - (d : ℝ) / n) * (rowEntryReal s j - (d : ℝ) / n) =
      rowEntryReal s i * rowEntryReal s j - (d : ℝ) / n * rowEntryReal s i -
        (d : ℝ) / n * rowEntryReal s j + ((d : ℝ) / n) ^ 2 := by ring
  simp_rw [he, finiteMean_add, finiteMean_sub, finiteMean_const_mul,
    finiteMean_const, row_entry_mean hd hdn i, row_entry_mean hd hdn j,
    row_entry_pair_mean hdn i j hij]
  have hn : 2 ≤ n := by
    simpa only [Finset.card_pair hij, Fintype.card_fin] using
      Finset.card_le_univ ({i, j} : Finset (Fin n))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

theorem rowSliceLaw_covariance {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ s, (rowEntryReal s i - (d : ℝ) / n) * (rowEntryReal s j - (d : ℝ) / n)
      ∂rowSliceLaw n d) =
      -(((d : ℝ) / n) * (1 - (d : ℝ) / n)) / ((n : ℝ) - 1) := by
  rw [rowSliceLaw, integral_finiteUniformMeasure]
  exact row_entry_covariance hd hdn i j hij

def centeredRowReal {n d : ℕ} (s : RowSlice n d) (j : Fin n) : ℝ :=
  rowEntryReal s j - (d : ℝ) / n

theorem centeredRowReal_mean {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    finiteMean (fun s : RowSlice n d => centeredRowReal s j) = 0 := by
  haveI := rowSlice_nonempty hdn
  simp only [centeredRowReal, finiteMean_sub, row_entry_mean hd hdn j, finiteMean_const,
    sub_self]

theorem centered_row_covariance {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (i j : Fin n) :
    finiteMean (fun s : RowSlice n d => centeredRowReal s i * centeredRowReal s j) =
      (((d : ℝ) / n) * (1 - (d : ℝ) / n) / ((n : ℝ) - 1)) *
        ((if i = j then (n : ℝ) else 0) - 1) := by
  classical
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have h := row_entry_variance hd hdn i
    simp only [pow_two] at h
    rw [show (fun s : RowSlice n d => centeredRowReal s i * centeredRowReal s i) =
      (fun s => (rowEntryReal s i - (d : ℝ) / n) * (rowEntryReal s i - (d : ℝ) / n)) from rfl,
      h]
    field_simp
  · rw [if_neg hij]
    have h := row_entry_covariance hd hdn i j hij
    change finiteMean (fun s : RowSlice n d =>
      (rowEntryReal s i - (d : ℝ) / n) * (rowEntryReal s j - (d : ℝ) / n)) = _
    rw [h]
    ring

theorem centered_row_dot_mean {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (a : Fin n → ℝ) :
    finiteMean (fun s : RowSlice n d => ∑ j, a j * centeredRowReal s j) = 0 := by
  rw [finiteMean_finset_sum]
  simp only [finiteMean_const_mul, centeredRowReal_mean hd hdn, mul_zero, Finset.sum_const_zero]

theorem centered_row_dot_variance {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (a : Fin n → ℝ) :
    finiteMean (fun s : RowSlice n d => (∑ j, a j * centeredRowReal s j) ^ 2) =
      (((d : ℝ) / n) * (1 - (d : ℝ) / n) / ((n : ℝ) - 1)) *
        ((n : ℝ) * (∑ j, a j ^ 2) - (∑ j, a j) ^ 2) := by
  classical
  let C : ℝ := ((d : ℝ) / n) * (1 - (d : ℝ) / n) / ((n : ℝ) - 1)
  have hexpand (s : RowSlice n d) : (∑ j, a j * centeredRowReal s j) ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (centeredRowReal s i * centeredRowReal s j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand, finiteMean_finset_sum, finiteMean_const_mul,
    centered_row_covariance hn hd hdn]
  have hterm (i j : Fin n) : (a i * a j) * (C * ((if i = j then (n : ℝ) else 0) - 1)) =
      C * ((a i * a j) * (if i = j then (n : ℝ) else 0) - a i * a j) := by ring
  change (∑ i, ∑ j, (a i * a j) * (C * ((if i = j then (n : ℝ) else 0) - 1))) = _
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  have hdiag : (∑ i, ∑ j, (a i * a j) * (if i = j then (n : ℝ) else 0)) =
      (n : ℝ) * ∑ j, a j ^ 2 := by
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag, pow_two, ← Finset.sum_mul_sum]

theorem complex_norm_sq_parts (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem centered_row_complex_dot_second_moment {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (a : Fin n → ℂ) :
    finiteMean (fun s : RowSlice n d => ‖∑ j, a j * (centeredRowReal s j : ℂ)‖ ^ 2) =
      (((d : ℝ) / n) * (1 - (d : ℝ) / n) / ((n : ℝ) - 1)) *
        ((n : ℝ) * (∑ j, ‖a j‖ ^ 2) - ‖∑ j, a j‖ ^ 2) := by
  have hexpand (s : RowSlice n d) : ‖∑ j, a j * (centeredRowReal s j : ℂ)‖ ^ 2 =
      (∑ j, (a j).re * centeredRowReal s j) ^ 2 +
        (∑ j, (a j).im * centeredRowReal s j) ^ 2 := by
    simp only [complex_norm_sq_parts, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_add]
  simp_rw [hexpand, finiteMean_add, centered_row_dot_variance hn hd hdn,
    complex_norm_sq_parts, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib]
  ring

/-- The centered slice is isotropic on the orthogonal complement of the
all-ones vector, with exactly the variance-normalization scale. -/
theorem centered_row_complex_dot_second_moment_of_sum_zero {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (a : Fin n → ℂ) (ha : ∑ j, a j = 0) :
    finiteMean (fun s : RowSlice n d => ‖∑ j, a j * (centeredRowReal s j : ℂ)‖ ^ 2) =
      (bulkScaleSq n d / ((n : ℝ) - 1)) * (∑ j, ‖a j‖ ^ 2) := by
  rw [centered_row_complex_dot_second_moment hn hd hdn a, ha, norm_zero, zero_pow
    (by decide : 2 ≠ 0), sub_zero]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold bulkScaleSq
  field_simp

theorem rowSliceLaw_complex_dot_second_moment {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (a : Fin n → ℂ) :
    (∫ s, ‖∑ j, a j * (centeredRowReal s j : ℂ)‖ ^ 2 ∂rowSliceLaw n d) =
      (((d : ℝ) / n) * (1 - (d : ℝ) / n) / ((n : ℝ) - 1)) *
        ((n : ℝ) * (∑ j, ‖a j‖ ^ 2) - ‖∑ j, a j‖ ^ 2) := by
  rw [rowSliceLaw, integral_finiteUniformMeasure]
  exact centered_row_complex_dot_second_moment hn hd hdn a

end CircularLaw
