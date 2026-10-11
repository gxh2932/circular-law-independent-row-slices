import Mathlib

/-!
# The independent row-slice model

The support representation is equivalent to the paper's zero-one vectors of
weight `d`: membership gives the entries and the support has cardinality `d`.
The finite uniform law on `RowSliceMatrix n d` is the independent product of
the uniform row laws, since every tuple of supports has the same weight.

References: `sections/01_intro.tex` and the centering discussion in
`sections/06_normals.tex`.
-/

open scoped BigOperators

noncomputable section

namespace CircularLaw

/-- A row of weight `d`, represented by its support. -/
abbrev RowSlice (n d : ℕ) := {s : Finset (Fin n) // s.card = d}

/-- A tuple of `n` exact row slices. -/
abbrev RowSliceMatrix (n d : ℕ) := Fin n → RowSlice n d

theorem card_rowSlice (n d : ℕ) : Fintype.card (RowSlice n d) = n.choose d := by
  simp [RowSlice]

theorem rowSlice_nonempty {n d : ℕ} (hd : d ≤ n) : Nonempty (RowSlice n d) := by
  apply Fintype.card_pos_iff.mp
  rw [card_rowSlice]
  exact Nat.choose_pos hd

theorem card_rowSliceMatrix (n d : ℕ) :
    Fintype.card (RowSliceMatrix n d) = (n.choose d) ^ n := by
  simp [RowSliceMatrix]

/-- The complex zero-one coordinate of a row. -/
def rowEntry {n d : ℕ} (s : RowSlice n d) (j : Fin n) : ℂ :=
  if j ∈ s.val then 1 else 0

theorem rowEntry_zero_or_one {n d : ℕ} (s : RowSlice n d) (j : Fin n) :
    rowEntry s j = 0 ∨ rowEntry s j = 1 := by
  simp only [rowEntry]
  split_ifs <;> simp

theorem row_sum {n d : ℕ} (s : RowSlice n d) :
    ∑ j : Fin n, rowEntry s j = (d : ℂ) := by
  simp [rowEntry, s.property]

/-- The matrix corresponding to the tuple of supports. -/
def sliceMatrix {n d : ℕ} (s : RowSliceMatrix n d) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => rowEntry (s i) j

/-- The fixed row sum forces the all-ones eigenvector. -/
theorem mulVec_one {n d : ℕ} (s : RowSliceMatrix n d) :
    (sliceMatrix s).mulVec (fun _ => 1) = fun _ => (d : ℂ) := by
  funext i
  simpa [Matrix.mulVec, dotProduct, sliceMatrix] using row_sum (s i)

/-- The all-ones vector is nonzero in positive dimension. -/
theorem one_vector_ne_zero {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n => (1 : ℂ)) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp at this

def centeredRow {n d : ℕ} (s : RowSlice n d) (j : Fin n) : ℂ :=
  rowEntry s j - (d : ℂ) / (n : ℂ)

theorem centeredRow_sum {n d : ℕ} (hn : 0 < n) (s : RowSlice n d) :
    ∑ j : Fin n, centeredRow s j = 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [centeredRow, Finset.sum_sub_distrib, row_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Subtracting the coordinate mean isolates a deterministic shift. -/
theorem row_dot_centering {n d : ℕ} (s : RowSlice n d) (y : Fin n → ℂ) (c : ℂ) :
    ∑ j, rowEntry s j * y j =
      (∑ j, rowEntry s j * (y j - c)) + (d : ℂ) * c := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, row_sum]
  ring

/-- The square of the Hilbert--Schmidt norm is exactly `n*d`. -/
theorem frobenius_sq {n d : ℕ} (s : RowSliceMatrix n d) :
    ∑ i, ∑ j, ‖sliceMatrix s i j‖ ^ 2 = (n : ℝ) * d := by
  have hrow (i : Fin n) : ∑ j, ‖sliceMatrix s i j‖ ^ 2 = (d : ℝ) := by
    simp [sliceMatrix, rowEntry, apply_ite, (s i).property]
  simp [hrow]

/-- The variance normalization used in the main theorem. -/
def bulkScaleSq (n d : ℕ) : ℝ := (d : ℝ) * (1 - (d : ℝ) / n)

theorem bulkScaleSq_pos {n d : ℕ} (hd : 0 < d) (hdn : d < n) :
    0 < bulkScaleSq n d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hd hdn)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdn' : (d : ℝ) < n := by exact_mod_cast hdn
  exact mul_pos hd' (sub_pos.mpr ((div_lt_one hn).mpr hdn'))

end CircularLaw
