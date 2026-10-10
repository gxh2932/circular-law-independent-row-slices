import CircularLaw.BernoulliPrefixFiltration

/-!
# The literal column-then-row prefix schedule

Starting from an M-square minor, even times expose a square and odd times
expose one extra column. After 2*(N-M) insertions the full N-square matrix
has been exposed. Saturating at N defines the filtration at all times.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def sourceAlternatingPrefixRows (N M s : ℕ) : ℕ := min N (M + s / 2)

def sourceAlternatingPrefixColumns (N M s : ℕ) : ℕ := min N (M + (s + 1) / 2)

theorem source_alternating_prefix_rows_le (N M s : ℕ) :
    sourceAlternatingPrefixRows N M s ≤ N := min_le_left _ _

theorem source_alternating_prefix_columns_le (N M s : ℕ) :
    sourceAlternatingPrefixColumns N M s ≤ N := min_le_left _ _

theorem source_alternating_prefix_rows_mono (N M : ℕ) :
    Monotone (sourceAlternatingPrefixRows N M) := by
  intro s t hst
  unfold sourceAlternatingPrefixRows
  exact min_le_min le_rfl (by omega)

theorem source_alternating_prefix_columns_mono (N M : ℕ) :
    Monotone (sourceAlternatingPrefixColumns N M) := by
  intro s t hst
  unfold sourceAlternatingPrefixColumns
  exact min_le_min le_rfl (by omega)

theorem source_alternating_prefix_dimensions (N M s : ℕ) :
    sourceAlternatingPrefixRows N M s ≤ sourceAlternatingPrefixColumns N M s ∧
      sourceAlternatingPrefixColumns N M s ≤ sourceAlternatingPrefixRows N M s + 1 := by
  unfold sourceAlternatingPrefixRows sourceAlternatingPrefixColumns
  omega

theorem source_alternating_prefix_rows_ge_initial {N M : ℕ} (hM : M ≤ N) (s : ℕ) :
    M ≤ sourceAlternatingPrefixRows N M s := by
  unfold sourceAlternatingPrefixRows
  omega

theorem source_alternating_prefix_even {N M k : ℕ} (h : M + k ≤ N) :
    sourceAlternatingPrefixRows N M (2 * k) = M + k ∧
      sourceAlternatingPrefixColumns N M (2 * k) = M + k := by
  unfold sourceAlternatingPrefixRows sourceAlternatingPrefixColumns
  omega

theorem source_alternating_prefix_odd {N M k : ℕ} (h : M + k + 1 ≤ N) :
    sourceAlternatingPrefixRows N M (2 * k + 1) = M + k ∧
      sourceAlternatingPrefixColumns N M (2 * k + 1) = M + k + 1 := by
  unfold sourceAlternatingPrefixRows sourceAlternatingPrefixColumns
  omega

theorem source_alternating_prefix_initial {N M : ℕ} (hM : M ≤ N) :
    sourceAlternatingPrefixRows N M 0 = M ∧ sourceAlternatingPrefixColumns N M 0 = M := by
  exact source_alternating_prefix_even (k := 0) (by omega)

theorem source_alternating_prefix_terminal {N M : ℕ} (hM : M ≤ N) :
    sourceAlternatingPrefixRows N M (2 * (N - M)) = N ∧
      sourceAlternatingPrefixColumns N M (2 * (N - M)) = N := by
  have h := source_alternating_prefix_even (k := N - M) (by omega : M + (N - M) ≤ N)
  simpa only [Nat.add_sub_of_le hM] using h

def sourceAlternatingPrefixFiltration (N M : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (BernoulliSquareSample N)) :=
  bernoulliRectangularPrefixFiltration (sourceAlternatingPrefixRows N M)
    (sourceAlternatingPrefixColumns N M) (source_alternating_prefix_rows_le N M)
    (source_alternating_prefix_columns_le N M) (source_alternating_prefix_rows_mono N M)
    (source_alternating_prefix_columns_mono N M)

end CircularLaw
