import CircularLaw.AlternatingPrefixSchedule

/-!
# The modified retained-rank height and its exact integer guard

The rectangular full-row-rank state has doubled height one. Collapsing
that state to zero is the modified height used in the exposure argument.
At the final square, zero modified height still means every singular
value has been retained. A wider drift barrier discharges the strict
integer insertion guard without a rounding loss.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def collapseExposureHeight (h : ℕ) : ℕ := if h = 1 then 0 else h

def sourceAlternatingRetainedHeight (N M s r : ℕ) : ℕ :=
  collapseExposureHeight (sourceAlternatingPrefixRows N M s +
    sourceAlternatingPrefixColumns N M s - 2 * r)

theorem collapse_exposure_height_le (h : ℕ) : collapseExposureHeight h ≤ h := by
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem collapse_exposure_height_zero_iff (h : ℕ) :
    collapseExposureHeight h = 0 ↔ h = 0 ∨ h = 1 := by
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem collapse_exposure_height_growth {h h' : ℕ} (hGrowth : h' ≤ h + 1) :
    collapseExposureHeight h' ≤ collapseExposureHeight h + 2 := by
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem collapse_exposure_height_down {h h' : ℕ} (hDown : h' ≤ h - 1) :
    collapseExposureHeight h' ≤ collapseExposureHeight h - 1 := by
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem source_alternating_prefix_dimension_sum {N M s : ℕ}
    (hM : M ≤ N) (hs : s ≤ 2 * (N - M)) :
    sourceAlternatingPrefixRows N M s + sourceAlternatingPrefixColumns N M s = 2 * M + s := by
  unfold sourceAlternatingPrefixRows sourceAlternatingPrefixColumns
  omega

theorem source_alternating_prefix_remaining_time {N M s : ℕ}
    (hM : M ≤ N) (hs : s ≤ 2 * (N - M)) :
    2 * (N - M) - s = 2 * (N - sourceAlternatingPrefixColumns N M s) + s % 2 := by
  unfold sourceAlternatingPrefixColumns
  omega

theorem source_alternating_retained_height_square {N M k r : ℕ}
    (h : M + k ≤ N) (hr : r ≤ M + k) :
    sourceAlternatingRetainedHeight N M (2 * k) r = 2 * (M + k - r) := by
  obtain ⟨ha, hm⟩ := source_alternating_prefix_even h
  unfold sourceAlternatingRetainedHeight
  rw [ha, hm]
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem source_alternating_retained_height_rectangle {N M k r : ℕ}
    (h : M + k + 1 ≤ N) (hr : r ≤ M + k) :
    sourceAlternatingRetainedHeight N M (2 * k + 1) r =
      if r = M + k then 0 else 2 * (M + k - r) + 1 := by
  obtain ⟨ha, hm⟩ := source_alternating_prefix_odd h
  unfold sourceAlternatingRetainedHeight
  rw [ha, hm]
  unfold collapseExposureHeight
  split_ifs <;> omega

theorem source_alternating_retained_height_growth {N M s r r' : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M))
    (hRank : r ≤ r') :
    sourceAlternatingRetainedHeight N M (s + 1) r' ≤
      sourceAlternatingRetainedHeight N M s r + 2 := by
  apply collapse_exposure_height_growth
  rw [source_alternating_prefix_dimension_sum hM (by omega),
    source_alternating_prefix_dimension_sum hM (by omega)]
  have hDimensions := source_alternating_prefix_dimensions N M s
  have hSum := source_alternating_prefix_dimension_sum hM (by omega : s ≤ 2 * (N - M))
  omega

theorem source_alternating_retained_height_success_down {N M s r : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M))
    (hNext : r < sourceAlternatingPrefixColumns N M s) :
    sourceAlternatingRetainedHeight N M (s + 1) (r + 1) ≤
      sourceAlternatingRetainedHeight N M s r - 1 := by
  apply collapse_exposure_height_down
  rw [source_alternating_prefix_dimension_sum hM (by omega),
    source_alternating_prefix_dimension_sum hM (by omega)]
  have hDimensions := source_alternating_prefix_dimensions N M s
  have hSum := source_alternating_prefix_dimension_sum hM (by omega : s ≤ 2 * (N - M))
  omega

theorem source_alternating_wide_barrier_insertion_guard {N M s r : ℕ}
    (hM : M ≤ N) (hs : s ≤ 2 * (N - M))
    (hNext : r < sourceAlternatingPrefixColumns N M s)
    (hActive : 2 * ((2 * (N - M) - s) / 8) ≤ sourceAlternatingRetainedHeight N M s r) :
    (N - sourceAlternatingPrefixColumns N M s) / 8 <
      sourceAlternatingPrefixColumns N M s - r := by
  have hTime := source_alternating_prefix_remaining_time hM hs
  have hDimensions := source_alternating_prefix_dimensions N M s
  have hCollapse := collapse_exposure_height_le
    (sourceAlternatingPrefixRows N M s + sourceAlternatingPrefixColumns N M s - 2 * r)
  change 2 * ((2 * (N - M) - s) / 8) ≤ collapseExposureHeight
    (sourceAlternatingPrefixRows N M s + sourceAlternatingPrefixColumns N M s - 2 * r) at hActive
  omega

theorem source_alternating_retained_height_terminal_zero_iff {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ N) :
    sourceAlternatingRetainedHeight N M (2 * (N - M)) r = 0 ↔ r = N := by
  have h := source_alternating_retained_height_square (k := N - M)
    (by omega : M + (N - M) ≤ N) (by omega : r ≤ M + (N - M))
  rw [h]
  omega

theorem source_alternating_retained_height_initial_bound {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ M) (hInitial : 2 * (M - r) ≤ N - M) :
    (sourceAlternatingRetainedHeight N M 0 r : ℝ) ≤ (2 * (N - M) : ℕ) / (2 : ℝ) := by
  rw [source_alternating_retained_height_square (k := 0) (by omega) (by omega)]
  have hReal : (2 * (M - r) : ℕ) ≤ N - M := hInitial
  have hCast : ((2 * (M - r) : ℕ) : ℝ) ≤ (N - M : ℕ) := by exact_mod_cast hReal
  simpa only [Nat.add_zero, Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hCast

theorem measurable_source_alternating_retained_height {N M s : ℕ}
    (r : BernoulliSquareSample N → ℕ)
    (hr : Measurable[sourceAlternatingPrefixFiltration N M s] r) :
    Measurable[sourceAlternatingPrefixFiltration N M s]
      (fun x => sourceAlternatingRetainedHeight N M s (r x)) :=
  (Measurable.of_discrete : Measurable (sourceAlternatingRetainedHeight N M s)).comp hr

end CircularLaw
