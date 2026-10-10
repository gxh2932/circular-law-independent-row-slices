import CircularLaw.WeightHeightBounds
import CircularLaw.ProfileK2Separation

/-!
# High-height coordinates below an upper weight cutoff

If the cutoff is below the large-part weight lower bound, every such
part is small. Its actual weight order lies in a finite logarithmic
interval. The checked 512-times-cutoff bin bound controls the total
coordinate mass, with a constant independent of the height scale.
-/

noncomputable section
open Classical

namespace CircularLaw

def profileHighLowParts {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) (H W : ℝ) : Finset ι :=
  Finset.univ.filter (fun q => H ≤ (P.height q : ℝ) ∧ truncatedProfileWeight P d q < W)

theorem profile_high_low_part_small {n : ℕ} (hn : 0 < n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι) {d : ℕ} (hd : 0 < d)
    {H W : ℝ} (hCut : W ≤ H * Real.rpow (d : ℝ) (-1 / 3 : ℝ))
    {q : ι} (hq : q ∈ profileHighLowParts P d H W) :
    q ∈ (profileCutoffParts P d (1 / 3))ᶜ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨hH, hW⟩ := (Finset.mem_filter.mp hq).2
  apply Finset.mem_compl.mpr
  intro hLargeSize
  have hLarge := profileCutoff_is_large P hd (le_refl (1 / 3 : ℝ)) hLargeSize
  have hWeight := profileLargePart_weight_lower P hd q hLarge
  have hLower : H * Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤
      (P.height q : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (Nat.cast_nonneg d) (-1 / 3 : ℝ))
  linarith

theorem profile_high_low_order_bounds {n : ℕ} (hn : 0 < n) {ι : Type*}
    [Fintype ι] (P : RowProfile (Fin n) ι) {d : ℕ} (hd : 0 < d)
    {H W : ℝ} (hH : 0 < H) {q : ι} (hq : q ∈ profileHighLowParts P d H W) :
    ⌊Real.logb 2 (H / d)⌋ ≤ dyadicProfilePartOrder P d q ∧
      dyadicProfilePartOrder P d q ≤ ⌊Real.logb 2 W⌋ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hHeight, hWeight⟩ := (Finset.mem_filter.mp hq).2
  have hLower : H / d ≤ truncatedProfileWeight P d q :=
    (div_le_div_of_nonneg_right hHeight hdR.le).trans (truncatedProfileWeight_height_div_degree_le P hd q)
  exact ⟨Int.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos hH hdR) hLower),
    Int.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (truncatedProfileWeight_pos P hd q) hWeight.le)⟩

theorem profile_high_low_mass_bound {n : ℕ} (hn : 0 < n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι)
    (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) {H W : ℝ} (hH : 0 < H) (hW : 0 < W)
    (hOrder : H / d ≤ W) (hCut : W ≤ H * Real.rpow (d : ℝ) (-1 / 3 : ℝ)) :
    profileSelectedMass P (profileHighLowParts P d H W) ≤
      512 * (Real.logb 2 W - Real.logb 2 (H / d) + 2) *
        Real.rpow (d : ℝ) (-1 / 3 : ℝ) * n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let B := fun i => dyadicProfilePartOrder P d (P.part i)
  let S := Finset.univ.filter (fun i => P.part i ∈ profileHighLowParts P d H W)
  let a := ⌊Real.logb 2 (H / d)⌋
  let b := ⌊Real.logb 2 W⌋
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hab : a ≤ b := Int.floor_mono
    ((Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (div_pos hH hdR) hW).mpr hOrder)
  have hBins : ∀ j : ℤ, ((S.filter (fun i => B i = j)).card : ℝ) ≤
      512 * Real.rpow (d : ℝ) (-1 / 3 : ℝ) * n := by
    intro j
    have hSubset : S.filter (fun i => B i = j) ⊆ Finset.univ.filter
        (fun i => P.part i ∈ (profileCutoffParts P d (1 / 3))ᶜ ∧
          dyadicProfilePartOrder P d (P.part i) = j) := by
      intro i hi
      obtain ⟨hiS, hiB⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        profile_high_low_part_small hn P hd hCut (Finset.mem_filter.mp hiS).2, hiB⟩
    have hBound := profile_small_cutoff_bin P order hGeometry hd (1 / 3) j
    have hCard : ((S.filter (fun i => B i = j)).card : ℝ) ≤
        ((Finset.univ.filter (fun i => P.part i ∈ (profileCutoffParts P d (1 / 3))ᶜ ∧
          dyadicProfilePartOrder P d (P.part i) = j)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset
    exact hCard.trans (by simpa only [neg_div] using hBound)
  have hFilter : S.filter (fun i => a ≤ B i ∧ B i ≤ b) = S := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact profile_high_low_order_bounds hn P hd hH (Finset.mem_filter.mp hi).2
  have hInterval := integer_interval_selected_mass B S hab hBins
  rw [hFilter] at hInterval
  have hLength : (b : ℝ) - a + 1 ≤ Real.logb 2 W - Real.logb 2 (H / d) + 2 := by
    have hLow := Int.sub_one_lt_floor (Real.logb 2 (H / d))
    have hHigh := Int.floor_le (Real.logb 2 W)
    dsimp only [a, b]
    linarith
  rw [profileSelectedMass_eq_coordinate_card]
  change (S.card : ℝ) ≤ _
  exact hInterval.trans (by
    have h := mul_le_mul_of_nonneg_right hLength (show 0 ≤ 512 *
      Real.rpow (d : ℝ) (-1 / 3 : ℝ) * (n : ℝ) from
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) (Nat.cast_nonneg n))
    convert h using 1
    ring)

end CircularLaw
