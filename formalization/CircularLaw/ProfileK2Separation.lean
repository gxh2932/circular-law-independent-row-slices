import CircularLaw.ProfileCutoffProduct
import CircularLaw.IntegerOrderQuantiles

/-!
# The small-part weight-order branch

Canonical creation-order geometry supplies the source bound of 512
times the cutoff for each small-part weight bin. Actual coordinate
quantiles then give lower and upper probability tails and an integer
gap estimate. No alternate weight bins are introduced.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem profile_small_cutoff_bin {n : ℕ} [NeZero n] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι)
    (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (κ : ℝ) (b : ℤ) :
    ((Finset.univ.filter (fun i => P.part i ∈ (profileCutoffParts P d κ)ᶜ ∧
      dyadicProfilePartOrder P d (P.part i) = b)).card : ℝ) ≤
        512 * Real.rpow (d : ℝ) (-κ) * n := by
  let J := dyadicProfileBinParts P d b ∩ (profileCutoffParts P d κ)ᶜ
  have hSubset : J ⊆ dyadicProfileBinParts P d b := Finset.inter_subset_left
  have hSmall : ∀ q ∈ J, (profilePartSize P q : ℝ) < Real.rpow (d : ℝ) (-κ) * Fintype.card (Fin n) := by
    intro q hq
    have hNot := Finset.mem_compl.mp (Finset.mem_inter.mp hq).2
    simpa only [profileCutoffParts, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hNot
  have hBound := profile_small_bin_sum P order hGeometry hd b J hSubset
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) _) (Nat.cast_nonneg _)) hSmall
  have hMassBound : profileSelectedMass P J ≤ 512 * Real.rpow (d : ℝ) (-κ) * n := by
    simpa only [profileSelectedMass, Nat.cast_sum, Fintype.card_fin, mul_assoc] using hBound
  rw [profileSelectedMass_eq_coordinate_card] at hMassBound
  have hSet : Finset.univ.filter (fun i => P.part i ∈ (profileCutoffParts P d κ)ᶜ ∧
      dyadicProfilePartOrder P d (P.part i) = b) =
      Finset.univ.filter (fun i => P.part i ∈ J) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, J, Finset.mem_inter,
      dyadicProfileBinParts]
    tauto
  calc
    _ = ((Finset.univ.filter (fun i => P.part i ∈ J)).card : ℝ) := congrArg (fun S : Finset (Fin n) => (S.card : ℝ)) hSet
    _ ≤ _ := hMassBound

theorem profile_K2_quantile_separation {n : ℕ} (hn : 4 ≤ n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι)
    (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (κ : ℝ) {R : ℝ} (hR : 0 < R) (hRn : R ≤ n)
    (hSmall : R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ) :
    ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
      (R / 16) / n ≤ uniformProbability (fun i => dyadicProfilePartOrder P d (P.part i) ≤ b₁) ∧
      (R / 16) / n ≤ uniformProbability (fun i => b₂ ≤ dyadicProfilePartOrder P d (P.part i)) ∧
      R / 8 ≤ ((b₂ : ℝ) - b₁ + 1) * (512 * Real.rpow (d : ℝ) (-κ) * n) := by
  letI : NeZero n := ⟨by omega⟩
  let B := fun i => dyadicProfilePartOrder P d (P.part i)
  let S := Finset.univ.filter (fun i => P.part i ∈ (profileCutoffParts P d κ)ᶜ)
  have hSmallS : R / 4 ≤ (S.card : ℝ) := by
    rw [profileSelectedMass_eq_coordinate_card] at hSmall
    exact hSmall
  have hBins : ∀ b : ℤ, ((S.filter (fun i => B i = b)).card : ℝ) ≤
      512 * Real.rpow (d : ℝ) (-κ) * n := by
    intro b
    have h := profile_small_cutoff_bin P order hGeometry hd κ b
    simpa only [S, B, Finset.filter_filter] using h
  obtain ⟨b₁, b₂, hOrder, hLow, hHigh, hGap⟩ := integer_order_small_mass_quantiles hn B S hR hRn hSmallS hBins
  refine ⟨b₁, b₂, hOrder, ?_, ?_, hGap⟩
  · simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hLow (Nat.cast_nonneg n)
  · simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hHigh (Nat.cast_nonneg n)

end CircularLaw
