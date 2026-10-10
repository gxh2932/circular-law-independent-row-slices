import CircularLaw.ProfileHighHeightBins
import CircularLaw.SourceRefinementFamilies
import CircularLaw.CanonicalProfile

/-!
# Actual high-height coordinate mass and upper probability tails

The tagged high-height union equals the high-height part mass in the
ordered profile. Removing its coordinates below a weight threshold
leaves an upper tail for the literal dyadic weight order.
-/

noncomputable section
open Classical

namespace CircularLaw

def profileHighParts {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (H : ℝ) : Finset ι :=
  Finset.univ.filter (fun q => H ≤ (P.height q : ℝ))

theorem orderedCanonical_coordinate_height {n : ℕ} (y : Fin n → ℂ) (η : ℝ) (i : Fin n) :
    (orderedCanonicalRowProfile y η).height ((orderedCanonicalRowProfile y η).part i) =
      (taggedValues y η (canonicalCoordinateLabel y η i).val).card := by
  simp only [orderedCanonicalRowProfile, canonicalRowProfile, Equiv.apply_symm_apply]

theorem orderedCanonical_highHeight_mass {n : ℕ} (y : Fin n → ℂ) (η H : ℝ) :
    profileSelectedMass (orderedCanonicalRowProfile y η) (profileHighParts (orderedCanonicalRowProfile y η) H) =
      (highHeightCoordinates y η H).card := by
  rw [profileSelectedMass_eq_coordinate_card]
  apply congrArg (fun S : Finset (Fin n) => (S.card : ℝ))
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, profileHighParts]
  rw [orderedCanonical_coordinate_height]
  constructor
  · intro hHeight
    exact Finset.mem_biUnion.mpr ⟨(canonicalCoordinateLabel y η i).val,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeight⟩, canonicalCoordinateLabel_mem y η i⟩
  · intro hi
    obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
    let q' : CanonicalLabel y η := ⟨q, ⟨i, hiq⟩⟩
    have hLabel : canonicalCoordinateLabel y η i = q' :=
      (canonicalCoordinateLabel_eq_iff y η i q').mpr hiq
    rw [hLabel]
    exact (Finset.mem_filter.mp hq).2

theorem profile_high_height_upper_tail {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : RowProfile (Fin n) ι) (d : ℕ)
    (H : ℝ) {W : ℝ} (hW : 0 < W) :
    (profileSelectedMass P (profileHighParts P H) - profileSelectedMass P (profileHighLowParts P d H W)) / n ≤
      uniformProbability (fun i => ⌊Real.logb 2 W⌋ ≤ dyadicProfilePartOrder P d (P.part i)) := by
  let A := Finset.univ.filter (fun i => P.part i ∈ profileHighParts P H)
  let S := Finset.univ.filter (fun i => P.part i ∈ profileHighLowParts P d H W)
  let T := Finset.univ.filter (fun i => ⌊Real.logb 2 W⌋ ≤ dyadicProfilePartOrder P d (P.part i))
  have hSubset : A ⊆ S ∪ T := by
    intro i hi
    by_cases hiS : i ∈ S
    · exact Finset.mem_union_left _ hiS
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hHeight : H ≤ (P.height (P.part i) : ℝ) :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2
      have hWeight : W ≤ truncatedProfileWeight P d (P.part i) := by
        by_contra h
        exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeight, lt_of_not_ge h⟩⟩)
      exact Int.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hW hWeight)
  have hCard : A.card ≤ S.card + T.card :=
    (Finset.card_le_card hSubset).trans (Finset.card_union_le S T)
  have hCardR : (A.card : ℝ) ≤ S.card + T.card := by exact_mod_cast hCard
  rw [profileSelectedMass_eq_coordinate_card, profileSelectedMass_eq_coordinate_card]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin]
  change ((A.card : ℝ) - S.card) / n ≤ (T.card : ℝ) / n
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

end CircularLaw
