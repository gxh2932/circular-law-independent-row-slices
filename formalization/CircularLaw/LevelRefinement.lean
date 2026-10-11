import CircularLaw.ApproximationRefinement
import CircularLaw.LevelSliceCounts

/-!
# Majority levels under refinement

Outside the source shrinking-coordinate set, a coarse level has exactly
one finer level of size greater than half its own size. The value map is
therefore a bijection on the represented majority levels. Selected levels
survive at the preceding order, and their prefix masses transfer with
the source factor eight. All level sets and counts are literal finite
coordinate sets, rather than assumptions about an abstract partition.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def shrinkingCoordinates {n : ℕ} (fine coarse : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2 * (initialLevel fine (fine i)).card ≤
    (initialLevel coarse (coarse i)).card)

def nonshrinkingCoordinates {n : ℕ} (fine coarse : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (initialLevel coarse (coarse i)).card <
    2 * (initialLevel fine (fine i)).card)

def nonshrinkingFineValues {n : ℕ} (fine coarse : Fin n → ℂ) : Finset ℂ :=
  (nonshrinkingCoordinates fine coarse).image fine

def nonshrinkingCoarseValues {n : ℕ} (fine coarse : Fin n → ℂ) : Finset ℂ :=
  (nonshrinkingCoordinates fine coarse).image coarse

theorem nonshrinkingCoordinates_eq_compl {n : ℕ} (fine coarse : Fin n → ℂ) :
    nonshrinkingCoordinates fine coarse = Finset.univ \ shrinkingCoordinates fine coarse := by
  ext i
  simp only [nonshrinkingCoordinates, shrinkingCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff, not_le]

theorem initialLevel_disjoint_values {n : ℕ} (y : Fin n → ℂ) {z w : ℂ}
    (h : z ≠ w) : Disjoint (initialLevel y z) (initialLevel y w) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact h ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem refined_initialLevel_subset {n : ℕ} (fine coarse : Fin n → ℂ) (π : ℂ → ℂ)
    (h : ∀ i, coarse i = π (fine i)) (i : Fin n) :
    initialLevel fine (fine i) ⊆ initialLevel coarse (coarse i) := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ j, ?_⟩
  rw [h j, h i, (Finset.mem_filter.mp hj).2]

theorem nonshrinking_same_coarse_eq_fine {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) {i j : Fin n}
    (hi : i ∈ nonshrinkingCoordinates fine coarse)
    (hj : j ∈ nonshrinkingCoordinates fine coarse) (hij : coarse i = coarse j) :
    fine i = fine j := by
  by_contra hNe
  have hDisjoint := initialLevel_disjoint_values fine hNe
  have hSub : initialLevel fine (fine i) ∪ initialLevel fine (fine j) ⊆
      initialLevel coarse (coarse i) := by
    apply Finset.union_subset
    · exact refined_initialLevel_subset fine coarse π h i
    · rw [hij]
      exact refined_initialLevel_subset fine coarse π h j
  have hCount := Finset.card_le_card hSub
  rw [Finset.card_union_of_disjoint hDisjoint] at hCount
  have hI := (Finset.mem_filter.mp hi).2
  have hJ := (Finset.mem_filter.mp hj).2
  rw [← hij] at hJ
  omega

theorem nonshrinkingValueMap_injective {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) :
    Set.InjOn π (nonshrinkingFineValues fine coarse) := by
  intro z hz w hw hzw
  change z ∈ (nonshrinkingCoordinates fine coarse).image fine at hz
  change w ∈ (nonshrinkingCoordinates fine coarse).image fine at hw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  exact nonshrinking_same_coarse_eq_fine fine coarse π h hi hj (by
    rw [h i, h j]
    exact hzw)

theorem nonshrinkingFineValues_image {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) :
    (nonshrinkingFineValues fine coarse).image π = nonshrinkingCoarseValues fine coarse := by
  unfold nonshrinkingFineValues nonshrinkingCoarseValues
  rw [Finset.image_image]
  congr 1
  funext i
  exact (h i).symm

theorem nonshrinkingValues_card_eq {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) :
    (nonshrinkingFineValues fine coarse).card = (nonshrinkingCoarseValues fine coarse).card := by
  rw [← nonshrinkingFineValues_image fine coarse π h,
    Finset.card_image_of_injOn (nonshrinkingValueMap_injective fine coarse π h)]

theorem nonshrinkingValue_majority {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) {z : ℂ}
    (hz : z ∈ nonshrinkingFineValues fine coarse) :
    (initialLevel coarse (π z)).card < 2 * (initialLevel fine z).card := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  rw [← h i]
  exact (Finset.mem_filter.mp hi).2

theorem nonshrinkingRepresentedValues_card_le {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) (j : ℕ) :
    ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card ≤
      ((nonshrinkingFineValues fine coarse) ∩ representedValues fine (j - 1)).card := by
  have hSub : (nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j ⊆
      (((nonshrinkingFineValues fine coarse) ∩ representedValues fine (j - 1)).image π) := by
    intro z hz
    obtain ⟨hzGood, hzRep⟩ := Finset.mem_inter.mp hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzGood
    have hFine := selectedLevel_majority_previous
      (initialLevel coarse (coarse i)) (initialLevel fine (fine i)) j
      (Finset.mem_filter.mp hi).2 ((selectedLevelAt_nonempty_mem coarse j _).mpr hzRep)
    apply Finset.mem_image.mpr
    refine ⟨fine i, Finset.mem_inter.mpr ⟨?_, ?_⟩, (h i).symm⟩
    · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · exact (selectedLevelAt_nonempty_mem fine (j - 1) _).mp hFine
  exact (Finset.card_le_card hSub).trans (Finset.card_image_le)

def levelPrefixCoordinates {n : ℕ} (y : Fin n → ℂ) (A : Finset ℂ) (J : ℕ) :
    Finset (Fin n) := A.biUnion (fun z => selectedLevelPrefix (initialLevel y z) J)

theorem selectedLevelPrefix_subset {α : Type*} [LinearOrder α] (s : Finset α) (J : ℕ) :
    selectedLevelPrefix s J ⊆ s := by
  intro i hi
  obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
  exact levelRemainder_subset s j (orderChunk_subset _ _ hij)

theorem levelPrefixCoordinates_card {n : ℕ} (y : Fin n → ℂ) (A : Finset ℂ) (J : ℕ) :
    (levelPrefixCoordinates y A J).card =
      ∑ z ∈ A, (selectedLevelPrefix (initialLevel y z) J).card := by
  apply Finset.card_biUnion
  intro z hz w hw hzw
  exact (initialLevel_disjoint_values y hzw).mono
    (selectedLevelPrefix_subset _ _) (selectedLevelPrefix_subset _ _)

theorem nonshrinkingPrefix_mass_transfer {n : ℕ} (fine coarse : Fin n → ℂ)
    (π : ℂ → ℂ) (h : ∀ i, coarse i = π (fine i)) (J : ℕ) :
    (levelPrefixCoordinates coarse (nonshrinkingCoarseValues fine coarse) (J + 1)).card ≤
      8 * (levelPrefixCoordinates fine (nonshrinkingFineValues fine coarse) (J - 1 + 1)).card := by
  rw [levelPrefixCoordinates_card, levelPrefixCoordinates_card,
    ← nonshrinkingFineValues_image fine coarse π h,
    Finset.sum_image (nonshrinkingValueMap_injective fine coarse π h), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact selectedLevelPrefix_majority_card (initialLevel coarse (π z)) (initialLevel fine z) J
    (nonshrinkingValue_majority fine coarse π h hz)

theorem canonicalApprox_pow_nonshrinkingValues_card_eq {n d : ℕ} (hd : 0 < d)
    (u : ℕ) (x : Fin n → ℂ) :
    (nonshrinkingFineValues (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      (fun i => canonicalApprox (d ^ u) (x i))).card =
    (nonshrinkingCoarseValues (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      (fun i => canonicalApprox (d ^ u) (x i))).card :=
  nonshrinkingValues_card_eq _ _ (canonicalApprox (d ^ u))
    (fun i => (canonicalApprox_pow_refinement hd u (x i)).symm)

theorem canonicalApprox_pow_nonshrinkingPrefix_mass_transfer {n d : ℕ} (hd : 0 < d)
    (u : ℕ) (x : Fin n → ℂ) (J : ℕ) :
    (levelPrefixCoordinates (fun i => canonicalApprox (d ^ u) (x i))
      (nonshrinkingCoarseValues (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (fun i => canonicalApprox (d ^ u) (x i))) (J + 1)).card ≤
    8 * (levelPrefixCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      (nonshrinkingFineValues (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (fun i => canonicalApprox (d ^ u) (x i))) (J - 1 + 1)).card :=
  nonshrinkingPrefix_mass_transfer _ _ (canonicalApprox (d ^ u))
    (fun i => (canonicalApprox_pow_refinement hd u (x i)).symm) J

end CircularLaw
