import CircularLaw.ShiftedGraphBudgets

/-!
# A coordinate gap forces a spread matrix image

The proof splits the actual vector into head, middle and tail. Rows with
a large row mass or a middle entry (including the shifted diagonal) are
removed. Every remaining unique-neighbourhood row has a large image.
The quantitative conclusion uses actual row and column support counts.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def uniqueNeighbourhoodGoodRows {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β L : ℝ) (S S' : Finset ι) : Finset ρ :=
  matrixUniqueNeighbourhood A e β S \
    (matrixHeavyRows A L ∪ shiftedMiddleTouchedRows A e (coordinateMiddleSet S S'))

theorem coordinate_restricted_vector_three_parts {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (S S' : Finset ι) (hS : S ⊆ S') :
    coordinateRestrictedVector v S + coordinateRestrictedVector v (coordinateMiddleSet S S') +
      coordinateRestrictedVector v S'ᶜ = v := by
  classical
  ext j
  by_cases hj : j ∈ S
  · simp [coordinateMiddleSet, coordinate_restricted_vector_apply, hj, hS hj]
  · by_cases hj' : j ∈ S'
    · simp [coordinateMiddleSet, coordinate_restricted_vector_apply, hj, hj']
    · simp [coordinateMiddleSet, coordinate_restricted_vector_apply, hj, hj']

theorem unique_neighbourhood_good_rows_mem {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β L : ℝ) (S S' : Finset ι) (i : ρ) :
    i ∈ uniqueNeighbourhoodGoodRows A e β L S S' ↔
      i ∈ matrixUniqueNeighbourhood A e β S ∧ i ∉ matrixHeavyRows A L ∧
        i ∉ shiftedMiddleTouchedRows A e (coordinateMiddleSet S S') := by
  simp only [uniqueNeighbourhoodGoodRows, Finset.mem_sdiff, Finset.mem_union,
    not_or]

theorem unique_neighbourhood_good_rows_card_budget {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β L : ℝ) (S S' : Finset ι) :
    (matrixUniqueNeighbourhood A e β S).card ≤
      (uniqueNeighbourhoodGoodRows A e β L S S').card +
        (matrixHeavyRows A L).card +
          ∑ j ∈ coordinateMiddleSet S S', ((matrixColumnSupport A j).card + 1) := by
  classical
  have hDiff : (matrixUniqueNeighbourhood A e β S).card ≤
      (uniqueNeighbourhoodGoodRows A e β L S S').card +
        (matrixHeavyRows A L ∪ shiftedMiddleTouchedRows A e (coordinateMiddleSet S S')).card :=
    Finset.card_le_card_sdiff_add_card
  have hUnion := Finset.card_union_le (s := matrixHeavyRows A L)
    (t := shiftedMiddleTouchedRows A e (coordinateMiddleSet S S'))
  have hMiddle := shifted_middle_touched_rows_card_le A e (coordinateMiddleSet S S')
  omega

theorem unique_neighbourhood_good_row_image_lower {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ) (v : EuclideanSpace ℂ ι)
    (S S' : Finset ι) (hS : S ⊆ S') {β L a q d : ℝ}
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hq : 0 ≤ q) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hHead : ∀ j ∈ S, a ≤ ‖v j‖)
    (hTail : ∀ j ∈ S'ᶜ, ‖v j‖ ≤ q * a) (hGap : (L + d) * q ≤ β / 2)
    (i : ρ) (hi : i ∈ uniqueNeighbourhoodGoodRows A e β L S S') :
    β * a / 2 ≤ ‖(diagonalEmbeddedShift A e z).toEuclideanLin v i‖ := by
  obtain ⟨hUnique, hLight, hUntouched⟩ :=
    (unique_neighbourhood_good_rows_mem A e β L S S' i).mp hi
  have hHeadLower := unique_neighbourhood_restricted_image_lower
    A e z v S hβ ha hz hHead i hUnique
  have hMiddle := shifted_middle_restricted_image_zero A e z v (coordinateMiddleSet S S') i hUntouched
  have hRow := matrix_heavy_rows_complement A L i hLight
  have hTailUpper := shifted_restricted_image_norm_le A e z v S'ᶜ
    (mul_nonneg hq ha) hTail i
  have hSmall : ‖(diagonalEmbeddedShift A e z).toEuclideanLin
      (coordinateRestrictedVector v S'ᶜ) i‖ ≤ β * a / 2 := by
    calc
      _ ≤ (matrixRowL1Mass A i + ‖z‖) * (q * a) := hTailUpper
      _ ≤ (L + d) * (q * a) :=
        mul_le_mul_of_nonneg_right (add_le_add hRow hzUpper) (mul_nonneg hq ha)
      _ = ((L + d) * q) * a := by ring
      _ ≤ (β / 2) * a := mul_le_mul_of_nonneg_right hGap ha
      _ = β * a / 2 := by ring
  have hImage : (diagonalEmbeddedShift A e z).toEuclideanLin v i =
      (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i +
        (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S'ᶜ) i := by
    have h := congrArg (fun w => (diagonalEmbeddedShift A e z).toEuclideanLin w i)
      (coordinate_restricted_vector_three_parts v S S' hS)
    simpa only [map_add, PiLp.add_apply, hMiddle, add_zero] using h.symm
  have hTriangle :
      ‖(diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i‖ ≤
        ‖(diagonalEmbeddedShift A e z).toEuclideanLin v i‖ +
          ‖(diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S'ᶜ) i‖ := by
    have hEq : (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S) i =
        (diagonalEmbeddedShift A e z).toEuclideanLin v i -
          (diagonalEmbeddedShift A e z).toEuclideanLin (coordinateRestrictedVector v S'ᶜ) i := by
      rw [hImage]
      abel
    rw [hEq]
    exact norm_sub_le _ _
  linarith

theorem unique_neighbourhood_good_rows_subset_image_spread {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ) (v : EuclideanSpace ℂ ι)
    (S S' : Finset ι) (hS : S ⊆ S') {β L a q d : ℝ}
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hq : 0 ≤ q) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hHead : ∀ j ∈ S, a ≤ ‖v j‖)
    (hTail : ∀ j ∈ S'ᶜ, ‖v j‖ ≤ q * a) (hGap : (L + d) * q ≤ β / 2) :
    uniqueNeighbourhoodGoodRows A e β L S S' ⊆
      coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v) (β * a / 2) := by
  intro i hi
  exact (coordinate_spread_set_mem _ _ i).mpr
    (unique_neighbourhood_good_row_image_lower A e z v S S' hS
      hβ ha hq hz hzUpper hHead hTail hGap i hi)

theorem unique_neighbourhood_image_spread_of_budgets {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (z : ℂ) (v : EuclideanSpace ℂ ι)
    (S S' : Finset ι) (hS : S ⊆ S') {β L a q d b : ℝ}
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hq : 0 ≤ q) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hHead : ∀ j ∈ S, a ≤ ‖v j‖)
    (hTail : ∀ j ∈ S'ᶜ, ‖v j‖ ≤ q * a) (hGap : (L + d) * q ≤ β / 2)
    (hUnique : b ≤ ((matrixUniqueNeighbourhood A e β S).card : ℝ))
    (hHeavy : ((matrixHeavyRows A L).card : ℝ) ≤ b / 4)
    (hColumns : ((∑ j ∈ coordinateMiddleSet S S', ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) ≤ b / 4) :
    b / 2 ≤ ((coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v)
      (β * a / 2)).card : ℝ) := by
  have hBudget := unique_neighbourhood_good_rows_card_budget A e β L S S'
  have hBudgetReal : ((matrixUniqueNeighbourhood A e β S).card : ℝ) ≤
      ((uniqueNeighbourhoodGoodRows A e β L S S').card : ℝ) +
        ((matrixHeavyRows A L).card : ℝ) +
          (∑ j ∈ coordinateMiddleSet S S', ((matrixColumnSupport A j).card + 1) : ℕ) := by
    exact_mod_cast hBudget
  have hSpread : ((uniqueNeighbourhoodGoodRows A e β L S S').card : ℝ) ≤
      ((coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v)
        (β * a / 2)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (unique_neighbourhood_good_rows_subset_image_spread A e z v S S' hS
        hβ ha hq hz hzUpper hHead hTail hGap)
  linarith

end CircularLaw
