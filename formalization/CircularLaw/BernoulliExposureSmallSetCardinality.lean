import CircularLaw.BernoulliSmallSetFamilyExpansion

/-!
# Actual small-set expansion for square and rectangular exposures

Both laws use the original ambient degree and threshold. In a matrix
with one extra column, the two subset families give a factor of two.
No expansion event is inherited by deleting rows from a larger matrix.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_ambient_square_small_cardinality_expansion_failure
    {N M ell : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw M p hp).real {x | ∃ S : Finset (Fin M), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤ Real.exp (-d * ell / 16) := by
  exact bernoulli_small_set_family_expansion_source_range hN hMN hell hRows le_rfl p hp hDegree
    hd hSmall hβ hβOne (Function.Embedding.refl _) id
    (fun _ hT => hT) (fun T hT => by rw [id_eq, bernoulli_unique_inside_rows_identity]; exact hT)

theorem bernoulli_ambient_rectangular_small_cardinality_expansion_failure
    {N M ell : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real {x |
      ∃ S : Finset (Fin (M + 1)), S.card = ell ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β S).card : ℝ) <
          sourceGraphExpansion N d ell} ≤ 2 * Real.exp (-d * ell / 16) := by
  let E₀ := {x : Fin M × Fin (M + 1) → Bool | ∃ T : Finset (Fin M), T.card = ell ∧
    ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β
      (T.image Fin.castSucc)).card : ℝ) < sourceGraphExpansion N d ell}
  let E₁ := {x : Fin M × Fin (M + 1) → Bool | ∃ T : Finset (Fin M), T.card = ell - 1 ∧
    ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β
      (insert (Fin.last M) (T.image Fin.castSucc))).card : ℝ) < sourceGraphExpansion N d ell}
  have h₀ : (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real E₀ ≤ Real.exp (-d * ell / 16) :=
    bernoulli_small_set_family_expansion_source_range hN hMN hell hRows le_rfl p hp hDegree
      hd hSmall hβ hβOne Fin.castSuccEmb (fun T => T.image Fin.castSucc)
      (fun T hT => (bernoulli_rectangular_image_card T).trans hT)
      (fun T hT => by rw [bernoulli_rectangular_inside_rows_image]; exact hT)
  have h₁ : (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real E₁ ≤ Real.exp (-d * ell / 16) :=
    bernoulli_small_set_family_expansion_source_range hN hMN hell hRows (Nat.sub_le ell 1) p hp hDegree
      hd hSmall hβ hβOne Fin.castSuccEmb (fun T => insert (Fin.last M) (T.image Fin.castSucc))
      (fun T hT => by rw [bernoulli_rectangular_insert_last_card, hT]; omega)
      (fun T hT => by rw [bernoulli_rectangular_inside_rows_insert_last]; exact hT)
  have hSubset : {x : Fin M × Fin (M + 1) → Bool | ∃ S : Finset (Fin (M + 1)), S.card = ell ∧
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β S).card : ℝ) <
        sourceGraphExpansion N d ell} ⊆ E₀ ∪ E₁ := by
    rintro x ⟨S, hS, hBad⟩
    let T := bernoulliUniqueInsideRows Fin.castSuccEmb S
    have hDecomp := bernoulli_rectangular_column_set_decomposition S
    by_cases hLast : Fin.last M ∈ S
    · rw [if_pos hLast] at hDecomp
      have hTc : T.card = ell - 1 := by
        have h := bernoulli_rectangular_inside_card_of_last_mem S hLast
        dsimp only [T]
        omega
      right
      refine ⟨T, hTc, ?_⟩
      change ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β
        (insert (Fin.last M) (T.image Fin.castSucc))).card : ℝ) < sourceGraphExpansion N d ell
      dsimp only [T]
      rw [← hDecomp]
      exact hBad
    · rw [if_neg hLast] at hDecomp
      have hTc : T.card = ell := (bernoulli_rectangular_inside_card_of_last_not_mem S hLast).trans hS
      left
      refine ⟨T, hTc, ?_⟩
      change ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β
        (T.image Fin.castSucc)).card : ℝ) < sourceGraphExpansion N d ell
      dsimp only [T]
      rw [← hDecomp]
      exact hBad
  calc
    _ ≤ (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real (E₀ ∪ E₁) :=
      measureReal_mono hSubset (measure_ne_top _ _)
    _ ≤ (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real E₀ +
        (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real E₁ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end CircularLaw
