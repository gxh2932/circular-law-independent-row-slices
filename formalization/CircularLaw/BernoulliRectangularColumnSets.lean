import CircularLaw.BernoulliAmbientSmallSetExpansion
import Mathlib.Data.Fin.Embedding

/-!
# The two kinds of column sets in a one-column rectangular exposure

Sets either lie in the diagonal image of the rows or contain the final
unmatched column. The exact diagonal-row counts and the finite set
decomposition justify counting these two families separately.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_rectangular_last_not_mem_image {M : ℕ} (T : Finset (Fin M)) :
    Fin.last M ∉ T.image Fin.castSucc := by
  rintro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact Fin.castSucc_ne_last i hi

theorem bernoulli_rectangular_inside_rows_image {M : ℕ} (T : Finset (Fin M)) :
    bernoulliUniqueInsideRows Fin.castSuccEmb (T.image Fin.castSucc) = T := by
  ext i
  simp [bernoulliUniqueInsideRows, Finset.mem_image]

theorem bernoulli_rectangular_inside_rows_insert_last {M : ℕ} (T : Finset (Fin M)) :
    bernoulliUniqueInsideRows Fin.castSuccEmb (insert (Fin.last M) (T.image Fin.castSucc)) = T := by
  ext i
  simp [bernoulliUniqueInsideRows, Finset.mem_image, Fin.castSucc_ne_last]

theorem bernoulli_rectangular_image_card {M : ℕ} (T : Finset (Fin M)) :
    (T.image Fin.castSucc).card = T.card :=
  Finset.card_image_of_injective _ (Fin.castSucc_injective M)

theorem bernoulli_rectangular_insert_last_card {M : ℕ} (T : Finset (Fin M)) :
    (insert (Fin.last M) (T.image Fin.castSucc)).card = T.card + 1 := by
  rw [Finset.card_insert_of_notMem (bernoulli_rectangular_last_not_mem_image T),
    bernoulli_rectangular_image_card]

theorem bernoulli_rectangular_column_set_decomposition {M : ℕ} (S : Finset (Fin (M + 1))) :
    S = if Fin.last M ∈ S then
      insert (Fin.last M) ((bernoulliUniqueInsideRows Fin.castSuccEmb S).image Fin.castSucc)
    else (bernoulliUniqueInsideRows Fin.castSuccEmb S).image Fin.castSucc := by
  ext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · by_cases hLast : Fin.last M ∈ S <;>
      simp [hLast, bernoulliUniqueInsideRows, Finset.mem_image, Fin.castSucc_ne_last]
  · by_cases hLast : Fin.last M ∈ S <;>
      simp [hLast]

theorem bernoulli_rectangular_inside_card_of_last_not_mem {M : ℕ}
    (S : Finset (Fin (M + 1))) (hLast : Fin.last M ∉ S) :
    (bernoulliUniqueInsideRows Fin.castSuccEmb S).card = S.card := by
  have h := bernoulli_rectangular_column_set_decomposition S
  rw [if_neg hLast] at h
  conv_rhs => rw [h]
  rw [bernoulli_rectangular_image_card]

theorem bernoulli_rectangular_inside_card_of_last_mem {M : ℕ}
    (S : Finset (Fin (M + 1))) (hLast : Fin.last M ∈ S) :
    (bernoulliUniqueInsideRows Fin.castSuccEmb S).card + 1 = S.card := by
  have h := bernoulli_rectangular_column_set_decomposition S
  rw [if_pos hLast] at h
  conv_rhs => rw [h]
  rw [bernoulli_rectangular_insert_last_card]

end CircularLaw
