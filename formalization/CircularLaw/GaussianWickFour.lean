import CircularLaw.GaussianEntryProducts
import Mathlib.Data.List.Perm.Basic

/-!
# Four-entry expectations, retaining coincident indices

The two possible direct-to-conjugate pairings contribute separately.
When all four indices coincide, both contribute, giving the actual
fourth moment two. No distinct-index assumption is imposed.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem two_word_counts_eq_iff {ι : Type*} [DecidableEq ι] (i j k l : ι) :
    (∀ t, [i, k].count t = [j, l].count t) ↔
      (i = j ∧ k = l) ∨ (i = l ∧ k = j) := by
  constructor
  · intro h
    have hp : ([i, k] : List ι).Perm [j, l] := List.perm_iff_count.mpr h
    have hi : i = j ∨ i = l := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hp.subset (by simp)
    rcases hi with hij | hil
    · subst j
      exact Or.inl ⟨rfl, by simpa using hp.cons_inv⟩
    · subst l
      have hp' : ([i, k] : List ι).Perm [i, j] := hp.trans (List.Perm.swap i j [])
      exact Or.inr ⟨rfl, by simpa using hp'.cons_inv⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact fun _ => rfl
    · exact List.perm_iff_count.mp (List.Perm.swap _ _ [])

theorem two_word_factorial_product {ι : Type*} [Fintype ι] [DecidableEq ι] (i k : ι) :
    (∏ t, (([i, k].count t).factorial : ℂ)) = if i = k then 2 else 1 := by
  by_cases hik : i = k
  · subst k
    have hFactor (t : ι) : (([i, i].count t).factorial : ℂ) =
        if t = i then 2 else 1 := by
      by_cases h : t = i
      · subst t
        norm_num
      · simp [h, Ne.symm h]
    simp [hFactor]
  · have hFactor (t : ι) : (([i, k].count t).factorial : ℂ) = 1 := by
      by_cases hti : t = i
      · subst t
        simp [hik]
      · by_cases htk : t = k
        · subst t
          simp [hik, Ne.symm hik]
        · simp [Ne.symm hti, Ne.symm htk]
    simp [hFactor, hik]

theorem gaussian_entry_wick_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    (∫ x : ι → ℂ, x i * star (x j) * x k * star (x l)
      ∂standardComplexGaussianProductLaw ι) =
      (if i = j ∧ k = l then 1 else 0) + (if i = l ∧ k = j then 1 else 0) := by
  have hWord (x : ι → ℂ) : x i * star (x j) * x k * star (x l) =
      gaussianEntryWord [i, k] [j, l] x := by
    simp only [gaussianEntryWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    ring
  simp only [hWord, gaussian_entry_word_integral, two_word_factorial_product]
  simp only [two_word_counts_eq_iff]
  by_cases hA : i = j ∧ k = l
  · by_cases hB : i = l ∧ k = j
    · have hik : i = k := hA.1.trans hB.2.symm
      rw [if_pos (Or.inl hA), if_pos hik, if_pos hA, if_pos hB]
      norm_num
    · have hik : i ≠ k := by
        rintro rfl
        exact hB ⟨hA.2, hA.1⟩
      rw [if_pos (Or.inl hA), if_neg hik, if_pos hA, if_neg hB, add_zero]
  · by_cases hB : i = l ∧ k = j
    · have hik : i ≠ k := by
        rintro rfl
        exact hA ⟨hB.2, hB.1⟩
      rw [if_pos (Or.inr hB), if_neg hik, if_neg hA, if_pos hB, zero_add]
    · rw [if_neg (not_or.mpr ⟨hA, hB⟩), if_neg hA, if_neg hB, zero_add]

theorem gaussian_entry_wick_four_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    Integrable (fun x : ι → ℂ => x i * star (x j) * x k * star (x l))
      (standardComplexGaussianProductLaw ι) := by
  have hWord : (fun x : ι → ℂ => x i * star (x j) * x k * star (x l)) =
      gaussianEntryWord [i, k] [j, l] := by
    funext x
    simp only [gaussianEntryWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    ring
  rw [hWord]
  exact gaussian_entry_word_integrable _ _

end CircularLaw
