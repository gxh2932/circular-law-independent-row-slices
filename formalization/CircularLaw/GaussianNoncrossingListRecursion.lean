import CircularLaw.GaussianNoncrossingNegation
import CircularLaw.GaussianWordNoncrossingCounts
import Mathlib.Data.List.TakeDrop

/-!
# First-pair recursion on literal finite Gaussian words

The finite noncrossing decomposition is expressed in terms of list
prefixes and suffixes. This is the word-functional recursion used to
evaluate scalar-shifted moment expansions.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem gaussian_noncrossing_word_count_ofFn {n : ℕ} (b : Fin n → Bool) :
    gaussianNoncrossingWordCount (List.ofFn b) = Fintype.card (GaussianNoncrossingPairings b) := by
  cases n with
  | zero =>
    rw [List.ofFn_zero]
    exact (gaussian_noncrossing_empty_card b).symm
  | succ k =>
    rw [← gaussian_word_mean_count_eq_noncrossing_word_count,
      gaussian_word_mean_count_eq_noncrossing_card]

theorem gaussian_noncrossing_word_count_map_not (w : List Bool) :
    gaussianNoncrossingWordCount (w.map Bool.not) = gaussianNoncrossingWordCount w := by
  conv_lhs => rw [← List.ofFn_get w, List.map_ofFn]
  rw [gaussian_noncrossing_word_count_ofFn]
  change Fintype.card (GaussianNoncrossingPairings (fun i => !(w.get i))) = _
  rw [gaussian_noncrossing_card_negation, ← gaussian_noncrossing_word_count_ofFn, List.ofFn_get]

theorem gaussian_first_interior_list (b : Bool) (w : List Bool) (q : Fin (w.length + 1)) :
    List.ofFn ((b :: w).get ∘ gaussianFirstInteriorMap q) = w.take (q.val - 1) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take]
    have hq := q.isLt
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn, Function.comp_apply, gaussianFirstInteriorMap,
      List.get_eq_getElem, List.getElem_cons_succ, List.getElem_take]

theorem gaussian_first_outer_list (b : Bool) (w : List Bool) (q : Fin (w.length + 1)) :
    List.ofFn ((b :: w).get ∘ gaussianFirstOuterMap q) = w.drop q.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_drop]
  · intro i hi hi'
    simp only [List.getElem_ofFn, Function.comp_apply, gaussianFirstOuterMap,
      List.get_eq_getElem, List.getElem_drop]
    simp only [show q.val + 1 + i = (q.val + i) + 1 by omega, List.getElem_cons_succ]

theorem gaussian_noncrossing_false_first_list (w : List Bool) :
    gaussianNoncrossingWordCount (false :: w) =
      ∑ q : GaussianAdjointPositions (false :: w).get,
        gaussianNoncrossingWordCount (w.take (q.val.val - 1)) *
          gaussianNoncrossingWordCount (w.drop q.val.val) := by
  change Fintype.card (GaussianNoncrossingPairings (false :: w).get) = _
  rw [gaussian_noncrossing_first_pair_card _ (by rfl)]
  apply Finset.sum_congr rfl
  intro q _
  rw [← gaussian_noncrossing_word_count_ofFn, ← gaussian_noncrossing_word_count_ofFn,
    gaussian_first_interior_list, gaussian_first_outer_list]

theorem gaussian_false_first_partner_pos (w : List Bool)
    (q : GaussianAdjointPositions (false :: w).get) : 0 < q.val.val := by
  by_contra h
  have hZero : q.val = 0 := Fin.ext (by change q.val.val = 0; omega)
  have hColor := q.property
  rw [hZero] at hColor
  change false = true at hColor
  exact Bool.noConfusion hColor

def gaussianFalseFirstPartnerEquiv (w : List Bool) :
    GaussianAdjointPositions (false :: w).get ≃ GaussianAdjointPositions w.get where
  toFun q := ⟨⟨q.val.val - 1, by
    have h := q.val.isLt
    simp only [List.length_cons] at h
    have hPos := gaussian_false_first_partner_pos w q
    omega⟩, by
    have hPos := gaussian_false_first_partner_pos w q
    have hIndex : q.val = (⟨q.val.val - 1, by
      have h := q.val.isLt
      simp only [List.length_cons] at h
      omega⟩ : Fin w.length).succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    have hColor := q.property
    rw [hIndex] at hColor
    exact hColor⟩
  invFun q := ⟨q.val.succ, q.property⟩
  left_inv q := by
    apply Subtype.ext
    apply Fin.ext
    have hPos := gaussian_false_first_partner_pos w q
    simp only [Fin.val_succ]
    omega
  right_inv q := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_succ, Nat.add_sub_cancel]

theorem gaussian_noncrossing_false_first_tail (w : List Bool) :
    gaussianNoncrossingWordCount (false :: w) =
      ∑ q : GaussianAdjointPositions w.get,
        gaussianNoncrossingWordCount (w.take q.val.val) *
          gaussianNoncrossingWordCount (w.drop (q.val.val + 1)) := by
  rw [gaussian_noncrossing_false_first_list]
  rw [← (gaussianFalseFirstPartnerEquiv w).symm.sum_comp]
  rfl

theorem gaussian_noncrossing_false_first_sum (w : List Bool) :
    gaussianNoncrossingWordCount (false :: w) =
      ∑ q : Fin w.length, if w.get q = true then
        gaussianNoncrossingWordCount (w.take q.val) *
          gaussianNoncrossingWordCount (w.drop (q.val + 1)) else 0 := by
  rw [gaussian_noncrossing_false_first_tail]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun q : Fin w.length => w.get q = true)
    (Finset.univ.filter (fun q : Fin w.length => w.get q = true))
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun q => gaussianNoncrossingWordCount (w.take q.val) *
      gaussianNoncrossingWordCount (w.drop (q.val + 1)))).symm

theorem gaussian_noncrossing_word_first_sum (b : Bool) (w : List Bool) :
    gaussianNoncrossingWordCount (b :: w) =
      ∑ q : Fin w.length, if w.get q ≠ b then
        gaussianNoncrossingWordCount (w.take q.val) *
          gaussianNoncrossingWordCount (w.drop (q.val + 1)) else 0 := by
  cases b with
  | false =>
    rw [gaussian_noncrossing_false_first_sum]
    apply Finset.sum_congr rfl
    intro q _
    cases w.get q <;> simp
  | true =>
    have h := gaussian_noncrossing_false_first_sum (w.map Bool.not)
    have hHead : gaussianNoncrossingWordCount (false :: w.map Bool.not) =
        gaussianNoncrossingWordCount (true :: w) := by
      simpa only [List.map_cons, Bool.not_true] using
        gaussian_noncrossing_word_count_map_not (true :: w)
    rw [hHead] at h
    refine h.trans ?_
    rw [← (finCongr (show (w.map Bool.not).length = w.length from
      List.length_map Bool.not)).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    simp [List.get_eq_getElem, ← List.map_take, ← List.map_drop,
      gaussian_noncrossing_word_count_map_not]

end CircularLaw
