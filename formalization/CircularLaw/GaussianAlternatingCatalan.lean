import CircularLaw.GaussianAlternatingWords
import Mathlib.Combinatorics.Enumerative.Catalan

/-!
# Alternating Gaussian word counts are Catalan numbers

The exact first-pair equivalence gives the Catalan convolution. Parity
parametrizes every first adjoint partner and fixes both smaller lengths.
This identifies the actual limiting normalized word means at every order.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_alternating_adjoint_symm_value (n : ℕ) (a : Fin (n / 2)) :
    ((gaussianAlternatingAdjointEquiv n).symm a).val.val = 2 * a.val + 1 := rfl

theorem gaussian_alternating_first_recurrence (k : ℕ) :
    gaussianAlternatingNoncrossingCount (k + 1) =
      ∑ a : Fin ((k + 1) / 2), gaussianAlternatingNoncrossingCount (2 * a.val) *
        gaussianAlternatingNoncrossingCount (k - (2 * a.val + 1)) := by
  have hZero : gaussianAlternatingWord (k + 1) 0 = false := by
    simp [gaussianAlternatingWord]
  have h := gaussian_noncrossing_first_pair_card (gaussianAlternatingWord (k + 1)) hZero
  simp only [gaussian_alternating_interior_count, gaussian_alternating_outer_count] at h
  change gaussianAlternatingNoncrossingCount (k + 1) =
    ∑ q : GaussianAdjointPositions (gaussianAlternatingWord (k + 1)),
      gaussianAlternatingNoncrossingCount (q.val.val - 1) *
        gaussianAlternatingNoncrossingCount (k - q.val.val) at h
  rw [h]
  symm
  apply Fintype.sum_equiv (gaussianAlternatingAdjointEquiv (k + 1)).symm
  intro a
  simp only [gaussian_alternating_adjoint_symm_value, Nat.add_sub_cancel]

theorem gaussian_alternating_even_recurrence (k : ℕ) :
    gaussianAlternatingNoncrossingCount (2 * (k + 1)) =
      ∑ a : Fin (k + 1), gaussianAlternatingNoncrossingCount (2 * a.val) *
        gaussianAlternatingNoncrossingCount (2 * (k - a.val)) := by
  have hSize : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  have hHalf : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
  have h := gaussian_alternating_first_recurrence (2 * k + 1)
  rw [hHalf] at h
  rw [hSize] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  have hLength : (2 * k + 1) - (2 * a.val + 1) = 2 * (k - a.val) := by
    have := a.isLt
    omega
  rw [hLength]

theorem gaussian_alternating_noncrossing_catalan (k : ℕ) :
    gaussianAlternatingNoncrossingCount (2 * k) = catalan k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [Nat.mul_zero, catalan_zero] using gaussian_alternating_noncrossing_zero
    | succ k =>
      rw [gaussian_alternating_even_recurrence, catalan_succ]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih a.val (by have := a.isLt; omega), ih (k - a.val) (by omega)]

theorem gaussian_alternating_noncrossing_centralBinom (k : ℕ) :
    gaussianAlternatingNoncrossingCount (2 * k) = k.centralBinom / (k + 1) := by
  rw [gaussian_alternating_noncrossing_catalan, catalan_eq_centralBinom_div]

theorem gaussian_word_mean_count_eq_noncrossing_card_all {n : ℕ} (b : Fin n → Bool) :
    gaussianWordMeanCount (List.ofFn b) = Fintype.card (GaussianNoncrossingPairings b) := by
  cases n with
  | zero => rw [List.ofFn_zero, gaussian_word_mean_count_nil, gaussian_noncrossing_empty_card]
  | succ n => exact gaussian_word_mean_count_eq_noncrossing_card n b

theorem gaussian_alternating_word_mean_count_catalan (k : ℕ) :
    gaussianWordMeanCount (List.ofFn (gaussianAlternatingWord (2 * k))) = catalan k := by
  rw [gaussian_word_mean_count_eq_noncrossing_card_all]
  exact gaussian_alternating_noncrossing_catalan k

theorem gaussian_alternating_normalized_word_mean_tendsto_catalan (k : ℕ) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n
      (List.ofFn (gaussianAlternatingWord (2 * k)))) atTop (𝓝 (catalan k : ℂ)) := by
  simpa only [gaussian_alternating_word_mean_count_catalan] using
    gaussian_word_mean_count_tendsto (List.ofFn (gaussianAlternatingWord (2 * k)))

end CircularLaw
