import CircularLaw.GaussianShiftedWordFunctional
import CircularLaw.GaussianAlternatingWords

/-!
# Recursion for actual shifted alternating-word moment limits

At a real shift, color negation preserves the limiting word functional.
Thus the value of any alternating word depends only on its length. The
first-pair identity reduces to a scalar recurrence with the exact even
partner positions. Even lengths are the actual singular moments.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianAlternatingList (b : Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => b :: gaussianAlternatingList (!b) n

theorem gaussian_alternating_list_length (b : Bool) (n : ℕ) :
    (gaussianAlternatingList b n).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [gaussianAlternatingList, ih]

theorem gaussian_alternating_list_map_not (b : Bool) (n : ℕ) :
    (gaussianAlternatingList b n).map Bool.not = gaussianAlternatingList (!b) n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [gaussianAlternatingList, ih]

theorem gaussian_alternating_list_getElem (b : Bool) {n : ℕ} (q : ℕ) (hq : q < n) :
    (gaussianAlternatingList b n)[q]'(by rw [gaussian_alternating_list_length]; exact hq) =
      if q % 2 = 0 then b else !b := by
  induction n generalizing b q with
  | zero => omega
  | succ n ih =>
    cases q with
    | zero => simp [gaussianAlternatingList]
    | succ q =>
      simp only [gaussianAlternatingList, List.getElem_cons_succ]
      rw [ih (!b) q (by omega)]
      by_cases h : q % 2 = 0
      · have h' : (q + 1) % 2 ≠ 0 := by omega
        simp [h, h']
      · have h' : (q + 1) % 2 = 0 := by omega
        simp [h, h']

theorem gaussian_alternating_list_take (b : Bool) (n q : ℕ) (hq : q ≤ n) :
    (gaussianAlternatingList b n).take q = gaussianAlternatingList b q := by
  induction q generalizing b n with
  | zero => simp [gaussianAlternatingList]
  | succ q ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [gaussianAlternatingList, List.take_succ_cons]
      rw [ih (!b) n (by omega)]

theorem gaussian_alternating_list_drop (b : Bool) (n q : ℕ) :
    (gaussianAlternatingList b n).drop q =
      gaussianAlternatingList (if q % 2 = 0 then b else !b) (n - q) := by
  induction q generalizing b n with
  | zero => simp
  | succ q ih =>
    cases n with
    | zero => simp [gaussianAlternatingList]
    | succ n =>
      simp only [gaussianAlternatingList, List.drop_succ_cons]
      rw [ih (!b) n]
      by_cases h : q % 2 = 0
      · have h' : (q + 1) % 2 ≠ 0 := by omega
        simp [h, h']
      · have h' : (q + 1) % 2 = 0 := by omega
        simp [h, h']

theorem gaussian_alternating_list_gram (k : ℕ) :
    gaussianAlternatingList false (2 * k) = gramMatrixWord k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    simp only [gaussianAlternatingList, Bool.not_false, Bool.not_true, gramMatrixWord, ih]

def gaussianShiftedAlternatingValue (r : ℝ) (n : ℕ) : ℂ :=
  gaussianShiftedWordMeanValue (r : ℂ) (gaussianAlternatingList false n)

theorem gaussian_shifted_alternating_value_orientation (r : ℝ) (b : Bool) (n : ℕ) :
    gaussianShiftedWordMeanValue (r : ℂ) (gaussianAlternatingList b n) =
      gaussianShiftedAlternatingValue r n := by
  cases b with
  | false => rfl
  | true =>
    change gaussianShiftedWordMeanValue (r : ℂ) (gaussianAlternatingList (!false) n) = _
    rw [← gaussian_alternating_list_map_not false,
      gaussian_shifted_word_mean_value_map_not_real]
    rfl

theorem gaussian_shifted_alternating_value_zero (r : ℝ) :
    gaussianShiftedAlternatingValue r 0 = 1 :=
  gaussian_shifted_word_mean_value_nil (r : ℂ)

theorem gaussian_shifted_alternating_value_even (r : ℝ) (k : ℕ) :
    gaussianShiftedAlternatingValue r (2 * k) = gaussianShiftedMomentMeanLimit (r : ℂ) k := by
  rw [gaussianShiftedAlternatingValue, gaussian_alternating_list_gram,
    gaussian_shifted_word_mean_value_gram]

theorem gaussian_shifted_alternating_value_recursion (r : ℝ) (n : ℕ) :
    gaussianShiftedAlternatingValue r (n + 1) =
      -(r : ℂ) * gaussianShiftedAlternatingValue r n +
        ∑ q : Fin n, if q.val % 2 = 0 then
          gaussianShiftedAlternatingValue r q.val *
            gaussianShiftedAlternatingValue r (n - (q.val + 1)) else 0 := by
  rw [gaussianShiftedAlternatingValue, gaussianAlternatingList,
    gaussian_shifted_word_mean_value_first_sum, scalar_shift_word_factor_real,
    gaussian_shifted_alternating_value_orientation]
  congr 1
  let f : Fin (gaussianAlternatingList true n).length → ℂ := fun q =>
    if (gaussianAlternatingList true n).get q ≠ false then
      gaussianShiftedWordMeanValue (r : ℂ) ((gaussianAlternatingList true n).take q.val) *
        gaussianShiftedWordMeanValue (r : ℂ)
          ((gaussianAlternatingList true n).drop (q.val + 1)) else 0
  change (∑ q, f q) = _
  rw [← (finCongr (gaussian_alternating_list_length true n)).symm.sum_comp f]
  apply Finset.sum_congr rfl
  intro q _
  simp only [f, List.get_eq_getElem, finCongr_symm_apply_coe]
  simp only [gaussian_alternating_list_getElem true q.val q.isLt,
    gaussian_alternating_list_take true n q.val (Nat.le_of_lt q.isLt),
    gaussian_alternating_list_drop, gaussian_shifted_alternating_value_orientation]
  by_cases h : q.val % 2 = 0 <;> simp [h]

theorem finite_even_positions_sum (n : ℕ) (f : ℕ → ℂ) :
    (∑ q : Fin n, if q.val % 2 = 0 then f q.val else 0) =
      ∑ j : Fin ((n + 1) / 2), f (2 * j.val) := by
  calc
    _ = ∑ q : {q : Fin n // q.val % 2 = 0}, f q.val.val := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun q : Fin n => q.val % 2 = 0)
        (Finset.univ.filter (fun q => q.val % 2 = 0))
        (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun q => f q.val))
    _ = _ := (finiteParityPositionsEquiv n 0 (by decide)).sum_comp
      (fun q => f q.val.val) |>.symm

theorem gaussian_shifted_alternating_even_recursion (r : ℝ) (k : ℕ) :
    gaussianShiftedAlternatingValue r (2 * (k + 1)) =
      -(r : ℂ) * gaussianShiftedAlternatingValue r (2 * k + 1) +
        ∑ j : Fin (k + 1), gaussianShiftedAlternatingValue r (2 * j.val) *
          gaussianShiftedAlternatingValue r (2 * (k - j.val)) := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    gaussian_shifted_alternating_value_recursion,
    finite_even_positions_sum (2 * k + 1) (fun q => gaussianShiftedAlternatingValue r q *
      gaussianShiftedAlternatingValue r (2 * k + 1 - (q + 1)))]
  congr 1
  rw [← (finCongr (show (2 * k + 1 + 1) / 2 = k + 1 by omega)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [finCongr_symm_apply_coe]
  congr 2
  omega

theorem gaussian_shifted_alternating_odd_recursion (r : ℝ) (k : ℕ) :
    gaussianShiftedAlternatingValue r (2 * k + 1) =
      -(r : ℂ) * gaussianShiftedAlternatingValue r (2 * k) +
        ∑ j : Fin k, gaussianShiftedAlternatingValue r (2 * j.val) *
          gaussianShiftedAlternatingValue r (2 * (k - j.val - 1) + 1) := by
  rw [gaussian_shifted_alternating_value_recursion,
    finite_even_positions_sum (2 * k) (fun q => gaussianShiftedAlternatingValue r q *
      gaussianShiftedAlternatingValue r (2 * k - (q + 1)))]
  congr 1
  rw [← (finCongr (show (2 * k + 1) / 2 = k by omega)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [finCongr_symm_apply_coe]
  have := j.isLt
  congr 2
  omega

end CircularLaw
