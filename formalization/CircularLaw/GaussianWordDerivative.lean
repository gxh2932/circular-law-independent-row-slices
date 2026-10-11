import CircularLaw.GaussianNoncrossingListRecursion

/-!
# Finite word difference quotients for the actual Gaussian moment state

Deleting a symbol of opposite orientation leaves an ordered prefix and
suffix. The derivative retains every such occurrence, obeys the exact
noncommutative product rule and evaluates to the checked first-pair
Gaussian word moment. No word products are commuted.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def gaussianWordDerivative (b : Bool) : List Bool → List (List Bool × List Bool)
  | [] => []
  | c :: w => (if c ≠ b then [([], w)] else []) ++
      (gaussianWordDerivative b w).map (fun p => (c :: p.1, p.2))

theorem gaussian_word_derivative_sum (b : Bool) (w : List Bool)
    (f : List Bool × List Bool → ℂ) :
    ((gaussianWordDerivative b w).map f).sum =
      ∑ q : Fin w.length, if w.get q ≠ b then f (w.take q.val, w.drop (q.val + 1)) else 0 := by
  induction w generalizing f with
  | nil => simp [gaussianWordDerivative]
  | cons c w ih =>
    simp only [gaussianWordDerivative, List.map_append, List.sum_append, List.map_map]
    rw [ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    by_cases h : c ≠ b <;> simp [h]

theorem gaussian_word_derivative_append (b : Bool) (u v : List Bool) :
    gaussianWordDerivative b (u ++ v) =
      ((gaussianWordDerivative b u).map (fun p => (p.1, p.2 ++ v))) ++
        (gaussianWordDerivative b v).map (fun p => (u ++ p.1, p.2)) := by
  induction u with
  | nil => simp [gaussianWordDerivative]
  | cons c u ih =>
    simp only [List.cons_append, gaussianWordDerivative, ih, List.map_append, List.map_map]
    by_cases h : c ≠ b <;> simp [h, Function.comp_def]

theorem gaussian_word_derivative_moment (b : Bool) (w : List Bool) :
    (gaussianNoncrossingWordCount (b :: w) : ℂ) =
      ((gaussianWordDerivative b w).map
        (fun p => (gaussianNoncrossingWordCount p.1 : ℂ) * gaussianNoncrossingWordCount p.2)).sum := by
  rw [gaussian_word_derivative_sum]
  have h := congrArg (fun n : ℕ => (n : ℂ)) (gaussian_noncrossing_word_first_sum b w)
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero] using h

theorem gaussian_word_mean_count_derivative (b : Bool) (w : List Bool) :
    (gaussianWordMeanCount (b :: w) : ℂ) =
      ((gaussianWordDerivative b w).map
        (fun p => (gaussianWordMeanCount p.1 : ℂ) * gaussianWordMeanCount p.2)).sum := by
  simpa only [gaussian_word_mean_count_eq_noncrossing_word_count] using
    gaussian_word_derivative_moment b w

end CircularLaw
