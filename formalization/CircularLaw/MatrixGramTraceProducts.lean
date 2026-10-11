import CircularLaw.MatrixGramWalks
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Products of actual Gram traces as joint closed walks

The two trace blocks retain independent row and column labels before
Wick matching. Reindexing by currying joins their position types without
discarding repeated entries or matchings between the traces.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem matrix_gram_trace_square_closed_walk_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (((A * A.conjTranspose) ^ (k + 1)).trace) ^ 2 =
      ∑ r : Bool × Fin (k + 1) → Fin n, ∑ s : Bool × Fin (k + 1) → Fin n,
        (∏ a, A (r a) (s a)) *
          ∏ a, star (A (r (a.1, finRotate (k + 1) a.2)) (s a)) := by
  let e := Equiv.curry Bool (Fin (k + 1)) (Fin n)
  calc
    _ = ∏ _b : Bool, ((A * A.conjTranspose) ^ (k + 1)).trace := by
      simp only [Fintype.prod_bool, pow_two]
    _ = ∏ _b : Bool, ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
        (∏ t, A (r t) (s t)) * ∏ t, star (A (r (finRotate (k + 1) t)) (s t)) := by
      simp only [matrix_gram_trace_closed_walk_sum]
    _ = ∑ R : Bool → Fin (k + 1) → Fin n, ∑ S : Bool → Fin (k + 1) → Fin n,
        (∏ b, ∏ t, A (R b t) (S b t)) *
          ∏ b, ∏ t, star (A (R b (finRotate (k + 1) t)) (S b t)) := by
      rw [Fintype.prod_sum]
      simp only [Fintype.prod_sum, Finset.prod_mul_distrib]
    _ = _ := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro r _
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro s _
      simp only [e, Equiv.curry_apply, Function.curry]
      simp only [Fintype.prod_prod_type]

end CircularLaw
