import CircularLaw.MatrixGramWalks

/-!
# Exact closed-walk expansion for a noncommuting matrix word

Each matrix keeps its position in the product. Summing over every
intermediate index gives the entry formula; closing the endpoints gives
one cyclic vertex assignment and one entry factor per word position.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem matrix_word_entry_walk_sum {n : ℕ} (k : ℕ)
    (A : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (List.ofFn A).prod i j = ∑ v : Fin k → Fin n,
      ∏ t, A t ((Fin.cons i v : Fin (k + 1) → Fin n) t)
        ((Fin.snoc v j : Fin (k + 1) → Fin n) t) := by
  induction k generalizing i j with
  | zero => simp [Fin.snoc_zero]
  | succ k ih =>
    have hA : A = Fin.cons (A 0) (Fin.tail A) := (Fin.cons_self_tail A).symm
    conv_lhs => rw [hA, List.ofFn_cons, List.prod_cons, Matrix.mul_apply]
    simp only [ih, Finset.mul_sum]
    rw [finite_tuple_sum_cons]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ← Fin.cons_snoc_eq_snoc_cons]
    rfl

theorem matrix_word_trace_closed_walk_sum {n : ℕ} (k : ℕ)
    (A : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) :
    (List.ofFn A).prod.trace = ∑ v : Fin (k + 1) → Fin n,
      ∏ t, A t (v t) (v (finRotate (k + 1) t)) := by
  simp only [Matrix.trace, Matrix.diag, matrix_word_entry_walk_sum]
  rw [finite_tuple_sum_cons]
  simp only [Fin.snoc_eq_cons_rotate]

end CircularLaw
