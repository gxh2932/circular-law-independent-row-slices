import CircularLaw.MatrixGramShiftTrace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Matrix powers and Gram traces as exact finite walks

An entry path retains every intermediate row index. A Gram path then
expands over one column index for each edge, separating its direct and
conjugate entry factors. No distinctness or asymptotic approximation is
used, including paths that revisit the same matrix entry.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem finite_tuple_sum_cons {α E : Type*} [Fintype α] [AddCommMonoid E]
    (k : ℕ) (f : (Fin (k + 1) → α) → E) :
    (∑ v, f v) = ∑ a, ∑ w : Fin k → α, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

def matrixEntryPath {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Fin n → List (Fin n) → Fin n → ℂ
  | i, [], j => A i j
  | i, a :: path, j => A i a * matrixEntryPath A a path j

theorem matrix_power_entry_path_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (i j : Fin n) :
    (A ^ (k + 1)) i j = ∑ v : Fin k → Fin n, matrixEntryPath A i (List.ofFn v) j := by
  induction k generalizing i j with
  | zero => simp [matrixEntryPath]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, finite_tuple_sum_cons]
    simp only [ih, Finset.mul_sum, List.ofFn_cons, matrixEntryPath]

theorem matrix_power_trace_path_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (A ^ (k + 1)).trace =
      ∑ i, ∑ v : Fin k → Fin n, matrixEntryPath A i (List.ofFn v) i := by
  simp only [Matrix.trace, Matrix.diag, matrix_power_entry_path_sum]

theorem matrix_gram_entry_path_sum_columns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (i j : Fin n) (v : Fin k → Fin n) :
    matrixEntryPath (A * A.conjTranspose) i (List.ofFn v) j =
      ∑ s : Fin (k + 1) → Fin n,
        (∏ t, A ((Fin.cons i v : Fin (k + 1) → Fin n) t) (s t)) *
          ∏ t, star (A ((Fin.snoc v j : Fin (k + 1) → Fin n) t) (s t)) := by
  induction k generalizing i j with
  | zero =>
    rw [finite_tuple_sum_cons]
    simp [matrixEntryPath, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.snoc_zero]
  | succ k ih =>
    have hv : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
    rw [hv, List.ofFn_cons, matrixEntryPath, ih, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    conv_rhs => rw [finite_tuple_sum_cons]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ← Fin.cons_snoc_eq_snoc_cons]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro s _
    ring

theorem matrix_gram_trace_walk_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ((A * A.conjTranspose) ^ (k + 1)).trace =
      ∑ i, ∑ v : Fin k → Fin n, ∑ s : Fin (k + 1) → Fin n,
        (∏ t, A ((Fin.cons i v : Fin (k + 1) → Fin n) t) (s t)) *
          ∏ t, star (A ((Fin.snoc v i : Fin (k + 1) → Fin n) t) (s t)) := by
  simp only [matrix_power_trace_path_sum, matrix_gram_entry_path_sum_columns]

theorem matrix_gram_trace_closed_walk_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ((A * A.conjTranspose) ^ (k + 1)).trace =
      ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
        (∏ t, A (r t) (s t)) * ∏ t, star (A (r (finRotate (k + 1) t)) (s t)) := by
  rw [matrix_gram_trace_walk_sum, finite_tuple_sum_cons]
  simp only [Fin.snoc_eq_cons_rotate]

end CircularLaw
