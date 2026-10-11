import CircularLaw.GaussianScaledMatrixWords

/-!
# Finite noncommuting expansion of every scalar-shifted matrix word

Each position contributes either its matrix factor or its scalar
multiple of the identity. The recursive list retains multiplicities
and order. It expands shifted Gram powers at every order without a
commutativity assumption on matrix products.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

def matrixAdjointWord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : List Bool) :
    Matrix (Fin n) (Fin n) ℂ := (w.map (fun b => if b then A.conjTranspose else A)).prod

def scalarShiftWordFactor (z : ℂ) (b : Bool) : ℂ := if b then -star z else -z

def matrixScalarShiftedWord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (w : List Bool) : Matrix (Fin n) (Fin n) ℂ :=
  (w.map (fun b => (if b then A.conjTranspose else A) + scalarShiftWordFactor z b • 1)).prod

def scalarShiftWordExpansion (z : ℂ) : List Bool → List (ℂ × List Bool)
  | [] => [(1, [])]
  | b :: w =>
    ((scalarShiftWordExpansion z w).map (fun p => (p.1, b :: p.2))) ++
      (scalarShiftWordExpansion z w).map (fun p => (scalarShiftWordFactor z b * p.1, p.2))

theorem matrix_adjoint_word_cons {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Bool) (w : List Bool) :
    matrixAdjointWord A (b :: w) = (if b then A.conjTranspose else A) * matrixAdjointWord A w := rfl

theorem matrix_scalar_shift_list_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (s : ℂ) (L : List (ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    (A + s • 1) * (L.map (fun p => p.1 • p.2)).sum =
      (L.map (fun p => p.1 • (A * p.2))).sum +
        (L.map (fun p => (s * p.1) • p.2)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [mul_add, ih, add_mul, mul_smul_comm, smul_mul_assoc, Matrix.one_mul, smul_smul]
    abel

theorem matrix_scalar_shifted_word_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (w : List Bool) :
    matrixScalarShiftedWord A z w =
      ((scalarShiftWordExpansion z w).map (fun p => p.1 • matrixAdjointWord A p.2)).sum := by
  induction w with
  | nil => simp [matrixScalarShiftedWord, scalarShiftWordExpansion, matrixAdjointWord]
  | cons b w ih =>
    change ((if b then A.conjTranspose else A) + scalarShiftWordFactor z b • 1) *
      matrixScalarShiftedWord A z w = _
    rw [ih]
    simp only [scalarShiftWordExpansion, List.map_append, List.sum_append, List.map_map]
    simpa only [List.map_map, Function.comp_apply] using
      matrix_scalar_shift_list_sum (if b then A.conjTranspose else A) (scalarShiftWordFactor z b)
        ((scalarShiftWordExpansion z w).map (fun p => (p.1, matrixAdjointWord A p.2)))

theorem matrix_scalar_shifted_word_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (w : List Bool) :
    matrixScalarShiftedWord A z w = matrixAdjointWord (A - z • 1) w := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro b _
  cases b <;>
    simp [scalarShiftWordFactor, Matrix.conjTranspose_smul,
      sub_eq_add_neg]

def gramMatrixWord : ℕ → List Bool
  | 0 => []
  | k + 1 => false :: true :: gramMatrixWord k

theorem matrix_adjoint_gram_word {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    matrixAdjointWord A (gramMatrixWord k) = (A * A.conjTranspose) ^ k := by
  induction k with
  | zero => simp [matrixAdjointWord, gramMatrixWord]
  | succ k ih =>
    rw [gramMatrixWord, matrix_adjoint_word_cons, matrix_adjoint_word_cons, ih, pow_succ']
    simp only [Bool.false_eq_true, if_false, if_true, mul_assoc]

theorem matrix_shifted_gram_pow_word {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (k : ℕ) :
    ((A - z • 1) * (A - z • 1).conjTranspose) ^ k =
      matrixScalarShiftedWord A z (gramMatrixWord k) := by
  rw [matrix_scalar_shifted_word_eq, matrix_adjoint_gram_word]

theorem gaussian_scaled_matrix_word_eq_adjoint_word {n : ℕ} (c : ℂ) (w : List Bool)
    (x : GaussianSquareSample n) :
    gaussianScaledMatrixWord c w x = matrixAdjointWord (c • gaussianSquareMatrix x) w := rfl

end CircularLaw
