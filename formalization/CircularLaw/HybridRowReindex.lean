import CircularLaw.HybridOneRowIncrement
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Isolating an arbitrary row in the hybrid determinant

Simultaneous row reindexing leaves the regularized potential unchanged.
The selected row can therefore be moved to the one-dimensional Schur
block while the remaining rows retain their literal values.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem hybridRowRidgeGram_row_submatrix {m l n : Type*}
    [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
    (H : Matrix m n ℂ) (e : l ≃ m) (η : ℝ) :
    hybridRowRidgeGram (H.submatrix e id) η = (hybridRowRidgeGram H η).submatrix e e := by
  unfold hybridRowRidgeGram
  rw [Matrix.conjTranspose_submatrix]
  have hMul : H.submatrix e id * Hᴴ.submatrix id e = (H * Hᴴ).submatrix e e :=
    Matrix.submatrix_mul_equiv H Hᴴ e (Equiv.refl n) e
  rw [hMul]
  have hOne := Matrix.submatrix_one_equiv (α := ℂ) e
  ext i j
  change (H * Hᴴ) (e i) (e j) + η ^ 2 • (1 : Matrix l l ℂ) i j =
    (H * Hᴴ) (e i) (e j) + η ^ 2 • (1 : Matrix m m ℂ) (e i) (e j)
  rw [show (1 : Matrix m m ℂ) (e i) (e j) = (1 : Matrix l l ℂ) i j from
    congrFun (congrFun hOne i) j]

theorem regularizedRowPotential_row_submatrix {m l n : Type*}
    [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
    (H : Matrix m n ℂ) (e : l ≃ m) (η : ℝ) :
    regularizedRowPotential (H.submatrix e id) η = regularizedRowPotential H η := by
  unfold regularizedRowPotential
  rw [hybridRowRidgeGram_row_submatrix, Matrix.det_submatrix_equiv_self]

def hybridRowIndexEquiv {m : ℕ} (i : Fin (m + 1)) : Unit ⊕ Fin m ≃ Fin (m + 1) where
  toFun := Sum.elim (fun _ => i) i.succAbove
  invFun j := (finSuccEquiv' i j).casesOn (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (⟨⟩ | j) <;> simp
  right_inv := by
    intro j
    exact Fin.succAboveCases i (by simp) (fun a => by simp) j

theorem hybridInsertedRows_eq_row_submatrix {m n : ℕ}
    (H : Matrix (Fin (m + 1)) (Fin n) ℂ) (i : Fin (m + 1)) :
    hybridInsertedRows (fun j => H (i.succAbove j)) (WithLp.toLp 2 (H i)) =
      H.submatrix (hybridRowIndexEquiv i) id := by
  ext (j | j) a
  · cases j
    rfl
  · rfl

theorem regularizedRowPotential_isolate_row {m n : ℕ}
    (H : Matrix (Fin (m + 1)) (Fin n) ℂ) (i : Fin (m + 1)) (η : ℝ) :
    regularizedRowPotential H η =
      regularizedRowPotential
        (hybridInsertedRows (fun j => H (i.succAbove j)) (WithLp.toLp 2 (H i))) η := by
  rw [hybridInsertedRows_eq_row_submatrix, regularizedRowPotential_row_submatrix]

end CircularLaw
