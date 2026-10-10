import CircularLaw.UnitaryEigenvectorReduction

/-!
# First-column block factorization in the Schur energy reduction

The characteristic roots split into the first eigenvalue and the roots
of the actual remaining block, with all algebraic multiplicities retained.
The first eigenvalue's squared norm and the remaining block's energy
are bounded by the full entrywise energy.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

def schurRemainingBlock {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := A.submatrix Fin.succ Fin.succ

theorem first_column_charpoly_factor {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (lambda : ℂ)
    (hColumn : ∀ i, A i 0 = if i = 0 then lambda else 0) :
    A.charpoly = (Polynomial.X - Polynomial.C lambda) * (schurRemainingBlock A).charpoly := by
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
    finSumFinEquiv.trans (finCongr (Nat.one_add n))
  have hLeft (i : Fin 1) : e (Sum.inl i) = 0 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply Fin.ext
    rfl
  have hRight (j : Fin n) : e (Sum.inr j) = j.succ := by
    apply Fin.ext
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
      Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  have hBlock : Matrix.reindex e.symm e.symm A = Matrix.fromBlocks
      (fun _ _ : Fin 1 => lambda) (fun _ j => A 0 j.succ) 0 (schurRemainingBlock A) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.reindex_apply, hLeft, hRight, hColumn, schurRemainingBlock, Fin.succ_ne_zero]
  have hScalar : (fun _ _ : Fin 1 => lambda) = Matrix.diagonal (fun _ => lambda) := by
    ext i j
    simp [Subsingleton.elim i j]
  have hChar := Matrix.charpoly_reindex e.symm A
  rw [hBlock, Matrix.charpoly_fromBlocks_zero₂₁, hScalar, Matrix.charpoly_diagonal] at hChar
  simpa using hChar.symm

theorem first_column_energy_bound {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (lambda : ℂ)
    (hColumn : ∀ i, A i 0 = if i = 0 then lambda else 0) :
    ‖lambda‖ ^ 2 + squareMatrixEnergy (schurRemainingBlock A) ≤ squareMatrixEnergy A := by
  have hEnergy : squareMatrixEnergy A = ‖lambda‖ ^ 2 +
      (∑ j : Fin n, ‖A 0 j.succ‖ ^ 2) + squareMatrixEnergy (schurRemainingBlock A) := by
    simp only [squareMatrixEnergy, Fin.sum_univ_succ, schurRemainingBlock,
      Matrix.submatrix_apply, hColumn, ite_true, Fin.succ_ne_zero, if_false,
      norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  have hNonneg : 0 ≤ ∑ j : Fin n, ‖A 0 j.succ‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem first_column_charpoly_roots {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (lambda : ℂ)
    (hColumn : ∀ i, A i 0 = if i = 0 then lambda else 0) :
    A.charpoly.roots = lambda ::ₘ (schurRemainingBlock A).charpoly.roots := by
  rw [first_column_charpoly_factor A lambda hColumn,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero lambda)
      (schurRemainingBlock A).charpoly_monic.ne_zero)]
  simp

theorem exists_schur_energy_reduction {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (lambda : ℂ) (B : Matrix (Fin n) (Fin n) ℂ),
      A.charpoly = (Polynomial.X - Polynomial.C lambda) * B.charpoly ∧
      ‖lambda‖ ^ 2 + squareMatrixEnergy B ≤ squareMatrixEnergy A := by
  obtain ⟨U, lambda, hRight, _, hColumn⟩ := exists_unitary_first_column_reduction A
  refine ⟨lambda, schurRemainingBlock (U.conjTranspose * A * U), ?_, ?_⟩
  · rw [← unitary_conjugate_charpoly A U hRight]
    exact first_column_charpoly_factor _ lambda hColumn
  · have h := first_column_energy_bound (U.conjTranspose * A * U) lambda hColumn
    rw [unitary_conjugate_energy A U hRight] at h
    exact h

end CircularLaw
