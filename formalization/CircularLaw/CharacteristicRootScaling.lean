import CircularLaw.SchurBlockReduction

/-!
# Scaling every characteristic root with its algebraic multiplicity

The unitary block reduction proves the exact multiset identity for every
complex scalar, including zero. No choice of distinct eigenvalues is used.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem matrix_charpoly_roots_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (c • A).charpoly.roots = A.charpoly.roots.map (fun z => c * z) := by
  induction n with
  | zero => simp [Matrix.charpoly]
  | succ n ih =>
    obtain ⟨U, lambda, hRight, _, hColumn⟩ := exists_unitary_first_column_reduction A
    let B := U.conjTranspose * A * U
    have hScaled : U.conjTranspose * (c • A) * U = c • B := by
      simp only [B, Matrix.mul_smul, Matrix.smul_mul]
    have hScaledColumn : ∀ i, (c • B) i 0 = if i = 0 then c * lambda else 0 := by
      intro i
      simp only [Matrix.smul_apply, smul_eq_mul, B, hColumn, mul_ite, mul_zero]
    have hRest : schurRemainingBlock (c • B) = c • schurRemainingBlock B := rfl
    rw [← unitary_conjugate_charpoly (c • A) U hRight, hScaled,
      first_column_charpoly_roots (c • B) (c * lambda) hScaledColumn, hRest, ih]
    rw [← unitary_conjugate_charpoly A U hRight, first_column_charpoly_roots B lambda hColumn]
    simp only [Multiset.map_cons]

end CircularLaw
