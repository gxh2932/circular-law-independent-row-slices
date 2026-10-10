import CircularLaw.SchurBlockReduction

/-!
# Schur's bound for all characteristic roots with algebraic multiplicity

The first-eigenvector block reduction and induction prove that the sum
of squared eigenvalue norms is at most the actual Hilbert--Schmidt energy.
No diagonalizability or normality hypothesis is added.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def squareEigenvalueEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (A.charpoly.roots.map (fun z => ‖z‖ ^ 2)).sum

theorem square_eigenvalue_energy_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    squareEigenvalueEnergy A ≤ squareMatrixEnergy A := by
  induction n with
  | zero => simp [squareEigenvalueEnergy, Matrix.charpoly, squareMatrixEnergy]
  | succ n ih =>
    obtain ⟨lambda, B, hChar, hEnergy⟩ := exists_schur_energy_reduction A
    have hRoots : A.charpoly.roots = lambda ::ₘ B.charpoly.roots := by
      rw [hChar, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero lambda)
        B.charpoly_monic.ne_zero)]
      simp
    rw [squareEigenvalueEnergy, hRoots, Multiset.map_cons, Multiset.sum_cons]
    exact (add_le_add le_rfl (ih B)).trans hEnergy

end CircularLaw
