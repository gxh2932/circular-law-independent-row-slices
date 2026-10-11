import CircularLaw.EmpiricalSpectralIntegrals
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Exact characteristic-root transport under a scalar shift

The root multiset keeps algebraic multiplicities. Evaluation of the
characteristic polynomial also identifies the singular shifts exactly.
-/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace CircularLaw

theorem matrix_scalar_eq_smul_one {n : ℕ} (z : ℂ) :
    Matrix.scalar (Fin n) z = z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar, h]

theorem matrix_charpoly_roots_sub_scalar {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (A - z • 1).charpoly.roots = A.charpoly.roots.map (fun w => w - z) := by
  have hFactor := (IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic
  have hShift : (A - z • 1).charpoly =
      ((A.charpoly.roots.map (fun w => w - z)).map
        (fun w => Polynomial.X - Polynomial.C w)).prod := by
    rw [← matrix_scalar_eq_smul_one, Matrix.charpoly_sub_scalar]
    conv_lhs => rw [hFactor, Polynomial.multiset_prod_comp, Multiset.map_map]
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro w _
    change (Polynomial.X - Polynomial.C w).comp (Polynomial.X + Polynomial.C z) =
      Polynomial.X - Polynomial.C (w - z)
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    simp only [Polynomial.C_sub]
    ring
  rw [hShift, Polynomial.roots_multiset_prod_X_sub_C]

theorem shifted_det_zero_iff_characteristic_root {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (A - z • 1).det = 0 ↔ z ∈ A.charpoly.roots := by
  rw [Polynomial.mem_roots A.charpoly_monic.ne_zero, Polynomial.IsRoot.def,
    Matrix.eval_charpoly, matrix_scalar_eq_smul_one]
  have hNeg : z • (1 : Matrix (Fin n) (Fin n) ℂ) - A = -(A - z • 1) := by abel
  rw [hNeg, Matrix.det_neg]
  simp

theorem empiricalSpectralMeasure_integral_sub_scalar {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (f : ℂ → ℝ) :
    (∫ w, f w ∂empiricalSpectralMeasure (A - z • 1)) =
      ∫ w, f (w - z) ∂empiricalSpectralMeasure A := by
  rw [empiricalSpectralMeasure_integral, empiricalSpectralMeasure_integral,
    matrix_charpoly_roots_sub_scalar, Multiset.map_map]
  rfl

theorem empiricalSpectralMeasure_singleton {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    empiricalSpectralMeasure A {z} =
      (n : ℝ≥0∞)⁻¹ * (A.charpoly.roots.count z : ℝ≥0∞) := by
  have hMass (s : Multiset ℂ) :
      ((s.map fun w => Measure.dirac w).sum : Measure ℂ) {z} = (s.count z : ℝ≥0∞) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      by_cases hw : w = z
      · simp [hw, ih, add_comm]
      · simp [hw, ih, Ne.symm hw]
  rw [empiricalSpectralMeasure, Measure.smul_apply, smul_eq_mul, hMass]

theorem empiricalSpectralMeasure_atom_iff_characteristic_root {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    empiricalSpectralMeasure A {z} ≠ 0 ↔ z ∈ A.charpoly.roots := by
  rw [empiricalSpectralMeasure_singleton]
  simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top,
    false_or, Nat.cast_eq_zero, Multiset.count_eq_zero, not_not]

end CircularLaw
