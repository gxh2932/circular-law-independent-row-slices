import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace of an inverse Hermitian matrix

Unitary diagonalization and an explicit diagonal right inverse identify
the inverse trace with the sum of inverse eigenvalues. This is the spectral
step in the negative second-moment identity; no spectral identity is
introduced as an axiom.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators

namespace CircularLaw

theorem hermitian_inverse_diagonalization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hEigen : ∀ i, hA.eigenvalues i ≠ 0) :
    A⁻¹ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)⁻¹))) := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let Dinv := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)⁻¹))
  have hDiag : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hEntry (i : ι) : (hA.eigenvalues i : ℂ) * (hA.eigenvalues i : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hEigen i))
    simp only [hEntry, Matrix.diagonal_one]
  have hSpectral : A = (U : Matrix ι ι ℂ) * D * (star U : Matrix ι ι ℂ) := hA.spectral_theorem
  apply Matrix.inv_eq_right_inv
  change A * ((U : Matrix ι ι ℂ) * Dinv * (star U : Matrix ι ι ℂ)) = 1
  rw [hSpectral]
  calc
    _ = (U : Matrix ι ι ℂ) * (D * ((star U : Matrix ι ι ℂ) * U) * Dinv) *
        (star U : Matrix ι ι ℂ) := by simp only [Matrix.mul_assoc]
    _ = (U : Matrix ι ι ℂ) * (D * Dinv) * (star U : Matrix ι ι ℂ) := by
      rw [Unitary.coe_star_mul_self, Matrix.mul_one]
    _ = 1 := by
      rw [hDiag, Matrix.mul_one]
      simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U

theorem hermitian_inverse_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hEigen : ∀ i, hA.eigenvalues i ≠ 0) :
    A⁻¹.trace = ∑ i, ((hA.eigenvalues i : ℂ)⁻¹) := by
  rw [hermitian_inverse_diagonalization hA hEigen, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

theorem hermitian_inverse_trace_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hEigen : ∀ i, hA.eigenvalues i ≠ 0) :
    A⁻¹.trace.re = ∑ i, (hA.eigenvalues i)⁻¹ := by
  rw [hermitian_inverse_trace hA hEigen, Complex.re_sum]
  simp only [← Complex.ofReal_inv, Complex.ofReal_re]

end CircularLaw
