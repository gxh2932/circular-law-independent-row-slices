import CircularLaw.UnitaryMatrixEnergy

/-!
# A unitary first-eigenvector reduction for an arbitrary complex matrix

An actual nonzero eigenvector is normalized and extended to an
orthonormal basis. In these coordinates the first column has only its
diagonal eigenvalue. This is the dimension-reduction step for Schur's
eigenvalue energy bound.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem exists_orthonormalBasis_with_first {n : ℕ}
    (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℂ (EuclideanSpace ℂ (Fin (n + 1))), b 0 = v := by
  let s : Set (Fin (n + 1)) := {0}
  have hOrtho : Orthonormal ℂ (s.restrict (fun _ : Fin (n + 1) => v)) := by
    constructor
    · exact fun _ => hv
    · intro i j hij
      have hi : i.val = 0 := i.property
      have hj : j.val = 0 := j.property
      exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))
  obtain ⟨b, hb⟩ := hOrtho.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Fintype.card (Fin (n + 1)))
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

theorem exists_unit_eigenvector {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (lambda : ℂ) (v : EuclideanSpace ℂ (Fin (n + 1))), ‖v‖ = 1 ∧
      Matrix.toEuclideanLin A v = lambda • v := by
  obtain ⟨lambda, hLambda⟩ := Module.End.exists_eigenvalue (Matrix.toEuclideanLin A)
  obtain ⟨v, hv⟩ := hLambda.exists_hasEigenvector
  have hNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  let w := (‖v‖ : ℂ)⁻¹ • v
  refine ⟨lambda, w, ?_, ?_⟩
  · rw [show w = (‖v‖ : ℂ)⁻¹ • v from rfl, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hNorm
  · simp only [w, map_smul, hv.apply_eq_smul, smul_smul]
    congr 1
    exact mul_comm _ _

theorem exists_unitary_first_column_reduction {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (lambda : ℂ),
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧
      ∀ i, (U.conjTranspose * A * U) i 0 = if i = 0 then lambda else 0 := by
  obtain ⟨lambda, v, hNorm, hEigen⟩ := exists_unit_eigenvector A
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_with_first v hNorm
  let U := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b
  have hUnitary := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hRight : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hUnitary
  have hLeft : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUnitary
  have hColumn : U.col 0 = (fun i => v i) := by
    funext i
    change (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.repr (b 0) i = v i
    rw [hb]
    rfl
  have hEigenPi : A.mulVec (fun i => v i) = lambda • (fun i => v i) := by
    have h := congrArg (fun w : EuclideanSpace ℂ (Fin (n + 1)) => WithLp.ofLp w) hEigen
    exact h
  refine ⟨U, lambda, hRight, hLeft, ?_⟩
  have hFirst : (U.conjTranspose * A * U).mulVec (Pi.single 0 1) =
      lambda • (Pi.single 0 1 : Fin (n + 1) → ℂ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, hColumn,
      hEigenPi, Matrix.mulVec_smul]
    rw [← hColumn, ← Matrix.mulVec_single_one U, Matrix.mulVec_mulVec, hLeft, Matrix.one_mulVec]
  intro i
  have h := congrFun hFirst i
  simpa only [Matrix.mulVec_single_one, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero] using h

end CircularLaw
