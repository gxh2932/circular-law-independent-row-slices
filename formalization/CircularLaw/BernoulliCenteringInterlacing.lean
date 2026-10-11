import CircularLaw.BernoulliNormalizedWordMeans
import CircularLaw.MatrixColumnRestriction
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Singular-value interlacing under the actual Bernoulli centering

A constant-entry matrix has rank at most one. Its adjoint vanishes on
the kernel of the coordinate-sum functional. The two row-Gram quadratic
forms agree there, so the checked kernel dimension comparison gives
both singular-value inequalities with one lost index. This applies to
the actual degree-normalized shifted Bernoulli matrix at every sample.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace Matrix NNReal

namespace CircularLaw

def constantEntryMatrix (n : ℕ) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => c

theorem constant_entry_matrix_rank_bound (n : ℕ) (c : ℂ) :
    (constantEntryMatrix n c).rank ≤ 1 := by
  have hEq : constantEntryMatrix n c =
      Matrix.vecMulVec (fun _ : Fin n => c) (fun _ : Fin n => (1 : ℂ)) := by
    ext i j
    simp [constantEntryMatrix, Matrix.vecMulVec]
  rw [hEq]
  exact Matrix.rank_vecMulVec_le _ _

def euclideanCoordinateSum (n : ℕ) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ where
  toFun v := ∑ i, v i
  map_add' v w := by simp only [PiLp.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

theorem constant_entry_adjoint_kernel_zero {n : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ LinearMap.ker (euclideanCoordinateSum n)) :
    (constantEntryMatrix n c).conjTranspose.toEuclideanLin v = 0 := by
  have hSum : ∑ i, v i = 0 := LinearMap.mem_ker.mp hv
  ext j
  change (∑ i, star c * v i) = 0
  rw [← Finset.mul_sum, hSum, mul_zero]

theorem constant_entry_perturbation_adjoint_agrees {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ LinearMap.ker (euclideanCoordinateSum n)) :
    (B + constantEntryMatrix n c).conjTranspose.toEuclideanLin v =
      B.conjTranspose.toEuclideanLin v := by
  have hSum : ∑ i, v i = 0 := LinearMap.mem_ker.mp hv
  ext j
  change (∑ i, star (B i j + c) * v i) = ∑ i, star (B i j) * v i
  simp only [star_add, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hSum, mul_zero, add_zero]

theorem constant_entry_perturbation_singular_value_le {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (i j : Fin n)
    (hIndex : j.val = i.val + 1) :
    orderedSquareSingularValues (B + constantEntryMatrix n c) j ≤
      orderedSquareSingularValues B i := by
  apply Real.sqrt_le_sqrt
  apply symmetric_shifted_eigenvalues_le_on_kernel
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self B))
    (Matrix.isHermitian_iff_isSymmetric.mp
      (Matrix.isHermitian_mul_conjTranspose_self (B + constantEntryMatrix n c)))
    finrank_euclideanSpace (Module.finrank_self ℂ) (euclideanCoordinateSum n)
    _ ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩
      ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ hIndex
  intro v hv
  rw [row_gram_quadratic_eq_adjoint_norm, row_gram_quadratic_eq_adjoint_norm,
    constant_entry_perturbation_adjoint_agrees B c v hv]

theorem constant_entry_perturbation_singular_values_interlace {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (i j : Fin n)
    (hIndex : j.val = i.val + 1) :
    orderedSquareSingularValues (B + constantEntryMatrix n c) j ≤ orderedSquareSingularValues B i ∧
      orderedSquareSingularValues B j ≤ orderedSquareSingularValues (B + constantEntryMatrix n c) i := by
  constructor
  · exact constant_entry_perturbation_singular_value_le B c i j hIndex
  · have hEq : (B + constantEntryMatrix n c) + constantEntryMatrix n (-c) = B := by
      ext u v
      simp [constantEntryMatrix]
    simpa only [hEq] using
      constant_entry_perturbation_singular_value_le (B + constantEntryMatrix n c) (-c) i j hIndex

theorem bernoulli_centering_singular_values_interlace {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (i j : Fin n) (hIndex : j.val = i.val + 1) :
    orderedSquareSingularValues (normalizedShiftedBernoulliMatrix d z x) j ≤
        orderedSquareSingularValues (normalizedCenteredBernoulliMatrix d x - z • 1) i ∧
      orderedSquareSingularValues (normalizedCenteredBernoulliMatrix d x - z • 1) j ≤
        orderedSquareSingularValues (normalizedShiftedBernoulliMatrix d z x) i := by
  have hEq : normalizedShiftedBernoulliMatrix d z x =
      (normalizedCenteredBernoulliMatrix d x - z • 1) +
        constantEntryMatrix n ((Real.sqrt (d : ℝ) : ℂ)⁻¹ * (rowBernoulliParameter n d : ℂ)) := by
    rw [normalized_shifted_bernoulli_centered_decomposition]
    congr 1
  rw [hEq]
  exact constant_entry_perturbation_singular_values_interlace _ _ i j hIndex

end CircularLaw
