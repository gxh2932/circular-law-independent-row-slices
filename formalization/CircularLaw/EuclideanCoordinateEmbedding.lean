import CircularLaw.SpectralSubspaceComparison
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Coordinate embeddings and principal-matrix quadratic forms

An injective coordinate map sends the standard orthonormal basis to an
orthonormal family, hence extends to a linear isometry. The quadratic form
of a principal submatrix agrees exactly with the full matrix on this
embedded space. This supplies the geometric input to interlacing.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

section Coordinates

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def euclideanCoordinateEmbeddingLinear (f : κ ↪ ι) :
    EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (EuclideanSpace.basisFun κ ℂ).toBasis.constr ℂ (fun i => (EuclideanSpace.basisFun ι ℂ) (f i))

omit [DecidableEq κ] [DecidableEq ι] in
theorem euclideanCoordinateEmbeddingLinear_basis (f : κ ↪ ι) (i : κ) :
    euclideanCoordinateEmbeddingLinear f ((EuclideanSpace.basisFun κ ℂ) i) =
      (EuclideanSpace.basisFun ι ℂ) (f i) :=
  (EuclideanSpace.basisFun κ ℂ).toBasis.constr_basis ℂ _ i

def euclideanCoordinateEmbedding (f : κ ↪ ι) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (euclideanCoordinateEmbeddingLinear f).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun κ ℂ).toBasis)
    (EuclideanSpace.basisFun κ ℂ).orthonormal (by
      change Orthonormal ℂ (fun i : κ => euclideanCoordinateEmbeddingLinear f ((EuclideanSpace.basisFun κ ℂ) i))
      have hf := (EuclideanSpace.basisFun ι ℂ).orthonormal.comp f f.injective
      convert hf using 1
      funext i
      exact euclideanCoordinateEmbeddingLinear_basis f i)

omit [DecidableEq κ] [DecidableEq ι] in
theorem euclideanCoordinateEmbedding_basis (f : κ ↪ ι) (i : κ) :
    euclideanCoordinateEmbedding f ((EuclideanSpace.basisFun κ ℂ) i) =
      (EuclideanSpace.basisFun ι ℂ) (f i) := euclideanCoordinateEmbeddingLinear_basis f i

theorem matrix_inner_standard_basis (A : Matrix ι ι ℂ) (i j : ι) :
    ⟪A.toEuclideanLin ((EuclideanSpace.basisFun ι ℂ) i), (EuclideanSpace.basisFun ι ℂ) j⟫_ℂ =
      (starRingEnd ℂ) (A j i) := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  simp only [Matrix.toLpLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single_one,
    one_mul]
  rfl

end Coordinates

theorem linear_operator_inner_finite_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {κ : Type*} [Fintype κ] (T : E →ₗ[ℂ] E) (v : κ → E) (c : κ → ℂ) :
    ⟪T (∑ i, c i • v i), ∑ j, c j • v j⟫_ℂ =
      ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * ⟪T (v i), v j⟫_ℂ := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem principal_matrix_quadratic_embedding {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (f : κ ↪ ι) (v : EuclideanSpace ℂ κ) :
    ⟪A.toEuclideanLin (euclideanCoordinateEmbedding f v), euclideanCoordinateEmbedding f v⟫_ℂ =
      ⟪(A.submatrix f f).toEuclideanLin v, v⟫_ℂ := by
  let b := EuclideanSpace.basisFun κ ℂ
  let L := euclideanCoordinateEmbedding f
  let c := fun i => b.repr v i
  have hExpand : (∑ i, c i • b i) = v := b.sum_repr v
  have hExpandL : L v = ∑ i, c i • L (b i) := by
    rw [← hExpand]
    change L.toLinearMap (∑ i, c i • b i) = _
    simp only [map_sum, map_smul]
    rfl
  have hBasis (i j : κ) : ⟪A.toEuclideanLin (L (b i)), L (b j)⟫_ℂ =
      ⟪(A.submatrix f f).toEuclideanLin (b i), b j⟫_ℂ := by
    rw [euclideanCoordinateEmbedding_basis, euclideanCoordinateEmbedding_basis,
      matrix_inner_standard_basis, matrix_inner_standard_basis]
    rfl
  calc
    _ = ⟪A.toEuclideanLin (∑ i, c i • L (b i)), ∑ i, c i • L (b i)⟫_ℂ :=
      congrArg (fun x => ⟪A.toEuclideanLin x, x⟫_ℂ) hExpandL
    _ = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * ⟪A.toEuclideanLin (L (b i)), L (b j)⟫_ℂ :=
      linear_operator_inner_finite_sum _ _ _
    _ = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * ⟪(A.submatrix f f).toEuclideanLin (b i), b j⟫_ℂ := by
      simp only [hBasis]
    _ = ⟪(A.submatrix f f).toEuclideanLin (∑ i, c i • b i), ∑ i, c i • b i⟫_ℂ :=
      (linear_operator_inner_finite_sum _ _ _).symm
    _ = _ := congrArg (fun x => ⟪(A.submatrix f f).toEuclideanLin x, x⟫_ℂ) hExpand

end CircularLaw
