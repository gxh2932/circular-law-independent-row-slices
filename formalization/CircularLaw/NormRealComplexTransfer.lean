import CircularLaw.RowSliceRealNorm

/-!
# Transfer of a checked real matrix bound to complex vectors

The literal complex action splits into its real and imaginary input
actions. Coordinate projections decrease the input Euclidean norm;
embedding real outputs preserves their norm. The triangle inequality
gives a sufficient factor two, without assuming norm equivalence.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normRealPart {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (v j).re)

def normImagPart {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (v j).im)

def normRealEmbedding {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => (x j : ℂ))

theorem normRealPart_norm_le {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖normRealPart v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change ‖(v j).re‖ ^ 2 ≤ ‖v j‖ ^ 2
  rw [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

theorem normImagPart_norm_le {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖normImagPart v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change ‖(v j).im‖ ^ 2 ≤ ‖v j‖ ^ 2
  rw [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2

theorem normRealEmbedding_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖normRealEmbedding x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change ‖(x j : ℂ)‖ ^ 2 = ‖x j‖ ^ 2
  rw [Complex.norm_real]

def normComplexMatrixOperatorReal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (fun i j => (M i j : ℂ)))

theorem normComplexMatrixOperatorReal_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    normComplexMatrixOperatorReal M v i = ∑ j, (M i j : ℂ) * v j := rfl

theorem normComplexMatrixOperatorReal_decomposition {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℂ (Fin n)) :
    normComplexMatrixOperatorReal M v = normRealEmbedding (normRealMatrixOperator M (normRealPart v)) +
      Complex.I • normRealEmbedding (normRealMatrixOperator M (normImagPart v)) := by
  apply WithLp.ofLp_injective
  funext i
  change (∑ j, (M i j : ℂ) * v j) = ((∑ j, M i j * (v j).re : ℝ) : ℂ) +
    Complex.I * ((∑ j, M i j * (v j).im : ℝ) : ℂ)
  rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Complex.ext <;> simp

theorem normComplexMatrixOperatorReal_action_bound {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hReal : ‖normRealMatrixOperator M‖ ≤ B) (v : EuclideanSpace ℂ (Fin n)) :
    ‖normComplexMatrixOperatorReal M v‖ ≤ 2 * B * ‖v‖ := by
  rw [normComplexMatrixOperatorReal_decomposition]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Complex.norm_I, one_mul, normRealEmbedding_norm, normRealEmbedding_norm]
  have hRe := ((normRealMatrixOperator M).le_of_opNorm_le hReal (normRealPart v)).trans
    (mul_le_mul_of_nonneg_left (normRealPart_norm_le v) hB)
  have hIm := ((normRealMatrixOperator M).le_of_opNorm_le hReal (normImagPart v)).trans
    (mul_le_mul_of_nonneg_left (normImagPart_norm_le v) hB)
  linarith only [hRe, hIm]

theorem normComplexMatrixOperatorReal_norm_bound {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hReal : ‖normRealMatrixOperator M‖ ≤ B) : ‖normComplexMatrixOperatorReal M‖ ≤ 2 * B := by
  exact (normComplexMatrixOperatorReal M).opNorm_le_bound (by positivity)
    (normComplexMatrixOperatorReal_action_bound M hB hReal)

end CircularLaw
