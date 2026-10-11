import CircularLaw.PairedTwoClosedWalks

/-!
# Products of arbitrary Gaussian word traces

The two word lengths and Boolean patterns can differ. The exact joint
closed-walk expansion joins their vertex assignments on a sum type.
Wick integration then counts every direct-to-adjoint bijection, including
those crossing the two trace blocks.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_two_word_walk_split {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {n : ℕ} (b : α → Bool) (c : β → Bool)
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (v : α → Fin n) (w : β → Fin n)
    (x : GaussianSquareSample n) :
    gaussianWordClosedWalk (Sum.elim b c) (Equiv.sumCongr ρ τ) (Sum.elim v w) x =
      gaussianWordClosedWalk b ρ v x * gaussianWordClosedWalk c τ w x := by
  simp only [gaussianWordClosedWalk, Fintype.prod_sum_type,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]

theorem gaussian_two_word_walk_sum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {n : ℕ} (b : α → Bool) (c : β → Bool)
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (x : GaussianSquareSample n) :
    (∑ v : α → Fin n, gaussianWordClosedWalk b ρ v x) *
      (∑ w : β → Fin n, gaussianWordClosedWalk c τ w x) =
      ∑ u : α ⊕ β → Fin n, gaussianWordClosedWalk (Sum.elim b c) (Equiv.sumCongr ρ τ) u x := by
  rw [← (Equiv.sumArrowEquivProdArrow α β (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact (gaussian_two_word_walk_split b c ρ τ v w x).symm

theorem gaussian_two_word_trace_walk_sum {n : ℕ} (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) (x : GaussianSquareSample n) :
    (gaussianMatrixWord (List.ofFn b) x).trace * (gaussianMatrixWord (List.ofFn c) x).trace =
      ∑ u : Fin (k + 1) ⊕ Fin (l + 1) → Fin n,
        gaussianWordClosedWalk (Sum.elim b c)
          (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) u x := by
  rw [gaussian_matrix_word_closed_walk_sum, gaussian_matrix_word_closed_walk_sum]
  exact gaussian_two_word_walk_sum b c _ _ x

theorem gaussian_two_word_trace_pairing_integral (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (e₀ : GaussianWordPairing (Sum.elim b c)) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace *
      (gaussianMatrixWord (List.ofFn c) x).trace ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing (Sum.elim b c),
        (n : ℂ) ^ gaussianWordVertexExponent (Sum.elim b c)
          (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e := by
  simp only [gaussian_two_word_trace_walk_sum]
  exact gaussian_word_walk_sum_integral _ _ e₀

theorem gaussian_matrix_word_trace_product_integrable (n : ℕ) (w v : List Bool) :
    Integrable (fun x => (gaussianMatrixWord w x).trace * (gaussianMatrixWord v x).trace)
      (gaussianSquareMatrixLaw n) := by
  have hEq : (fun x : GaussianSquareSample n =>
      (gaussianMatrixWord w x).trace * (gaussianMatrixWord v x).trace) =
      gaussianPolynomialEvaluation ((gaussianSymbolicMatrixWord n w).trace *
        (gaussianSymbolicMatrixWord n v).trace) := by
    funext x
    rw [gaussian_polynomial_evaluation_mul, gaussian_symbolic_word_trace_evaluation,
      gaussian_symbolic_word_trace_evaluation]
  rw [hEq]
  exact gaussian_polynomial_evaluation_integrable _

theorem gaussian_matrix_word_trace_product_integral_unbalanced (n : ℕ) (w v : List Bool)
    (h : gaussianMatrixWordImbalance w + gaussianMatrixWordImbalance v ≠ 0) :
    (∫ x, (gaussianMatrixWord w x).trace * (gaussianMatrixWord v x).trace
      ∂gaussianSquareMatrixLaw n) = 0 := by
  have hEq : (fun x : GaussianSquareSample n =>
      (gaussianMatrixWord w x).trace * (gaussianMatrixWord v x).trace) =
      gaussianPolynomialEvaluation ((gaussianSymbolicMatrixWord n w).trace *
        (gaussianSymbolicMatrixWord n v).trace) := by
    funext x
    rw [gaussian_polynomial_evaluation_mul, gaussian_symbolic_word_trace_evaluation,
      gaussian_symbolic_word_trace_evaluation]
  rw [hEq]
  exact gaussian_homogeneous_polynomial_integral_zero _
    ((gaussian_symbolic_word_trace_homogeneous n w).mul
      (gaussian_symbolic_word_trace_homogeneous n v)) h

end CircularLaw
