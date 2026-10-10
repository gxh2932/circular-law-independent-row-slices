import CircularLaw.GaussianWickPairings
import CircularLaw.MatrixGramWalks

/-!
# Every actual Gaussian Gram trace as a finite pairing sum

Closing each row walk gives a cyclic successor permutation. Wick's
formula pairs all direct and conjugate edges. Its row and column equality
constraints are retained exactly, so nonleading and repeated-index
contributions remain in the finite formula.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_gram_closed_walk_integrable (n k : ℕ)
    (r s : Fin (k + 1) → Fin n) :
    Integrable (fun x : GaussianSquareSample n =>
      (∏ t, x (r t, s t)) * ∏ t, star (x (r (finRotate (k + 1) t), s t)))
      (gaussianSquareMatrixLaw n) :=
  gaussian_entry_pairing_product_integrable (k + 1)
    (fun t => (r t, s t)) (fun t => (r (finRotate (k + 1) t), s t))

theorem gaussian_gram_closed_walk_integral (n k : ℕ)
    (r s : Fin (k + 1) → Fin n) :
    (∫ x : GaussianSquareSample n,
      (∏ t, x (r t, s t)) * ∏ t, star (x (r (finRotate (k + 1) t), s t))
      ∂gaussianSquareMatrixLaw n) =
      ∑ e : Equiv.Perm (Fin (k + 1)),
        ∏ t, if r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℂ) else 0 := by
  rw [gaussianSquareMatrixLaw, gaussian_entry_wick_pairings]
  simp only [Prod.mk.injEq]

theorem gaussian_gram_trace_pow_pairing_integrable (n k : ℕ) :
    Integrable (fun x : GaussianSquareSample n =>
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace)
      (gaussianSquareMatrixLaw n) := by
  simp only [matrix_gram_trace_closed_walk_sum, gaussianSquareMatrix]
  apply integrable_finset_sum
  intro r _
  apply integrable_finset_sum
  intro s _
  exact gaussian_gram_closed_walk_integrable n k r s

theorem gaussian_gram_trace_pow_pairing_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace
      ∂gaussianSquareMatrixLaw n) =
      ∑ e : Equiv.Perm (Fin (k + 1)),
        ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
          if ∀ t, r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℂ) else 0 := by
  simp only [matrix_gram_trace_closed_walk_sum, gaussianSquareMatrix]
  rw [integral_finset_sum _ (fun r _ => integrable_finset_sum _
    (fun s _ => gaussian_gram_closed_walk_integrable n k r s))]
  simp only [integral_finset_sum _ (fun s _ => gaussian_gram_closed_walk_integrable n k _ s),
    gaussian_gram_closed_walk_integral, finite_complex_indicator_product]
  calc
    _ = ∑ r : Fin (k + 1) → Fin n, ∑ e : Equiv.Perm (Fin (k + 1)),
        ∑ s : Fin (k + 1) → Fin n,
          if ∀ t, r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> rfl
    _ = _ := Finset.sum_comm

theorem gaussian_gram_trace_pow_pairing_real_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re
      ∂gaussianSquareMatrixLaw n) =
      ∑ e : Equiv.Perm (Fin (k + 1)),
        ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
          if ∀ t, r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℝ) else 0 := by
  change (∫ x, RCLike.re ((gaussianSquareMatrix x *
    (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace
    ∂gaussianSquareMatrixLaw n) = _
  rw [integral_re (gaussian_gram_trace_pow_pairing_integrable n k),
    gaussian_gram_trace_pow_pairing_integral]
  change (∑ e : Equiv.Perm (Fin (k + 1)),
    ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
      if ∀ t, r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℂ) else 0).re = _
  simp only [Complex.re_sum, apply_ite Complex.re, Complex.one_re, Complex.zero_re]

theorem gaussian_zero_shift_singular_moment_pairing_integral (n k : ℕ) :
    (∫ x, (∫ t, (t : ℝ) ^ (2 * (k + 1)) ∂gaussianSingularMeasure 0 x)
      ∂gaussianSquareMatrixLaw n) =
      (∑ e : Equiv.Perm (Fin (k + 1)),
        ∑ r : Fin (k + 1) → Fin n, ∑ s : Fin (k + 1) → Fin n,
          if ∀ t, r (e t) = r (finRotate (k + 1) t) ∧ s (e t) = s t then (1 : ℝ) else 0) /
        (n : ℝ) ^ (k + 2) := by
  simp only [gaussianSingularMeasure, normalizedShiftedGaussianMatrix,
    zero_smul, sub_zero]
  simp only [square_singular_measure_even_moment]
  simp only [square_gram_trace_pow_smul, pow_mul, inverse_sqrt_dimension_norm_sq]
  rw [integral_div, integral_const_mul, gaussian_gram_trace_pow_pairing_real_integral]
  simp only [div_eq_mul_inv, one_mul, inv_pow, pow_succ]
  ring

end CircularLaw
