import CircularLaw.GaussianSquareMatrixLaw

/-!
# Exact Gaussian Gram trace moments

The trace of `(G G*)^2` is expanded over the actual ordered entries.
The checked four-entry identity counts both pairings, including their
intersection. Its expectation is exactly `2*n^3` at every dimension.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem square_gram_trace_square_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((A * A.conjTranspose) ^ 2).trace =
      ∑ i, ∑ k, ∑ j, ∑ l, A i j * star (A k j) * A k l * star (A i l) := by
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem gaussian_gram_trace_square_integrable (n : ℕ) :
    Integrable (fun x => ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ 2).trace)
      (gaussianSquareMatrixLaw n) := by
  simp only [square_gram_trace_square_expansion, gaussianSquareMatrix]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro l _
  exact gaussian_entry_wick_four_integrable (i, j) (k, j) (k, l) (i, l)

theorem gaussian_gram_four_entry_integral {n : ℕ} (i k j l : Fin n) :
    (∫ x : GaussianSquareSample n, x (i, j) * star (x (k, j)) * x (k, l) * star (x (i, l))
      ∂gaussianSquareMatrixLaw n) =
      (if i = k then 1 else 0) + (if j = l then 1 else 0) := by
  rw [gaussianSquareMatrixLaw, gaussian_entry_wick_four]
  simp only [Prod.mk.injEq, and_true, true_and]
  have hi : (i = k ∧ k = i) ↔ i = k := ⟨And.left, fun h => ⟨h, h.symm⟩⟩
  have hj : (j = l ∧ l = j) ↔ j = l := ⟨And.left, fun h => ⟨h, h.symm⟩⟩
  simp only [hi, hj]

theorem gaussian_gram_trace_square_integral (n : ℕ) :
    (∫ x, ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ 2).trace
      ∂gaussianSquareMatrixLaw n) = (2 : ℂ) * (n : ℂ) ^ 3 := by
  have hInt (i k j l : Fin n) : Integrable (fun x : GaussianSquareSample n =>
      x (i, j) * star (x (k, j)) * x (k, l) * star (x (i, l))) (gaussianSquareMatrixLaw n) :=
    gaussian_entry_wick_four_integrable (i, j) (k, j) (k, l) (i, l)
  simp only [square_gram_trace_square_expansion, gaussianSquareMatrix]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hInt i k j l))))]
  simp only [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun l _ => hInt _ k j l))),
    integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hInt _ _ j l)),
    integral_finset_sum _ (fun l _ => hInt _ _ _ l), gaussian_gram_four_entry_integral,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem gaussian_gram_trace_square_real_integrable (n : ℕ) :
    Integrable (fun x => (((gaussianSquareMatrix x *
      (gaussianSquareMatrix x).conjTranspose) ^ 2).trace).re) (gaussianSquareMatrixLaw n) :=
  (gaussian_gram_trace_square_integrable n).re

theorem gaussian_gram_trace_square_real_integral (n : ℕ) :
    (∫ x, (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ 2).trace).re
      ∂gaussianSquareMatrixLaw n) = (2 : ℝ) * (n : ℝ) ^ 3 := by
  change (∫ x, RCLike.re (((gaussianSquareMatrix x *
    (gaussianSquareMatrix x).conjTranspose) ^ 2).trace) ∂gaussianSquareMatrixLaw n) = _
  rw [integral_re (gaussian_gram_trace_square_integrable n), gaussian_gram_trace_square_integral]
  norm_cast

end CircularLaw
