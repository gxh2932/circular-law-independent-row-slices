import CircularLaw.MatrixGramTraceProducts
import CircularLaw.GaussianFinitePairings
import CircularLaw.GaussianPairingCycleCounts
import CircularLaw.GaussianTwoTraceCycleBound

/-!
# Actual Gaussian squared Gram traces and all two-block pairings

The joint closed-walk expansion is integrable under the actual Gaussian
matrix law. Wick matching and exact row/column coloring counts give its
full second moment, retaining pairings that connect the trace blocks.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_gram_two_trace_walk_integrable (n k : ℕ)
    (r s : Bool × Fin (k + 1) → Fin n) :
    Integrable (fun x : GaussianSquareSample n =>
      (∏ a, x (r a, s a)) *
        ∏ a, star (x (r (gaussianTwoTraceSuccessor k a), s a)))
      (gaussianSquareMatrixLaw n) :=
  gaussian_entry_finite_pairing_integrable (fun a => (r a, s a))
    (fun a => (r (gaussianTwoTraceSuccessor k a), s a))

theorem gaussian_gram_trace_square_pairing_integrable (n k : ℕ) :
    Integrable (fun x : GaussianSquareSample n =>
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace) ^ 2)
      (gaussianSquareMatrixLaw n) := by
  simp only [matrix_gram_trace_square_closed_walk_sum, gaussianSquareMatrix]
  apply integrable_finset_sum
  intro r _
  apply integrable_finset_sum
  intro s _
  exact gaussian_gram_two_trace_walk_integrable n k r s

theorem gaussian_gram_trace_square_cycle_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace) ^ 2
      ∂gaussianSquareMatrixLaw n) =
      ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        (n : ℂ) ^ gaussianTwoTraceCycleExponent k σ := by
  simp only [matrix_gram_trace_square_closed_walk_sum, gaussianSquareMatrix]
  change (∫ x : GaussianSquareSample n,
    ∑ r : Bool × Fin (k + 1) → Fin n, ∑ s : Bool × Fin (k + 1) → Fin n,
      (∏ a, x (r a, s a)) * ∏ a, star (x (r (gaussianTwoTraceSuccessor k a), s a))
      ∂gaussianSquareMatrixLaw n) = _
  rw [integral_finset_sum _ (fun r _ => integrable_finset_sum _
    (fun s _ => gaussian_gram_two_trace_walk_integrable n k r s))]
  simp only [integral_finset_sum _ (fun s _ => gaussian_gram_two_trace_walk_integrable n k _ s)]
  change (∑ r : Bool × Fin (k + 1) → Fin n, ∑ s : Bool × Fin (k + 1) → Fin n,
    ∫ x : GaussianSquareSample n, (∏ a, x (r a, s a)) *
      ∏ a, star (x (r (gaussianTwoTraceSuccessor k a), s a)) ∂gaussianSquareMatrixLaw n) = _
  simp only [gaussianSquareMatrixLaw, gaussian_entry_finite_wick_pairings, Prod.mk.injEq,
    finite_complex_indicator_product]
  calc
    _ = ∑ r : Bool × Fin (k + 1) → Fin n, ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        ∑ s : Bool × Fin (k + 1) → Fin n,
          if ∀ a, r (σ a) = r (gaussianTwoTraceSuccessor k a) ∧ s (σ a) = s a
          then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        ∑ r : Bool × Fin (k + 1) → Fin n, ∑ s : Bool × Fin (k + 1) → Fin n,
          if ∀ a, r (σ a) = r (gaussianTwoTraceSuccessor k a) ∧ s (σ a) = s a
          then (1 : ℂ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact gaussian_pairing_assignment_count n σ (gaussianTwoTraceSuccessor k)

theorem gaussian_gram_trace_square_real_eq (n k : ℕ) (x : GaussianSquareSample n) :
    (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace) ^ 2 =
      ((((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re) ^ 2 : ℝ) := by
  rw [hermitian_trace_pow_eq_ofReal_re _ (Matrix.isHermitian_mul_conjTranspose_self _) (k + 1)]
  simp only [Complex.ofReal_re, Complex.ofReal_pow]

theorem gaussian_gram_trace_square_pairing_real_integrable (n k : ℕ) :
    Integrable (fun x : GaussianSquareSample n =>
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re) ^ 2)
      (gaussianSquareMatrixLaw n) := by
  have h := (gaussian_gram_trace_square_pairing_integrable n k).re
  simpa only [gaussian_gram_trace_square_real_eq, Complex.ofReal_re] using h

theorem gaussian_gram_trace_square_cycle_real_integral (n k : ℕ) :
    (∫ x : GaussianSquareSample n,
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re) ^ 2
      ∂gaussianSquareMatrixLaw n) =
      ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ := by
  have hEq : (fun x : GaussianSquareSample n =>
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re) ^ 2) =
      fun x => RCLike.re
        ((((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace) ^ 2) := by
    funext x
    rw [gaussian_gram_trace_square_real_eq]
    rfl
  rw [hEq, integral_re (gaussian_gram_trace_square_pairing_integrable n k),
    gaussian_gram_trace_square_cycle_integral]
  change (∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
    (n : ℂ) ^ gaussianTwoTraceCycleExponent k σ).re = _
  simp only [Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    Complex.ofReal_re]

end CircularLaw
