import CircularLaw.SquareSingularSecondMoment

/-!
# Every even singular moment equals the normalized Gram trace

The actual finite empirical singular measure retains every eigenvalue
with multiplicity. The identity holds at every natural power, including
power zero and the empty matrix, with Lean's real division convention.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

theorem hermitian_trace_pow_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem hermitian_trace_pow_real_eq_ordered_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace.re = ∑ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j ^ k := by
  have hReal : (A ^ k).trace.re = ∑ i, hA.eigenvalues i ^ k := by
    have h := congrArg Complex.re (hermitian_trace_pow_eq_sum A hA k)
    simpa only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] using h
  rw [hReal]
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  exact e.symm.sum_comp (fun j => hA.eigenvalues₀ j ^ k)

theorem square_singular_values_sum_even_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) :
    (∑ j, orderedSquareSingularValues A j ^ (2 * k)) =
      ((A * A.conjTranspose) ^ k).trace.re := by
  let hA := Matrix.isHermitian_mul_conjTranspose_self A
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin n).symm
  calc
    _ = ∑ j : Fin n, hA.eigenvalues₀ (c j) ^ k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_mul, orderedSquareSingularValues_sq]
      rfl
    _ = ∑ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j ^ k :=
      c.sum_comp (fun j => hA.eigenvalues₀ j ^ k)
    _ = _ := (hermitian_trace_pow_real_eq_ordered_sum _ hA k).symm

theorem square_singular_measure_even_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂squareSingularMeasure A) =
      ((A * A.conjTranspose) ^ k).trace.re / n := by
  rw [squareSingularMeasure, empiricalNonnegativeMeasure_integral]
  simp only [empiricalNonnegativeMean, finiteMean, Fintype.card_fin,
    squareSingularValuesNNReal, NNReal.coe_mk]
  rw [square_singular_values_sum_even_pow]

end CircularLaw
