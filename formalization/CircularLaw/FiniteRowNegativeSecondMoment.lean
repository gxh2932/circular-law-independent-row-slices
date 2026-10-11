import CircularLaw.FiniteRowGramInverse
import CircularLaw.HermitianInverseTrace
import CircularLaw.RectangularSingularInterlacing

/-!
# Negative second moments for arbitrary complex rectangular matrices

The inverse Gram trace equals the inverse squared singular-value sum and
the inverse squared row-distance sum. The literal conjugated rows have
Gram matrix `A A*`, so the identity applies directly to the ordered
rectangular singular values already used in interlacing.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace ComplexOrder

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def finiteRowSingularValues (rows : ι → EuclideanSpace ℂ (Fin n)) :
    Fin (Fintype.card ι) → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_gram ℂ rows).eigenvalues₀ j)

omit [DecidableEq ι] in
theorem finite_row_gram_posDef_of_distances (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) : (Matrix.gram ℂ rows).PosDef := by
  apply Matrix.posDef_gram_of_linearIndependent
  apply linearIndependent_iff_notMem_span.mpr
  intro i hMem
  exact (hDistance i).ne' (Metric.infDist_zero_of_mem hMem)

theorem finite_row_singular_values_sq (rows : ι → EuclideanSpace ℂ (Fin n))
    (j : Fin (Fintype.card ι)) :
    finiteRowSingularValues rows j ^ 2 = (Matrix.isHermitian_gram ℂ rows).eigenvalues₀ j := by
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := (Matrix.posSemidef_gram ℂ rows).eigenvalues_nonneg (e j)
  change 0 ≤ (Matrix.isHermitian_gram ℂ rows).eigenvalues₀ (e.symm (e j)) at h
  exact Real.sq_sqrt (by simpa only [Equiv.symm_apply_apply] using h)

theorem finite_row_singular_values_pos (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) (j : Fin (Fintype.card ι)) :
    0 < finiteRowSingularValues rows j := by
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := (finite_row_gram_posDef_of_distances rows hDistance).eigenvalues_pos (e j)
  change 0 < (Matrix.isHermitian_gram ℂ rows).eigenvalues₀ (e.symm (e j)) at h
  exact Real.sqrt_pos.mpr (by simpa only [Equiv.symm_apply_apply] using h)

theorem finite_row_negative_second_moment (rows : ι → EuclideanSpace ℂ (Fin n))
    (hDistance : ∀ i, 0 < finiteRowDistance rows i) :
    (∑ j, (finiteRowSingularValues rows j ^ 2)⁻¹) = ∑ i, (finiteRowDistance rows i ^ 2)⁻¹ := by
  let hGram := Matrix.isHermitian_gram ℂ rows
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hPos := finite_row_gram_posDef_of_distances rows hDistance
  have hEigen (i : ι) : hGram.eigenvalues i ≠ 0 := (hPos.eigenvalues_pos i).ne'
  calc
    _ = ∑ j, (hGram.eigenvalues₀ j)⁻¹ := by simp only [finite_row_singular_values_sq]
    _ = ∑ i, (hGram.eigenvalues i)⁻¹ :=
      (e.symm.sum_comp (fun j => (hGram.eigenvalues₀ j)⁻¹)).symm
    _ = ((Matrix.gram ℂ rows)⁻¹).trace.re := (hermitian_inverse_trace_real hGram hEigen).symm
    _ = _ := finite_row_gram_inverse_trace rows hDistance

theorem finite_row_negative_second_moment_sq_bound (rows : ι → EuclideanSpace ℂ (Fin n))
    {a : ℝ} (ha : 0 < a) (hDistance : ∀ i, a ≤ finiteRowDistance rows i ^ 2) :
    (∑ j, (finiteRowSingularValues rows j ^ 2)⁻¹) ≤ Fintype.card ι / a := by
  have hPos (i : ι) : 0 < finiteRowDistance rows i := by
    nlinarith [hDistance i, finite_row_distance_nonneg rows i]
  rw [finite_row_negative_second_moment rows hPos]
  calc
    _ ≤ ∑ _i : ι, a⁻¹ := Finset.sum_le_sum (fun i _ => by
      simpa only [one_div] using one_div_le_one_div_of_le ha (hDistance i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

def complexConjugateRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun j => star (A i j))

theorem complex_conjugate_row_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.gram ℂ (complexConjugateRows A) = A * A.conjTranspose := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
  change (∑ k, star (A j k) * star (star (A i k))) = ∑ k, A i k * star (A j k)
  simp only [star_star, mul_comm]

theorem finite_conjugate_row_singular_values_eq_rectangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin m) :
    finiteRowSingularValues (complexConjugateRows A)
      ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ = orderedRectangularSingularValues A j := by
  simp only [finiteRowSingularValues, orderedRectangularSingularValues, complex_conjugate_row_gram]

theorem rectangular_inverse_moment_eq_finite_row_inverse_moment {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (∑ j, (orderedRectangularSingularValues A j ^ 2)⁻¹) =
      ∑ j, (finiteRowSingularValues (complexConjugateRows A) j ^ 2)⁻¹ := by
  let c : Fin m ≃ Fin (Fintype.card (Fin m)) := finCongr (Fintype.card_fin _).symm
  calc
    _ = ∑ j : Fin m, (finiteRowSingularValues (complexConjugateRows A) (c j) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show c j = ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ from rfl,
        finite_conjugate_row_singular_values_eq_rectangular]
    _ = _ := c.sum_comp (fun j => (finiteRowSingularValues (complexConjugateRows A) j ^ 2)⁻¹)

theorem rectangular_singular_values_pos_of_row_distances {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ)
    (hDistance : ∀ i, 0 < finiteRowDistance (complexConjugateRows A) i) :
    ∀ j, 0 < orderedRectangularSingularValues A j := by
  intro j
  rw [← finite_conjugate_row_singular_values_eq_rectangular]
  exact finite_row_singular_values_pos _ hDistance _

theorem rectangular_negative_second_moment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (hDistance : ∀ i, 0 < finiteRowDistance (complexConjugateRows A) i) :
    (∑ j, (orderedRectangularSingularValues A j ^ 2)⁻¹) =
      ∑ i, (finiteRowDistance (complexConjugateRows A) i ^ 2)⁻¹ := by
  rw [rectangular_inverse_moment_eq_finite_row_inverse_moment]
  exact finite_row_negative_second_moment _ hDistance

theorem rectangular_negative_second_moment_sq_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) {a : ℝ} (ha : 0 < a)
    (hDistance : ∀ i, a ≤ finiteRowDistance (complexConjugateRows A) i ^ 2) :
    (∑ j, (orderedRectangularSingularValues A j ^ 2)⁻¹) ≤ m / a := by
  rw [rectangular_inverse_moment_eq_finite_row_inverse_moment]
  simpa only [Fintype.card_fin] using finite_row_negative_second_moment_sq_bound _ ha hDistance

end CircularLaw
