import CircularLaw.FiniteRowNegativeSecondMoment

/-!
# Exact scaling of actual leave-one-out row distances

Nonzero complex scaling preserves each row span. Orthogonal projection
is complex linear, so distances scale by the scalar norm. Conjugated
matrix rows use the conjugate scalar and give the same norm factor.
-/

noncomputable section
open Classical
open scoped Pointwise

namespace CircularLaw

theorem finite_row_span_except_smul {ι : Type*} {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) {c : ℂ} (hc : c ≠ 0) (i : ι) :
    finiteRowSpanExcept (fun j => c • rows j) i = finiteRowSpanExcept rows i := by
  have hImage : (fun j => c • rows j) '' (Set.univ \ {i}) = c • (rows '' (Set.univ \ {i})) := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨rows j, ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
  unfold finiteRowSpanExcept
  rw [hImage, Submodule.span_smul_eq_of_isUnit _ c (isUnit_iff_ne_zero.mpr hc)]

theorem finite_row_distance_smul {ι : Type*} {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) {c : ℂ} (hc : c ≠ 0) (i : ι) :
    finiteRowDistance (fun j => c • rows j) i = ‖c‖ * finiteRowDistance rows i := by
  rw [← finite_row_residual_norm, ← finite_row_residual_norm]
  unfold finiteRowResidual
  simp only [finite_row_span_except_smul rows hc i, map_smul, norm_smul]

theorem complex_conjugate_rows_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (c : ℂ) :
    complexConjugateRows (c • A) = fun i => star c • complexConjugateRows A i := by
  funext i
  ext j
  change star (c * A i j) = star c * star (A i j)
  simpa only [mul_comm] using (star_mul c (A i j))

theorem complex_conjugate_row_distance_smul {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) (i : Fin m) :
    finiteRowDistance (complexConjugateRows (c • A)) i =
      ‖c‖ * finiteRowDistance (complexConjugateRows A) i := by
  rw [complex_conjugate_rows_smul, finite_row_distance_smul _ (star_ne_zero.mpr hc), norm_star]

end CircularLaw
