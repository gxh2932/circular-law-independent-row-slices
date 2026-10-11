import CircularLaw.BernoulliSquareMatrixLaw

/-!
# The all-zero sample in the actual Bernoulli square law

This sample has strictly positive probability whenever `p<1`. Its shifted
matrix is `-z I`, so scalar-identity checks also apply to genuine samples
of the Bernoulli comparator, rather than only to abstract test matrices.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal Matrix ENNReal

namespace CircularLaw

def emptyBernoulliSquareSample (n : ℕ) : BernoulliSquareSample n := fun _ => false

theorem emptyBernoulliSquareMatrix (n : ℕ) :
    bernoulliSquareMatrix (emptyBernoulliSquareSample n) = 0 := by
  ext i j
  rfl

theorem normalizedShiftedBernoulliMatrix_empty (n d : ℕ) (z : ℂ) :
    normalizedShiftedBernoulliMatrix d z (emptyBernoulliSquareSample n) =
      (-z) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [normalizedShiftedBernoulliMatrix, emptyBernoulliSquareMatrix]
  simp only [smul_zero, zero_sub, neg_smul]

theorem emptyBernoulliSquareSample_probability (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliSquareMatrixLaw n p hp).real {emptyBernoulliSquareSample n} =
      (1 - (p : ℝ)) ^ (n * n) := by
  rw [measureReal_def, bernoulliSquareMatrixLaw, bernoulliCubeLaw,
    Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [← measureReal_def, emptyBernoulliSquareSample,
    bernoulliCoordinateLaw_singleton_real, Bool.false_eq_true, if_false,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

theorem emptyBernoulliSquareSample_probability_pos (n : ℕ) (p : ℝ≥0) (hp : p < 1) :
    0 < (bernoulliSquareMatrixLaw n p hp.le).real {emptyBernoulliSquareSample n} := by
  rw [emptyBernoulliSquareSample_probability]
  have hpR : (p : ℝ) < 1 := by exact_mod_cast hp
  exact pow_pos (sub_pos.mpr hpR) _

end CircularLaw
