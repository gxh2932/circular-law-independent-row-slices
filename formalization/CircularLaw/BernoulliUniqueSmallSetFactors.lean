import CircularLaw.BernoulliUniqueCountStructure
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Small-set bounds for both unique-neighbourhood row factors

When |S|*p is at most one half, the diagonal zero-pattern factor retains
the small quantity |S|*p+exp(-t). This is needed to offset the number of
possible sets, rather than discarding the diagonal-row contribution.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_zero_pattern_failure_le {p : ℝ} (hp : p ≤ 1) (ell : ℕ) :
    1 - (1 - p) ^ ell ≤ (ell : ℝ) * p := by
  have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) ell
  simp only [mul_neg, ← sub_eq_add_neg] at h
  linarith

theorem bernoulli_single_pattern_small_set_lower (p : ℝ≥0) (hp : p ≤ 1) (ell : ℕ)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) :
    ((ell : ℝ) * p) / 2 ≤ (ell : ℝ) * p * (1 - (p : ℝ)) ^ (ell - 1) := by
  have hpReal : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hPrevious : ((ell - 1 : ℕ) : ℝ) * p ≤ (ell : ℝ) * p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le ell 1) p.coe_nonneg
  have hZero := bernoulli_zero_pattern_failure_le hpReal (ell - 1)
  have hPower : 1 / 2 ≤ (1 - (p : ℝ)) ^ (ell - 1) := by linarith
  have h := mul_le_mul_of_nonneg_left hPower (mul_nonneg (Nat.cast_nonneg ell) p.coe_nonneg)
  simpa only [div_eq_mul_inv, one_mul] using h

theorem bernoulli_laplace_factor_nonneg {q t : ℝ} (hq : 0 ≤ q) (hqOne : q ≤ 1) :
    0 ≤ 1 + (Real.exp (-t) - 1) * q := by
  nlinarith [mul_nonneg (Real.exp_pos (-t)).le hq]

theorem bernoulli_zero_pattern_laplace_factor_le (p : ℝ≥0) (hp : p ≤ 1)
    (ell : ℕ) (t : ℝ) :
    1 + (Real.exp (-t) - 1) * (1 - (p : ℝ)) ^ ell ≤ (ell : ℝ) * p + Real.exp (-t) := by
  have hpReal : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hPow : (1 - (p : ℝ)) ^ ell ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hpReal)
    (by linarith [p.coe_nonneg])
  have hZero := bernoulli_zero_pattern_failure_le hpReal ell
  nlinarith [mul_le_mul_of_nonneg_left hPow (Real.exp_pos (-t)).le]

theorem bernoulli_single_pattern_laplace_factor_le (p : ℝ≥0) (hp : p ≤ 1)
    (ell : ℕ) (t : ℝ) (hSmall : (ell : ℝ) * p ≤ 1 / 2)
    (hExp : Real.exp (-t) ≤ 1 / 2) :
    1 + (Real.exp (-t) - 1) * ((ell : ℝ) * p * (1 - (p : ℝ)) ^ (ell - 1)) ≤
      Real.exp (-((ell : ℝ) * p) / 4) := by
  have hSingle := bernoulli_single_pattern_small_set_lower p hp ell hSmall
  have hCoeff : Real.exp (-t) - 1 ≤ 0 := by linarith
  have hMultiply := mul_le_mul_of_nonpos_left hSingle hCoeff
  have hCount : 0 ≤ (ell : ℝ) * p := mul_nonneg (Nat.cast_nonneg ell) p.coe_nonneg
  have hExpBound := Real.add_one_le_exp (-((ell : ℝ) * p) / 4)
  nlinarith [mul_le_mul_of_nonneg_right hExp hCount]

theorem bernoulli_unique_neighbourhood_small_set_lower_tail
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (e : ρ ↪ ι) (S : Finset ι) {β t : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (ht : 0 ≤ t)
    (hSmall : (S.card : ℝ) * p ≤ 1 / 2) (hExp : Real.exp (-t) ≤ 1 / 2) (u : ℝ) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤ u} ≤
        Real.exp (t * u) * ((S.card : ℝ) * p + Real.exp (-t)) ^
          (bernoulliUniqueInsideRows e S).card *
        Real.exp (-((Fintype.card ρ - (bernoulliUniqueInsideRows e S).card : ℕ) : ℝ) *
          ((S.card : ℝ) * p) / 4) := by
  apply (bernoulli_unique_neighbourhood_lower_tail_two_factors p hp e S hβ hβOne ht u).trans
  have hZeroBounds : 0 ≤ (1 - (p : ℝ)) ^ S.card ∧ (1 - (p : ℝ)) ^ S.card ≤ 1 := by
    rw [← bernoulli_row_zero_probability p hp S]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hSingleBounds : 0 ≤ (S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1) ∧
      (S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1) ≤ 1 := by
    rw [← bernoulli_row_exactly_one_probability p hp S]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hInside := pow_le_pow_left₀ (bernoulli_laplace_factor_nonneg hZeroBounds.1 hZeroBounds.2)
    (bernoulli_zero_pattern_laplace_factor_le p hp S.card t) (bernoulliUniqueInsideRows e S).card
  have hOutside := pow_le_pow_left₀ (bernoulli_laplace_factor_nonneg hSingleBounds.1 hSingleBounds.2)
    (bernoulli_single_pattern_laplace_factor_le p hp S.card t hSmall hExp)
    (Fintype.card ρ - (bernoulliUniqueInsideRows e S).card)
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hInside (Real.exp_pos _).le) hOutside
    (pow_nonneg (bernoulli_laplace_factor_nonneg hSingleBounds.1 hSingleBounds.2) _)
    (by positivity)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

end CircularLaw
