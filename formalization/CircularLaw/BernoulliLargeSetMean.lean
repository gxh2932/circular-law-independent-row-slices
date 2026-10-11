import CircularLaw.BernoulliUniqueCountStructure
import CircularLaw.SourceGraphGrowthRange

/-!
# A lower bound on the actual unique-neighbourhood mean for larger sets

The Bernoulli single-one probability is bounded directly, using
log(1-p) >= -2p for p <= one half. In the source terminal range,
at least half the ambient rows remain outside the column set.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem log_one_sub_probability_lower {p : ℝ} (hp : 0 ≤ p) (hHalf : p ≤ 1 / 2) :
    -2 * p ≤ Real.log (1 - p) := by
  have hPos : 0 < 1 - p := by linarith
  have hInv : (1 - p)⁻¹ ≤ 1 + 2 * p := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hPos).mpr
    nlinarith [mul_nonneg hp (by linarith : 0 ≤ 1 - 2 * p)]
  linarith [Real.one_sub_inv_le_log_of_pos hPos]

theorem bernoulli_zero_pattern_exponential_lower (p : ℝ≥0)
    (hHalf : (p : ℝ) ≤ 1 / 2) (ell : ℕ) :
    Real.exp (-2 * (ell : ℝ) * p) ≤ (1 - (p : ℝ)) ^ (ell - 1) := by
  have hPos : 0 < 1 - (p : ℝ) := by linarith
  have hLog := log_one_sub_probability_lower p.coe_nonneg hHalf
  have hMul := mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg (ell - 1) : (0 : ℝ) ≤ (ell - 1 : ℕ))
  have hCard : ((ell - 1 : ℕ) : ℝ) ≤ ell := by exact_mod_cast Nat.sub_le ell 1
  have hNeg := mul_le_mul_of_nonpos_right hCard (by linarith [p.coe_nonneg] : -2 * (p : ℝ) ≤ 0)
  rw [← Real.exp_log (pow_pos hPos (ell - 1)), Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem bernoulli_single_pattern_large_set_lower (p : ℝ≥0)
    (hHalf : (p : ℝ) ≤ 1 / 2) (ell : ℕ) {d : ℝ} (hLog : 0 < Real.log d)
    (hLarge : 1 / 2 ≤ (ell : ℝ) * p)
    (hRange : (ell : ℝ) * p ≤ Real.log (Real.log d) / 2) :
    1 / (2 * Real.log d) ≤ (ell : ℝ) * p * (1 - (p : ℝ)) ^ (ell - 1) := by
  have hExp : 1 / Real.log d ≤ Real.exp (-2 * (ell : ℝ) * p) := by
    have h := Real.exp_le_exp.mpr (show -Real.log (Real.log d) ≤ -2 * (ell : ℝ) * p by linarith)
    rwa [Real.exp_neg, Real.exp_log hLog, inv_eq_one_div] at h
  have hPower := hExp.trans (bernoulli_zero_pattern_exponential_lower p hHalf ell)
  calc
    _ = (1 / 2 : ℝ) * (1 / Real.log d) := by field_simp
    _ ≤ ((ell : ℝ) * p) * (1 / Real.log d) :=
      mul_le_mul_of_nonneg_right hLarge (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hPower (by positivity)

theorem bernoulli_large_set_ambient_mean_lower
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] {N : ℕ}
    (hN : 0 < N) (hRows : 3 * (N : ℝ) / 4 ≤ Fintype.card ρ)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2)
    (e : ρ ↪ ι) (S : Finset ι) {d : ℝ} (hLog : 0 < Real.log d)
    (hLarge : 1 / 2 ≤ (S.card : ℝ) * p)
    (hRange : (S.card : ℝ) * p ≤ Real.log (Real.log d) / 2)
    (hSize : (S.card : ℝ) ≤ (N : ℝ) / 4) :
    (N : ℝ) / (4 * Real.log d) ≤ bernoulliUniqueNeighbourhoodMean p e S := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hCard : S.card ≤ Fintype.card ρ := by
    have hReal : (S.card : ℝ) ≤ Fintype.card ρ := by linarith
    exact_mod_cast hReal
  have hOutside : (N : ℝ) / 2 ≤ ((Fintype.card ρ - S.card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hCard]
    linarith
  have hSingle := bernoulli_single_pattern_large_set_lower p hHalf S.card hLog hLarge hRange
  have hProduct := mul_le_mul hOutside hSingle (by positivity : 0 ≤ 1 / (2 * Real.log d))
    (Nat.cast_nonneg (Fintype.card ρ - S.card) : (0 : ℝ) ≤ (Fintype.card ρ - S.card : ℕ))
  have hEq : (N : ℝ) / 2 * (1 / (2 * Real.log d)) = (N : ℝ) / (4 * Real.log d) := by field_simp; norm_num
  rw [hEq] at hProduct
  exact hProduct.trans (bernoulli_unique_neighbourhood_mean_outside_lower p hp e S)

end CircularLaw
