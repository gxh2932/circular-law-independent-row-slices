import CircularLaw.CompactMomentConvergence

/-!
# Polynomial approximation with an actual high-moment tail bound

Approximation on a fixed interval controls the bulk of a nonnegative
array. Outside it, a polynomial grows at most as a fixed power, and a
higher empirical moment bounds its error. No samplewise operator-norm
bound is required. Compact target moments have the corresponding fixed
power bound, so the higher-order tail coefficient can be made small.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

def polynomialAbsoluteCoefficientSum (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ p.support, |p.coeff k|

theorem polynomial_absolute_coefficient_sum_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialAbsoluteCoefficientSum p := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem polynomial_eval_abs_power_bound (p : Polynomial ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |p.eval x| ≤ polynomialAbsoluteCoefficientSum p * x ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  calc
    _ ≤ ∑ k ∈ p.support, |p.coeff k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ p.support, |p.coeff k| * x ^ k := by
      simp only [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ x) _)]
    _ ≤ ∑ k ∈ p.support, |p.coeff k| * x ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hx (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)))
        (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem bounded_test_polynomial_power_error (p : Polynomial ℝ) (f : ℝ → ℝ) (M : ℝ)
    (hBound : ∀ x, |f x| ≤ M) {x : ℝ} (hx : 1 ≤ x) :
    |f x - p.eval x| ≤ (|M| + polynomialAbsoluteCoefficientSum p + 1) * x ^ p.natDegree := by
  have hPow : 1 ≤ x ^ p.natDegree := one_le_pow₀ hx
  have hF := (hBound x).trans (le_abs_self M)
  have hP := polynomial_eval_abs_power_bound p hx
  have hFM := mul_le_mul_of_nonneg_left hPow (abs_nonneg M)
  have hC := polynomial_absolute_coefficient_sum_nonneg p
  have hTriangle := abs_sub_le (f x) 0 (p.eval x)
  simp only [sub_zero, zero_sub, abs_neg] at hTriangle
  nlinarith

theorem polynomial_high_moment_pointwise_error (p : Polynomial ℝ) (f : ℝ → ℝ) (M S ε : ℝ)
    (hBound : ∀ x, |f x| ≤ M) (hS : 1 ≤ S) (hε : 0 ≤ ε)
    (hApprox : ∀ x ∈ Set.Icc (0 : ℝ) S, |p.eval x - f x| ≤ ε)
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |f x - p.eval x| ≤ ε +
      ((|M| + polynomialAbsoluteCoefficientSum p + 1) / S ^ k) * x ^ (p.natDegree + k) := by
  let C := |M| + polynomialAbsoluteCoefficientSum p + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg M, polynomial_absolute_coefficient_sum_nonneg p]
  have hSPos : 0 < S := by linarith
  by_cases hxS : x ≤ S
  · have hA := hApprox x ⟨hx, hxS⟩
    rw [abs_sub_comm] at hA
    exact hA.trans (le_add_of_nonneg_right (by positivity))
  · have hxLarge : S ≤ x := (lt_of_not_ge hxS).le
    have hP := bounded_test_polynomial_power_error p f M hBound (hS.trans hxLarge)
    have hPow : S ^ k ≤ x ^ k := pow_le_pow_left₀ hSPos.le hxLarge k
    have hTail : C * x ^ p.natDegree ≤ (C / S ^ k) * x ^ (p.natDegree + k) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (pow_pos hSPos k)).mpr
      calc
        _ ≤ (C * x ^ p.natDegree) * x ^ k := mul_le_mul_of_nonneg_left hPow (by positivity)
        _ = _ := by rw [pow_add]; ring
    exact hP.trans (hTail.trans (le_add_of_nonneg_left hε))

theorem polynomial_high_moment_finite_mean_error {α : Type*} [Fintype α] [Nonempty α]
    (p : Polynomial ℝ) (f : ℝ → ℝ) (M S ε : ℝ) (hBound : ∀ x, |f x| ≤ M)
    (hS : 1 ≤ S) (hε : 0 ≤ ε)
    (hApprox : ∀ x ∈ Set.Icc (0 : ℝ) S, |p.eval x - f x| ≤ ε)
    (k : ℕ) (s : α → ℝ) (hs : ∀ a, 0 ≤ s a) :
    |finiteMean (fun a => f (s a)) - finiteMean (fun a => p.eval (s a))| ≤
      ε + ((|M| + polynomialAbsoluteCoefficientSum p + 1) / S ^ k) *
        finiteMean (fun a => s a ^ (p.natDegree + k)) := by
  rw [← finiteMean_sub]
  apply (abs_finiteMean_le _).trans
  calc
    _ ≤ finiteMean (fun a => ε +
        ((|M| + polynomialAbsoluteCoefficientSum p + 1) / S ^ k) * s a ^ (p.natDegree + k)) :=
      finiteMean_mono (fun a => polynomial_high_moment_pointwise_error p f M S ε
        hBound hS hε hApprox k (hs a))
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_const_mul]

theorem compact_probability_moment_upper_bound {R : ℝ}
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R)) (m : ℕ) :
    (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) ≤ R ^ m := by
  have hInt : Integrable (fun t : Set.Icc (0 : ℝ) R => (t : ℝ) ^ m)
      (ν : Measure (Set.Icc (0 : ℝ) R)) :=
    (continuous_subtype_val.pow m).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hInt (integrable_const (R ^ m))
    (fun t => pow_le_pow_left₀ t.property.1 t.property.2 m)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem high_moment_tail_coefficient_exists {R S C ε : ℝ} (hR : 0 ≤ R)
    (hS : 0 < S) (hRS : R < S) (hε : 0 < ε) (N : ℕ) :
    ∃ k : ℕ, (C / S ^ k) * R ^ (N + k) < ε := by
  have hRatio : 0 ≤ R / S := div_nonneg hR hS.le
  have hRatioLt : R / S < 1 := (div_lt_one hS).mpr hRS
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hRatio hRatioLt).const_mul (C * R ^ N)
  simp only [mul_zero] at h
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds hε)).exists
  refine ⟨k, ?_⟩
  have hEq : (C / S ^ k) * R ^ (N + k) = (C * R ^ N) * (R / S) ^ k := by
    rw [pow_add, div_pow]
    ring
  rwa [hEq]

end CircularLaw
