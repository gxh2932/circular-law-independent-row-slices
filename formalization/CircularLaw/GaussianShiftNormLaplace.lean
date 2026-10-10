import CircularLaw.ComplexGaussianShiftLaplace

/-!
# Shifted Gaussian norm bounds with the actual dimension

Independence gives the exact lower Laplace transform of the shifted
Gaussian vector. The deterministic shift decreases this transform, so
Markov's inequality gives the same lower tail and small-ball bound as
in the centered case, uniformly over every deterministic shift.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem standardComplexGaussianVector_shift_lower_exponential_eq_prod {n : ℕ}
    (a : ℝ) (w : EuclideanSpace ℂ (Fin n)) (z : Fin n → ℂ) :
    Real.exp (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2) =
      ∏ i, Real.exp (-a * ‖z i + w i‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  rfl

theorem standardComplexGaussianVector_shift_lower_exponential_integrable {n : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (w : EuclideanSpace ℂ (Fin n)) :
    Integrable (fun z => Real.exp (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2))
      (standardComplexGaussianVectorLaw n) := by
  simp_rw [standardComplexGaussianVector_shift_lower_exponential_eq_prod]
  exact Integrable.fintype_prod (fun i : Fin n =>
    standardComplexGaussianLaw_shift_lower_exponential_integrable ha (w i))

theorem standardComplexGaussianVector_shift_lower_exponential_integral {n : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (w : EuclideanSpace ℂ (Fin n)) :
    (∫ z, Real.exp (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2)
      ∂standardComplexGaussianVectorLaw n) =
        ((1 + a)⁻¹) ^ n * Real.exp (-(a / (1 + a)) * ‖w‖ ^ 2) := by
  simp_rw [standardComplexGaussianVector_shift_lower_exponential_eq_prod]
  rw [standardComplexGaussianVectorLaw,
    integral_fintype_prod_eq_prod (fun i : Fin n => fun z : ℂ => Real.exp (-a * ‖z + w i‖ ^ 2))]
  simp only [standardComplexGaussianLaw_shift_lower_exponential_integral ha,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem standardComplexGaussianVector_shift_lower_exponential_integral_le {n : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (w : EuclideanSpace ℂ (Fin n)) :
    (∫ z, Real.exp (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2)
      ∂standardComplexGaussianVectorLaw n) ≤ ((1 + a)⁻¹) ^ n := by
  rw [standardComplexGaussianVector_shift_lower_exponential_integral ha]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)))

theorem standardComplexGaussianVector_shift_normSq_lower_tail {n : ℕ}
    (w : EuclideanSpace ℂ (Fin n)) {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖standardComplexGaussianVector n z + w‖ ^ 2 ≤ u} ≤
        ((1 + a)⁻¹) ^ n * Real.exp (a * u) := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (standardComplexGaussianVectorLaw n) (fun z =>
      (Real.exp_pos (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2)).le))
    (standardComplexGaussianVector_shift_lower_exponential_integrable ha w) (Real.exp (-a * u))
  have hSubset : {z | ‖standardComplexGaussianVector n z + w‖ ^ 2 ≤ u} ⊆
      {z | Real.exp (-a * u) ≤ Real.exp (-a * ‖standardComplexGaussianVector n z + w‖ ^ 2)} := by
    intro z hz
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr ha))
  have hEvent := measureReal_mono (μ := standardComplexGaussianVectorLaw n) hSubset
  have hMul := ((mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (-a * u)).le).trans hMark).trans
    (standardComplexGaussianVector_shift_lower_exponential_integral_le ha w)
  calc
    _ ≤ ((1 + a)⁻¹) ^ n / Real.exp (-a * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hMul)
    _ = _ := by simp [div_eq_mul_inv, neg_mul, Real.exp_neg]

theorem standardComplexGaussianVector_shift_normSq_smallBall {n : ℕ} (hn : 0 < n)
    (w : EuclideanSpace ℂ (Fin n)) {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖standardComplexGaussianVector n z + w‖ ^ 2 ≤ u} ≤
        (Real.exp 1 * u / n) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hTail := standardComplexGaussianVector_shift_normSq_lower_tail w
    (div_nonneg hnR.le hu.le) u
  have hInv : (1 + (n : ℝ) / u)⁻¹ ≤ u / n := by
    simpa only [one_div, inv_div] using one_div_le_one_div_of_le (div_pos hnR hu)
      (by linarith : (n : ℝ) / u ≤ 1 + (n : ℝ) / u)
  have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + (n : ℝ) / u)⁻¹) hInv n
  apply hTail.trans
  calc
    _ ≤ (u / n) ^ n * Real.exp ((n : ℝ) / u * u) :=
      mul_le_mul_of_nonneg_right hPow (Real.exp_pos _).le
    _ = (u / n) ^ n * Real.exp (n : ℝ) := by rw [div_mul_cancel₀ _ hu.ne']
    _ = _ := by rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]; ring

end CircularLaw
