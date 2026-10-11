import CircularLaw.ComplexGaussianDensity
import CircularLaw.PlanarGaussian
import CircularLaw.ProjectedComplexGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact exponential moments of the complex Gaussian norm

The variance-one-half planar density gives `E exp(t |G|²) = 1/(1-t)`
for every real `t<1`. The actual coordinate product law then gives the
dimension power, which supplies upper and lower Gaussian norm tails.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem standardComplexGaussianDensity_exponential (t : ℝ) (z : ℂ) :
    standardComplexGaussianDensity z * Real.exp (t * ‖z‖ ^ 2) =
      Real.pi⁻¹ * planarGaussian (1 - t) z := by
  unfold standardComplexGaussianDensity planarGaussian
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem standardComplexGaussianLaw_normSq_exponential_integrable {t : ℝ} (ht : t < 1) :
    Integrable (fun z : ℂ => Real.exp (t * ‖z‖ ^ 2)) standardComplexGaussianLaw := by
  have hD : Measurable (fun z => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  have hNonneg (z : ℂ) : 0 ≤ standardComplexGaussianDensity z := by
    unfold standardComplexGaussianDensity
    positivity
  rw [standardComplexGaussianLaw_density, densityLaw,
    integrable_withDensity_iff_integrable_smul' hD
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hNonneg _), smul_eq_mul,
    standardComplexGaussianDensity_exponential]
  exact (planarGaussian_integrable (sub_pos.mpr ht)).const_mul _

theorem standardComplexGaussianLaw_normSq_exponential_integral {t : ℝ} (ht : t < 1) :
    (∫ z : ℂ, Real.exp (t * ‖z‖ ^ 2) ∂standardComplexGaussianLaw) = (1 - t)⁻¹ := by
  have hD : Measurable (fun z => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  have hNonneg (z : ℂ) : 0 ≤ standardComplexGaussianDensity z := by
    unfold standardComplexGaussianDensity
    positivity
  rw [standardComplexGaussianLaw_density, densityLaw,
    integral_withDensity_eq_integral_toReal_smul hD
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hNonneg _), smul_eq_mul,
    standardComplexGaussianDensity_exponential]
  rw [integral_const_mul, planarGaussian_integral (sub_pos.mpr ht)]
  field_simp

theorem standardComplexGaussianVector_normSq_exponential_eq_prod (n : ℕ) (t : ℝ)
    (z : Fin n → ℂ) : Real.exp (t * ‖standardComplexGaussianVector n z‖ ^ 2) =
      ∏ i, Real.exp (t * ‖z i‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  rfl

theorem standardComplexGaussianVector_normSq_exponential_integrable (n : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun z => Real.exp (t * ‖standardComplexGaussianVector n z‖ ^ 2))
      (standardComplexGaussianVectorLaw n) := by
  simp_rw [standardComplexGaussianVector_normSq_exponential_eq_prod]
  exact Integrable.fintype_prod (fun _ : Fin n =>
    standardComplexGaussianLaw_normSq_exponential_integrable ht)

theorem standardComplexGaussianVector_normSq_exponential_integral (n : ℕ) {t : ℝ} (ht : t < 1) :
    (∫ z, Real.exp (t * ‖standardComplexGaussianVector n z‖ ^ 2)
      ∂standardComplexGaussianVectorLaw n) = ((1 - t)⁻¹) ^ n := by
  simp_rw [standardComplexGaussianVector_normSq_exponential_eq_prod]
  rw [standardComplexGaussianVectorLaw,
    integral_fintype_prod_eq_prod (fun _ : Fin n => fun z : ℂ => Real.exp (t * ‖z‖ ^ 2))]
  simp [standardComplexGaussianLaw_normSq_exponential_integral ht]

theorem standardComplexGaussianVector_normSq_upper_tail (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | u ≤ ‖standardComplexGaussianVector n z‖ ^ 2} ≤
      ((1 - t)⁻¹) ^ n * Real.exp (-t * u) := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (standardComplexGaussianVectorLaw n) (fun z =>
      (Real.exp_pos (t * ‖standardComplexGaussianVector n z‖ ^ 2)).le))
    (standardComplexGaussianVector_normSq_exponential_integrable n ht1) (Real.exp (t * u))
  have hSubset : {z | u ≤ ‖standardComplexGaussianVector n z‖ ^ 2} ⊆
      {z | Real.exp (t * u) ≤ Real.exp (t * ‖standardComplexGaussianVector n z‖ ^ 2)} := by
    intro z hz
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz ht)
  have hEvent := measureReal_mono (μ := standardComplexGaussianVectorLaw n) hSubset
  have hMul := (mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (t * u)).le).trans hMark
  rw [standardComplexGaussianVector_normSq_exponential_integral n ht1] at hMul
  calc
    _ ≤ ((1 - t)⁻¹) ^ n / Real.exp (t * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hMul)
    _ = _ := by simp [div_eq_mul_inv, neg_mul, Real.exp_neg]

theorem standardComplexGaussianVector_normSq_lower_tail (n : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖standardComplexGaussianVector n z‖ ^ 2 ≤ u} ≤
      ((1 + a)⁻¹) ^ n * Real.exp (a * u) := by
  have ht1 : -a < 1 := by linarith only [ha]
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (standardComplexGaussianVectorLaw n) (fun z =>
      (Real.exp_pos (-a * ‖standardComplexGaussianVector n z‖ ^ 2)).le))
    (standardComplexGaussianVector_normSq_exponential_integrable n ht1) (Real.exp (-a * u))
  have hSubset : {z | ‖standardComplexGaussianVector n z‖ ^ 2 ≤ u} ⊆
      {z | Real.exp (-a * u) ≤ Real.exp (-a * ‖standardComplexGaussianVector n z‖ ^ 2)} := by
    intro z hz
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr ha))
  have hEvent := measureReal_mono (μ := standardComplexGaussianVectorLaw n) hSubset
  have hMul := (mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (-a * u)).le).trans hMark
  rw [standardComplexGaussianVector_normSq_exponential_integral n ht1, sub_neg_eq_add] at hMul
  calc
    _ ≤ ((1 + a)⁻¹) ^ n / Real.exp (-a * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hMul)
    _ = _ := by simp [div_eq_mul_inv, neg_mul, Real.exp_neg]

theorem standardComplexGaussianVector_normSq_smallBall {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖standardComplexGaussianVector n z‖ ^ 2 ≤ u} ≤
      (Real.exp 1 * u / n) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hTail := standardComplexGaussianVector_normSq_lower_tail n
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

theorem standardComplexGaussianVector_normSq_upper_half_tail (n : ℕ) (u : ℝ) :
    (standardComplexGaussianVectorLaw n).real
      {z | u ≤ ‖standardComplexGaussianVector n z‖ ^ 2} ≤
      (2 : ℝ) ^ n * Real.exp (-u / 2) := by
  have h := standardComplexGaussianVector_normSq_upper_tail n
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) u
  convert h using 1
  norm_num
  ring

end CircularLaw
