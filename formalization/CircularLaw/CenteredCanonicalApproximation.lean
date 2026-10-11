import CircularLaw.Discretization
import CircularLaw.SteepNetMatrixError

/-!
# The actual mean and centered canonical rounding error

Coordinatewise floor rounding has nonnegative real and imaginary
errors below `1/k`. Their means have the same strict bounds. Removing
the mean leaves a vector whose coordinate sum is zero, with the source
Euclidean error bound up to an explicit absolute constant.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def canonicalErrorMean {n : ℕ} (k : ℕ) (x : Fin n → ℂ) : ℂ :=
  (∑ j, (x j - canonicalApprox k (x j))) / (n : ℂ)

def centeredCanonicalError {n : ℕ} (k : ℕ) (x : Fin n → ℂ) (j : Fin n) : ℂ :=
  x j - canonicalApprox k (x j) - canonicalErrorMean k x

theorem coordinate_real_mean_range {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ)
    {ε : ℝ} (hRange : ∀ j, 0 ≤ f j ∧ f j < ε) :
    0 ≤ (∑ j, f j) / n ∧ (∑ j, f j) / n < ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_nonneg (Finset.sum_nonneg (fun j _ => (hRange j).1)) hnR.le, ?_⟩
  apply (div_lt_iff₀ hnR).mpr
  have hNonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hSum := Finset.sum_lt_sum_of_nonempty hNonempty (fun j _ => (hRange j).2)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hSum

theorem canonicalErrorMean_component_ranges {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (x : Fin n → ℂ) :
    (0 ≤ (canonicalErrorMean k x).re ∧ (canonicalErrorMean k x).re < 1 / (k : ℝ)) ∧
    (0 ≤ (canonicalErrorMean k x).im ∧ (canonicalErrorMean k x).im < 1 / (k : ℝ)) := by
  have hRe := coordinate_real_mean_range hn
    (fun j => (x j).re - (⌊(k : ℝ) * (x j).re⌋ : ℝ) / k)
    (fun j => real_floor_approx_error hk (x j).re)
  have hIm := coordinate_real_mean_range hn
    (fun j => (x j).im - (⌊(k : ℝ) * (x j).im⌋ : ℝ) / k)
    (fun j => real_floor_approx_error hk (x j).im)
  simpa only [canonicalErrorMean, Complex.div_natCast_re, Complex.div_natCast_im,
    Complex.re_sum, Complex.im_sum, Complex.sub_re, Complex.sub_im, canonicalApprox, gridValue]
    using And.intro hRe hIm

theorem canonicalErrorMean_norm_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (x : Fin n → ℂ) : ‖canonicalErrorMean k x‖ ≤ Real.sqrt 2 / (k : ℝ) := by
  have hRange := canonicalErrorMean_component_ranges hn hk x
  calc
    _ ≤ Real.sqrt 2 * max |(canonicalErrorMean k x).re| |(canonicalErrorMean k x).im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left
      (max_le (by simpa only [abs_of_nonneg hRange.1.1] using hRange.1.2.le)
        (by simpa only [abs_of_nonneg hRange.2.1] using hRange.2.2.le)) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem centeredCanonicalError_sum {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Fin n → ℂ) :
    ∑ j, centeredCanonicalError k x j = 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [centeredCanonicalError, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, canonicalErrorMean]
  field_simp
  ring

theorem centeredCanonicalError_decomposition {n : ℕ} (k : ℕ) (x : Fin n → ℂ) (j : Fin n) :
    x j = canonicalApprox k (x j) + centeredCanonicalError k x j + canonicalErrorMean k x := by
  unfold centeredCanonicalError
  ring

theorem centeredCanonicalError_coordinate_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (x : Fin n → ℂ) (j : Fin n) :
    ‖centeredCanonicalError k x j‖ ≤ 2 * Real.sqrt 2 / (k : ℝ) := by
  unfold centeredCanonicalError
  calc
    _ ≤ ‖x j - canonicalApprox k (x j)‖ + ‖canonicalErrorMean k x‖ := norm_sub_le _ _
    _ ≤ Real.sqrt 2 / (k : ℝ) + Real.sqrt 2 / (k : ℝ) :=
      add_le_add (canonicalApprox_norm_error hk (x j)) (canonicalErrorMean_norm_bound hn hk x)
    _ = _ := by ring

theorem centeredCanonicalError_euclidean_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (x : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (centeredCanonicalError k x) : EuclideanSpace ℂ (Fin n))‖ ≤
      2 * Real.sqrt 2 * Real.sqrt n / (k : ℝ) := by
  have hBound := euclidean_norm_le_uniform (centeredCanonicalError k x)
    (by positivity : 0 ≤ 2 * Real.sqrt 2 / (k : ℝ))
    (centeredCanonicalError_coordinate_bound hn hk x)
  simpa only [Fintype.card_fin, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hBound

end CircularLaw
