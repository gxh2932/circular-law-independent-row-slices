import CircularLaw.RegularBlock
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Canonical complex lattice approximation

The manuscript's coordinatewise floor approximation is an actual grid
point, with error at most `sqrt(2)/k`. Distinct grid points have distance
at least `1/k`, supplying the regular-block geometric hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gridValue (k : ℕ) (a b : ℤ) : ℂ :=
  ⟨(a : ℝ) / (k : ℝ), (b : ℝ) / (k : ℝ)⟩

def canonicalApprox (k : ℕ) (z : ℂ) : ℂ :=
  gridValue k ⌊(k : ℝ) * z.re⌋ ⌊(k : ℝ) * z.im⌋

def IsKVector {ι : Type*} (k : ℕ) (y : ι → ℂ) : Prop :=
  ∀ i, ∃ a b : ℤ, y i = gridValue k a b

theorem canonicalApprox_isKVector {ι : Type*} (k : ℕ) (x : ι → ℂ) :
    IsKVector k (fun i => canonicalApprox k (x i)) :=
  fun i => ⟨⌊(k : ℝ) * (x i).re⌋, ⌊(k : ℝ) * (x i).im⌋, rfl⟩

theorem gridValue_mul (k : ℕ) (hk : 0 < k) (a b : ℤ) :
    (k : ℂ) * gridValue k a b = (a : ℂ) + (b : ℂ) * Complex.I := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply Complex.ext
  · simp only [gridValue, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_div_cancel₀ _ hkR.ne'
  · simp only [gridValue, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, add_zero, zero_add]
    exact mul_div_cancel₀ _ hkR.ne'

theorem canonicalApprox_eq_source {k : ℕ} (hk : 0 < k) (z : ℂ) :
    canonicalApprox k z =
      ((⌊(k : ℝ) * z.re⌋ : ℂ) + (⌊(k : ℝ) * z.im⌋ : ℂ) * Complex.I) / (k : ℂ) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  apply (eq_div_iff hkC).mpr
  rw [mul_comm]
  exact gridValue_mul k hk _ _

theorem isKVector_iff_scaled_lattice {ι : Type*} {k : ℕ} (hk : 0 < k) (y : ι → ℂ) :
    IsKVector k y ↔ ∀ i, ∃ a b : ℤ,
      (k : ℂ) * y i = (a : ℂ) + (b : ℂ) * Complex.I := by
  constructor
  · intro h i
    obtain ⟨a, b, hi⟩ := h i
    exact ⟨a, b, by rw [hi]; exact gridValue_mul k hk a b⟩
  · intro h i
    obtain ⟨a, b, hi⟩ := h i
    refine ⟨a, b, ?_⟩
    apply mul_left_cancel₀ (by exact_mod_cast hk.ne' : (k : ℂ) ≠ 0)
    rw [hi, gridValue_mul k hk a b]

theorem real_floor_approx_error {k : ℕ} (hk : 0 < k) (x : ℝ) :
    0 ≤ x - (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) ∧
      x - (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) < 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using Int.floor_le ((k : ℝ) * x)))
  · apply (lt_div_iff₀ hkR).mpr
    have h := Int.lt_floor_add_one ((k : ℝ) * x)
    have hCancel : (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) * (k : ℝ) = ⌊(k : ℝ) * x⌋ :=
      div_mul_cancel₀ _ hkR.ne'
    nlinarith

theorem canonicalApprox_norm_error {k : ℕ} (hk : 0 < k) (z : ℂ) :
    ‖z - canonicalApprox k z‖ ≤ Real.sqrt 2 / (k : ℝ) := by
  have hRe := real_floor_approx_error hk z.re
  have hIm := real_floor_approx_error hk z.im
  have hReAbs : |(z - canonicalApprox k z).re| ≤ 1 / (k : ℝ) := by
    simpa only [Complex.sub_re, canonicalApprox, gridValue, abs_of_nonneg hRe.1] using hRe.2.le
  have hImAbs : |(z - canonicalApprox k z).im| ≤ 1 / (k : ℝ) := by
    simpa only [Complex.sub_im, canonicalApprox, gridValue, abs_of_nonneg hIm.1] using hIm.2.le
  calc
    _ ≤ Real.sqrt 2 * max |(z - canonicalApprox k z).re| |(z - canonicalApprox k z).im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (max_le hReAbs hImAbs) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem int_cast_gap {a b : ℤ} (hne : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  by_cases hab : a < b
  · have h : a + 1 ≤ b := by omega
    have hR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h
    rw [abs_of_neg (by linarith : (a : ℝ) - (b : ℝ) < 0)]
    linarith
  · have h : b + 1 ≤ a := by omega
    have hR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith : 0 < (a : ℝ) - (b : ℝ))]
    linarith

theorem gridValue_separated {k : ℕ} (hk : 0 < k) {a b c d : ℤ}
    (hne : gridValue k a b ≠ gridValue k c d) :
    1 / (k : ℝ) ≤ dist (gridValue k a b) (gridValue k c d) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hPairs : a ≠ c ∨ b ≠ d := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hne (by rw [h.1, h.2])
  rw [dist_eq_norm]
  rcases hPairs with h | h
  · have hNorm := Complex.abs_re_le_norm (gridValue k a b - gridValue k c d)
    have hGap := div_le_div_of_nonneg_right (int_cast_gap h) hkR.le
    simp only [Complex.sub_re, gridValue, ← sub_div, abs_div, abs_of_pos hkR] at hNorm
    exact hGap.trans hNorm
  · have hNorm := Complex.abs_im_le_norm (gridValue k a b - gridValue k c d)
    have hGap := div_le_div_of_nonneg_right (int_cast_gap h) hkR.le
    simp only [Complex.sub_im, gridValue, ← sub_div, abs_div, abs_of_pos hkR] at hNorm
    exact hGap.trans hNorm

theorem kVector_values_separated {ι : Type*} {k : ℕ} (hk : 0 < k) {y : ι → ℂ}
    (hy : IsKVector k y) :
    (Set.range y).Pairwise (fun a b => 1 / (k : ℝ) ≤ dist a b) := by
  intro a ha b hb hab
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨ai, bi, hi⟩ := hy i
  obtain ⟨aj, bj, hj⟩ := hy j
  rw [hi, hj] at hab ⊢
  exact gridValue_separated hk hab

theorem canonicalApprox_sum_error {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 0 < k) (x : ι → ℂ) :
    ‖(∑ i, x i) - ∑ i, canonicalApprox k (x i)‖ ≤
      (Fintype.card ι : ℝ) * (Real.sqrt 2 / (k : ℝ)) := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (by
    calc
      _ ≤ ∑ _ : ι, Real.sqrt 2 / (k : ℝ) :=
        Finset.sum_le_sum (fun i _ => canonicalApprox_norm_error hk (x i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])

end CircularLaw
