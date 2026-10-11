import CircularLaw.PlanarPacking
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# The dilation estimate for characteristic functions

The Fourier-power argument in LLTTY19 Lemma 2.6 uses
`1 - |f(k*x)|^2 <= k^2 * (1 - |f(x)|^2)`. This file proves that inequality
for arbitrary probability laws, by symmetrization and a cosine estimate.
It does not assume a density or a Fourier-power estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Convolution

namespace CircularLaw

theorem abs_sin_nat_mul_le (k : ℕ) (x : ℝ) :
    |Real.sin ((k : ℝ) * x)| ≤ (k : ℝ) * |Real.sin x| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((k : ℝ) * x) * Real.cos x| +
          |Real.cos ((k : ℝ) * x) * Real.sin x| := abs_add_le _ _
      _ ≤ |Real.sin ((k : ℝ) * x)| + |Real.sin x| := by
        rw [abs_mul, abs_mul]
        apply add_le_add
        · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
        · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ (k : ℝ) * |Real.sin x| + |Real.sin x| := add_le_add ih le_rfl
      _ = _ := by ring

theorem sin_nat_mul_sq_le (k : ℕ) (x : ℝ) :
    Real.sin ((k : ℝ) * x) ^ 2 ≤ (k : ℝ) ^ 2 * Real.sin x ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_sin_nat_mul_le k x) 2
  simpa only [sq_abs, mul_pow] using h

theorem one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  linarith

theorem one_sub_cos_nat_mul_le (k : ℕ) (x : ℝ) :
    1 - Real.cos ((k : ℝ) * x) ≤ (k : ℝ) ^ 2 * (1 - Real.cos x) := by
  rw [one_sub_cos_eq_two_sin_sq, one_sub_cos_eq_two_sin_sq,
    show ((k : ℝ) * x) / 2 = (k : ℝ) * (x / 2) by ring]
  nlinarith [sin_nat_mul_sq_le k (x / 2)]

section ProbabilityLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def symmetrizedLaw (μ : Measure E) : Measure E := μ ∗ μ.map (fun x => -x)

instance symmetrizedLaw_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetrizedLaw μ) := by
  unfold symmetrizedLaw
  haveI : IsProbabilityMeasure (μ.map (fun x => -x)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  infer_instance

theorem integrable_inner_cos (μ : Measure E) [IsFiniteMeasure μ] (t : E) :
    Integrable (fun x => Real.cos ⟪x, t⟫) μ := by
  apply integrable_of_abs_bound μ (by fun_prop) (C := 1)
  exact fun x => Real.abs_cos_le_one _

theorem integrable_inner_cos_defect (μ : Measure E) [IsFiniteMeasure μ] (t : E) :
    Integrable (fun x => 1 - Real.cos ⟪x, t⟫) μ :=
  (integrable_const 1).sub (integrable_inner_cos μ t)

omit [SecondCountableTopology E] in
theorem charFun_re_eq_integral_cos (μ : Measure E) [IsFiniteMeasure μ] (t : E) :
    (charFun μ t).re = ∫ x, Real.cos ⟪x, t⟫ ∂μ := by
  have h : Integrable (fun x => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ :=
    (BoundedContinuousFunction.innerProbChar t).integrable μ
  rw [charFun_apply]
  calc
    _ = ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)).re ∂μ :=
      (integral_re h).symm
    _ = _ := by simp only [Complex.exp_ofReal_mul_I_re]

theorem symmetrized_charFun_re (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    (charFun (symmetrizedLaw μ) t).re = ‖charFun μ t‖ ^ 2 := by
  have hmap : charFun (μ.map (fun x => -x)) t = starRingEnd ℂ (charFun μ t) := by
    have h := charFun_map_smul (μ := μ) (-1) t
    simpa only [neg_one_smul, charFun_neg] using h
  rw [symmetrizedLaw, charFun_conv, hmap, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The characteristic-function variance defect is the cosine defect
under the law of the difference of independent copies. -/
theorem charFun_sq_defect_integral (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    1 - ‖charFun μ t‖ ^ 2 =
      ∫ x, 1 - Real.cos ⟪x, t⟫ ∂symmetrizedLaw μ := by
  rw [integral_sub (integrable_const 1) (integrable_inner_cos (symmetrizedLaw μ) t)]
  rw [← charFun_re_eq_integral_cos, symmetrized_charFun_re]
  simp

/-- The source dilation estimate, without any assumed variance or
symmetrization identity. -/
theorem charFun_sq_defect_nat_smul (μ : Measure E) [IsProbabilityMeasure μ] (k : ℕ) (t : E) :
    1 - ‖charFun μ ((k : ℝ) • t)‖ ^ 2 ≤
      (k : ℝ) ^ 2 * (1 - ‖charFun μ t‖ ^ 2) := by
  rw [charFun_sq_defect_integral, charFun_sq_defect_integral]
  calc
    _ ≤ ∫ x, (k : ℝ) ^ 2 * (1 - Real.cos ⟪x, t⟫) ∂symmetrizedLaw μ := by
      apply integral_mono (integrable_inner_cos_defect (symmetrizedLaw μ) _)
        ((integrable_inner_cos_defect (symmetrizedLaw μ) t).const_mul _)
      intro x
      dsimp only
      rw [real_inner_smul_right]
      exact one_sub_cos_nat_mul_le k ⟪x, t⟫
    _ = _ := integral_const_mul _ _

theorem charFun_superlevel_dilate (μ : Measure E) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) {t : E}
    (ht : 1 - δ ^ 2 ≤ ‖charFun μ t‖ ^ 2) :
    3 / 4 ≤ ‖charFun μ ((⌊1 / (2 * δ)⌋₊ : ℝ) • t)‖ ^ 2 := by
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / (2 * δ))
  have hproduct : (⌊1 / (2 * δ)⌋₊ : ℝ) * δ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * δ)).mp hfloor
    linarith
  have hnonneg : 0 ≤ (⌊1 / (2 * δ)⌋₊ : ℝ) * δ := by positivity
  have hsq := pow_le_pow_left₀ hnonneg hproduct 2
  have hdefect := charFun_sq_defect_nat_smul μ ⌊1 / (2 * δ)⌋₊ t
  have hm := mul_le_mul_of_nonneg_left (show 1 - ‖charFun μ t‖ ^ 2 ≤ δ ^ 2 by linarith)
    (sq_nonneg (⌊1 / (2 * δ)⌋₊ : ℝ))
  nlinarith

end ProbabilityLaw
end CircularLaw
