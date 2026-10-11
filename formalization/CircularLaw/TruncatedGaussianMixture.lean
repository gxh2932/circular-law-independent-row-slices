import CircularLaw.WeightedJensen

/-!
# Averaging the normalized Gaussian cosine bound

Weighted Jensen and Fubini turn the checked single-vector estimate into a
bound for the cosine defect of an arbitrary finite measure. The weights are
its actual truncated second moments, and all product integrability is proved.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace CircularLaw

def cosineAverage (ν : Measure ℂ) (t : ℂ) : ℝ :=
  ∫ v, 1 - Real.cos ⟪v, t⟫ ∂ν

theorem cosineAverage_nonneg (ν : Measure ℂ) (t : ℂ) : 0 ≤ cosineAverage ν t :=
  integral_nonneg (fun _ => sub_nonneg.mpr (Real.cos_le_one _))

theorem measurable_cosineAverage (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Measurable (cosineAverage ν) := by
  have hEq : cosineAverage ν = fun t => ν.real Set.univ - (charFun ν t).re := by
    funext t
    rw [cosineAverage, integral_sub (integrable_const 1) (integrable_inner_cos ν t),
      ← charFun_re_eq_integral_cos]
    simp only [integral_const, smul_eq_mul, mul_one]
  rw [hEq]
  fun_prop

theorem gaussian_cosineAverage_integrable (ν : Measure ℂ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun t => Real.exp (-b * ‖t‖ ^ 2 - cosineAverage ν t / 2)) volume := by
  apply (planarGaussian_integrable hb).mono'
  · exact ((by fun_prop : Measurable (fun t : ℂ => -b * ‖t‖ ^ 2)).sub
      ((measurable_cosineAverage ν).div_const 2)).exp.aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h := cosineAverage_nonneg ν t
    linarith

theorem planarCosineKernel_le_gaussian {b a : ℝ} (ha : 0 ≤ a) (v t : ℂ) :
    planarCosineKernel b a v t ≤ planarGaussian b t := by
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
    (sub_nonneg.mpr (Real.cos_le_one _)))

theorem truncatedNormSq_zero_imp {r₀ : ℝ} (hr₀ : 0 < r₀) {v : ℂ}
    (h : truncatedNormSq r₀ v = 0) : v = 0 := by
  by_contra hv
  have hPos : 0 < truncatedNormSq r₀ v := by
    unfold truncatedNormSq
    exact sq_pos_of_pos (lt_min (norm_pos_iff.mpr hv) hr₀)
  linarith

theorem truncated_gaussian_mixture_integral_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hA : 0 < ∫ v, truncatedNormSq r₀ v ∂ν) :
    (∫ t : ℂ, Real.exp (-(r ^ 2 / 4) * ‖t‖ ^ 2 - cosineAverage ν t / 2)) ≤
      96 / (r * Real.sqrt (∫ v, truncatedNormSq r₀ v ∂ν)) := by
  let w := truncatedNormSq r₀
  let A := ∫ v, w v ∂ν
  let b := r ^ 2 / 4
  let K : ℂ → ℂ → ℝ := fun v t => (w v / A) * planarCosineKernel b (A / (2 * w v)) v t
  have hAPos : 0 < A := hA
  have hrPos : 0 < r := hr₀.trans_le hr
  have hb : 0 < b := by dsimp [b]; positivity
  have hw : Measurable w := by unfold w truncatedNormSq; fun_prop
  have hwInt : Integrable w ν := truncatedNormSq_integrable ν hr₀.le
  have hwNonneg (v : ℂ) : 0 ≤ w v := truncatedNormSq_nonneg r₀ v
  have hK : Integrable (fun p : ℂ × ℂ => K p.1 p.2) (ν.prod volume) := by
    apply ((hwInt.div_const A).mul_prod (planarGaussian_integrable hb)).mono'
    · dsimp [K, w, planarCosineKernel, truncatedNormSq]
      fun_prop
    · apply ae_of_all
      intro p
      have hW := div_nonneg (hwNonneg p.1) hAPos.le
      have hCoeff : 0 ≤ A / (2 * w p.1) := div_nonneg hAPos.le
        (mul_nonneg (by norm_num) (hwNonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW
        (by unfold planarCosineKernel; positivity))]
      exact mul_le_mul_of_nonneg_left
        (planarCosineKernel_le_gaussian hCoeff p.1 p.2) hW
  have hPoint (t : ℂ) : Real.exp (-b * ‖t‖ ^ 2 - cosineAverage ν t / 2) ≤ ∫ v, K v t ∂ν := by
    have hJ := weighted_exponential_jensen ν hw hwInt hwNonneg
      (by fun_prop : Measurable (fun v : ℂ => 1 - Real.cos ⟪v, t⟫))
      (integrable_inner_cos_defect ν t) (fun _ => sub_nonneg.mpr (Real.cos_le_one _))
      (fun v hv => by rw [truncatedNormSq_zero_imp hr₀ hv]; simp) hA
    have h := mul_le_mul_of_nonneg_left hJ (Real.exp_pos (-b * ‖t‖ ^ 2)).le
    rw [← integral_const_mul] at h
    rw [sub_eq_add_neg, Real.exp_add]
    convert h using 1
    · simp only [cosineAverage, neg_div]
    · congr 1
      funext v
      change (w v / A) * (Real.exp (-b * ‖t‖ ^ 2) *
        Real.exp (-(A / (2 * w v)) * (1 - Real.cos ⟪v, t⟫))) =
        Real.exp (-b * ‖t‖ ^ 2) * ((w v / A) *
          Real.exp (-A * (1 - Real.cos ⟪v, t⟫) / (2 * w v)))
      rw [show -(A / (2 * w v)) * (1 - Real.cos ⟪v, t⟫) =
        -A * (1 - Real.cos ⟪v, t⟫) / (2 * w v) by ring]
      ring
  have h := integral_mono (gaussian_cosineAverage_integrable ν hb) hK.integral_prod_right hPoint
  rw [← integral_integral_swap hK] at h
  have hBound : (∫ v, (∫ t, K v t) ∂ν) ≤ 96 / (r * Real.sqrt A) := by
    have hInt := integral_mono hK.integral_prod_left
      ((hwInt.div_const A).mul_const (96 / (r * Real.sqrt A))) (fun v => by
        dsimp only [K]
        rw [integral_const_mul]
        by_cases hv : v = 0
        · simp [hv, w, truncatedNormSq, min_eq_left hr₀.le]
        · exact mul_le_mul_of_nonneg_left (truncated_planar_cosine_integral_le v hv hr₀ hr hA)
            (div_nonneg (hwNonneg _) hA.le))
    rw [integral_mul_const, integral_div, div_self hA.ne', one_mul] at hInt
    exact hInt
  exact h.trans hBound

end CircularLaw
