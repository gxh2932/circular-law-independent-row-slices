import CircularLaw.SmallValueLogIntegrability

/-!
# A uniform logarithmic clipping error from linear small-value mass

Layercake integrates the closed exponential tail bound. Applied to the
negative logarithmic clipping excess, it gives 2 C exp(-T/2) uniformly
over every finite limiting law with small-value mass bounded by C t.
This permits the law and the truncation level to vary together.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace CircularLaw

theorem nonnegative_integral_bound_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ) (hf : Measurable f)
    (hNonneg : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 < C)
    (hTail : ∀ u : ℝ, 0 < u → ν.real {x | u ≤ f x} ≤ C * Real.exp (-u / 2)) :
    Integrable f ν ∧ (∫ x, f x ∂ν) ≤ 2 * C := by
  have hAe : 0 ≤ᵐ[ν] f := ae_of_all ν hNonneg
  have hInt : Integrable (fun u : ℝ => C * Real.exp (-u / 2))
      (volume.restrict (Set.Ioi 0)) := by
    convert (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul C using 1
    ext u
    congr 2
    ring
  have hIntegral : (∫ u : ℝ in Set.Ioi 0, C * Real.exp (-u / 2)) = 2 * C := by
    rw [integral_const_mul]
    have hExp : (∫ u : ℝ in Set.Ioi 0, Real.exp (-u / 2)) = 2 := by
      convert integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0 using 1
      · congr 1
        ext u
        congr 1
        ring
      · norm_num
    rw [hExp]
    ring
  have hLin : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≤ ENNReal.ofReal (2 * C) := by
    rw [lintegral_eq_lintegral_meas_le ν hAe hf.aemeasurable]
    rw [← hIntegral, ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ (fun _ => mul_nonneg hC.le (Real.exp_pos _).le))]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hTail u hu)
  have hFInt : Integrable f ν :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hAe).mp
      (ne_of_lt (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hFInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hAe hf.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * C)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hLin

theorem negative_log_clipping_excess_integral_bound_of_linear_mass
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] {C T : ℝ} (hC : 0 < C) (hT : 0 ≤ T)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t) :
    Integrable (fun t => hermitizationNegativeLog t - clippedNegativeLog T t) ν ∧
      (∫ t, hermitizationNegativeLog t - clippedNegativeLog T t ∂ν) ≤
        2 * C * Real.exp (-T / 2) := by
  let f := fun t => max (hermitizationNegativeLog t - T) 0
  have hf : Measurable f :=
    (hermitizationNegativeLog_measurable.sub measurable_const).max measurable_const
  have hNonneg (t : ℝ≥0) : 0 ≤ f t := le_max_right _ _
  have hTail (u : ℝ) (hu : 0 < u) :
      ν.real {t | u ≤ f t} ≤
        (C * Real.exp (-T / 2)) * Real.exp (-u / 2) := by
    have hSubset : {t : ℝ≥0 | u ≤ f t} ⊆
        {t | T + u ≤ hermitizationNegativeLog t} := by
      intro t ht
      change u ≤ max (hermitizationNegativeLog t - T) 0 at ht
      rcases le_max_iff.mp ht with ht | ht
      · change T + u ≤ hermitizationNegativeLog t
        linarith
      · exact False.elim (not_le_of_gt hu ht)
    calc
      _ ≤ ν.real {t | T + u ≤ hermitizationNegativeLog t} := measureReal_mono hSubset
      _ ≤ C * Real.exp (-(T + u) / 2) :=
        negative_log_closed_tail_of_linear_mass ν hMass (by linarith)
      _ = _ := by
        rw [show -(T + u) / 2 = -T / 2 + -u / 2 by ring, Real.exp_add]
        ring
  have h := nonnegative_integral_bound_of_exponential_tail ν _ hf hNonneg
    (mul_pos hC (Real.exp_pos _)) hTail
  have hNe : ∀ᵐ t : ℝ≥0 ∂ν, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using
      zero_mass_of_linear_small_value_bound ν hC hMass
  have hEq : (fun t => hermitizationNegativeLog t - clippedNegativeLog T t) =ᵐ[ν] f := by
    filter_upwards [hNe] with t ht
    rw [clippedNegativeLog_eq_min hT (lt_of_le_of_ne (zero_le _) ht.symm)]
    by_cases hLe : hermitizationNegativeLog t ≤ T
    · simp only [min_eq_left hLe, sub_self, f, max_eq_right (sub_nonpos.mpr hLe)]
    · simp only [min_eq_right (le_of_not_ge hLe), f,
        max_eq_left (sub_nonneg.mpr (le_of_not_ge hLe))]
  refine ⟨h.1.congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq]
  simpa only [mul_assoc] using h.2

theorem negative_log_clipping_integral_error_of_linear_mass
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] {C T : ℝ} (hC : 0 < C) (hT : 0 ≤ T)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t) :
    |(∫ t, clippedNegativeLog T t ∂ν) - ∫ t, hermitizationNegativeLog t ∂ν| ≤
      2 * C * Real.exp (-T / 2) := by
  have hNeg := (negative_log_integrable_of_linear_mass ν hC hMass).1
  have hClip : Integrable (clippedNegativeLog T) ν :=
    (integrable_const T).mono' (continuous_clippedNegativeLog T).measurable.aestronglyMeasurable
      (ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clippedNegativeLog_bounds hT t).1]
        exact (clippedNegativeLog_bounds hT t).2))
  have hBound := (negative_log_clipping_excess_integral_bound_of_linear_mass ν hC hT hMass).2
  rw [integral_sub hNeg hClip] at hBound
  have hNe : ∀ᵐ t : ℝ≥0 ∂ν, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using
      zero_mass_of_linear_small_value_bound ν hC hMass
  have hNonneg : 0 ≤ (∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, clippedNegativeLog T t ∂ν := by
    apply sub_nonneg.mpr (integral_mono_ae hClip hNeg ?_)
    filter_upwards [hNe] with t ht
    rw [clippedNegativeLog_eq_min hT (lt_of_le_of_ne (zero_le _) ht.symm)]
    exact min_le_left _ _
  rw [abs_sub_comm, abs_of_nonneg hNonneg]
  exact hBound

theorem clipped_positive_log_integral_eq_of_support (ν : Measure ℝ≥0)
    (R : ℝ) (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0) {T : ℝ}
    (hT : Real.log (max R 1) ≤ T) :
    (∫ t, clippedPositiveLog T t ∂ν) = ∫ t, hermitizationPositiveLog t ∂ν := by
  have hAe : ∀ᵐ t : ℝ≥0 ∂ν, (t : ℝ) ≤ R := by
    rw [ae_iff]
    simpa only [not_le] using hSupport
  apply integral_congr_ae
  filter_upwards [hAe] with t ht
  have hLog : hermitizationPositiveLog t ≤ Real.log (max R 1) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max ht le_rfl)
  exact min_eq_left (hLog.trans hT)

end CircularLaw
