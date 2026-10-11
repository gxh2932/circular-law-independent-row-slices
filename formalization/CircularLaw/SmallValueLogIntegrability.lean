import CircularLaw.LogTruncationIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite logarithmic integral from the limiting-law mass bounds

The source Gaussian singular-value law has compact support and mass at
most `C*t` below every positive `t`. These two properties imply the actual
finite Lebesgue logarithmic integral, including zero mass at zero.
This module proves that analytic implication; it does not assert the
existence or bounds of the Gaussian limiting law.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace CircularLaw

theorem zero_mass_of_linear_small_value_bound (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t) : ν {0} = 0 := by
  have hZero : ν.real {0} ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hSub : ({0} : Set ℝ≥0) ⊆ {x | (x : ℝ) < ε / C} := by
      intro x hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      simpa only [hx0, NNReal.coe_zero] using div_pos hε hC
    have h := (measureReal_mono hSub).trans (hMass (ε / C) (div_pos hε hC))
    simpa only [mul_div_cancel₀ ε hC.ne', zero_add] using h
  have hEq : ν.real {0} = 0 := le_antisymm hZero measureReal_nonneg
  exact (measureReal_eq_zero_iff (by finiteness)).mp hEq

theorem negative_log_closed_tail_of_linear_mass (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {C : ℝ} (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    {u : ℝ} (hu : 0 < u) :
    ν.real {x | u ≤ hermitizationNegativeLog x} ≤ C * Real.exp (-u / 2) := by
  apply (measureReal_mono (s₂ := {x : ℝ≥0 | (x : ℝ) < Real.exp (-u / 2)}) ?_).trans
    (hMass _ (Real.exp_pos _))
  intro x hx
  change u ≤ max (-Real.log (x : ℝ)) 0 at hx
  have hLog : Real.log (x : ℝ) ≤ -u := by
    rcases le_max_iff.mp hx with h | h
    · linarith
    · linarith
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, NNReal.coe_zero, Real.log_zero] at hLog
    linarith
  have hxPos : (0 : ℝ) < x := by
    exact_mod_cast (lt_of_le_of_ne (zero_le x) hx0.symm)
  have hExp := Real.exp_le_exp.mpr hLog
  rw [Real.exp_log hxPos] at hExp
  exact hExp.trans_lt (Real.exp_lt_exp.mpr (by linarith))

theorem negative_log_integrable_of_linear_mass (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t) :
    Integrable hermitizationNegativeLog ν ∧ (∫ x, hermitizationNegativeLog x ∂ν) ≤ 2 * C := by
  have hNonneg : 0 ≤ᵐ[ν] hermitizationNegativeLog :=
    ae_of_all ν (fun _ => le_max_right _ _)
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
  have hLin : (∫⁻ x, ENNReal.ofReal (hermitizationNegativeLog x) ∂ν) ≤
      ENNReal.ofReal (2 * C) := by
    rw [lintegral_eq_lintegral_meas_le ν hNonneg hermitizationNegativeLog_measurable.aemeasurable]
    rw [← hIntegral, ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ (fun _ => mul_nonneg hC.le (Real.exp_pos _).le))]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (negative_log_closed_tail_of_linear_mass ν hMass hu)
  have hLogInt : Integrable hermitizationNegativeLog ν :=
    (lintegral_ofReal_ne_top_iff_integrable hermitizationNegativeLog_measurable.aestronglyMeasurable
      hNonneg).mp (ne_of_lt (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hLogInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hNonneg hermitizationNegativeLog_measurable.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * C)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hLin

theorem positive_log_integrable_of_bounded_support (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0) : Integrable hermitizationPositiveLog ν := by
  have hBound : ∀ᵐ x : ℝ≥0 ∂ν, (x : ℝ) ≤ R := by
    rw [ae_iff]
    simpa only [not_le] using hSupport
  apply (integrable_const (Real.log (max R 1))).mono'
    continuous_hermitizationPositiveLog.measurable.aestronglyMeasurable
  filter_upwards [hBound] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hermitizationPositiveLog_nonneg x)]
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max hx le_rfl)

theorem finite_logarithmic_integral_of_mass_and_support (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (R : ℝ) (hSupport : ν {x : ℝ≥0 | R < (x : ℝ)} = 0) : FiniteLogarithmicIntegral ν := by
  refine ⟨zero_mass_of_linear_small_value_bound ν hC hMass, ?_⟩
  have hPos := positive_log_integrable_of_bounded_support ν R hSupport
  have hNeg := (negative_log_integrable_of_linear_mass ν hC hMass).1
  have hDiff : Integrable (fun x => hermitizationPositiveLog x - hermitizationNegativeLog x) ν :=
    hPos.sub hNeg
  simpa only [← hermitization_log_decomposition] using hDiff

end CircularLaw
