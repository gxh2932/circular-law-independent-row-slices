import CircularLaw.RareBernoulliSmallBall
import CircularLaw.Tensorization

/-!
# Exponential tensorization of a rare-selection exclusion probability

A scalar exclusion probability q/2 at radius t/3 gives a Laplace
factor exp(-q/4). Independence then yields exp(-q*K/8) at squared
norm threshold t^2*q*K/72. The threshold tracks the rare density.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_rare_small_ball_laplace {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℂ) {t q : ℝ}
    (ht : 0 < t) (z : ℂ)
    (hSmall : μ.real {ω | ‖X ω - z‖ ≤ t / 3} ≤ 1 - q / 2) :
    (∫ ω, Real.exp (-(9 * ‖X ω - z‖ ^ 2 / t ^ 2)) ∂μ) ≤ Real.exp (-q / 4) := by
  let E : Set Ω := {ω | ‖X ω - z‖ ≤ t / 3}
  have hHalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hPoint (ω : Ω) : Real.exp (-(9 * ‖X ω - z‖ ^ 2 / t ^ 2)) ≤
      1 / 2 + E.indicator (fun _ => (1 / 2 : ℝ)) ω := by
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have h := Real.exp_le_exp.mpr
        (show -(9 * ‖X ω - z‖ ^ 2 / t ^ 2) ≤ 0 from neg_nonpos.mpr (by positivity))
      rw [Real.exp_zero] at h
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hNorm : t / 3 < ‖X ω - z‖ := lt_of_not_ge hω
      have hSquare : t ^ 2 ≤ 9 * ‖X ω - z‖ ^ 2 := by
        nlinarith [norm_nonneg (X ω - z)]
      have hRatio : 1 ≤ 9 * ‖X ω - z‖ ^ 2 / t ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by simpa only [one_mul] using hSquare)
      exact (Real.exp_le_exp.mpr (by linarith : -(9 * ‖X ω - z‖ ^ 2 / t ^ 2) ≤ -1)).trans hHalf
  calc
    _ ≤ ∫ ω, (1 / 2 + E.indicator (fun _ => (1 / 2 : ℝ)) ω) ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite hPoint
    _ = 1 / 2 + μ.real E * (1 / 2) := by
      rw [integral_add (integrable_const _) Integrable.of_finite,
        integral_const, integral_indicator_const _ (Set.toFinite _).measurableSet, probReal_univ]
      simp only [smul_eq_mul, one_mul]
    _ ≤ 1 - q / 4 := by change μ.real E ≤ _ at hSmall; linarith
    _ ≤ _ := by linarith [Real.add_one_le_exp (-q / 4)]

theorem finite_rare_small_ball_tensorization {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Fin K → Ω → ℂ) (hInd : iIndepFun X μ) {t q : ℝ} (ht : 0 < t)
    (z : Fin K → ℂ)
    (hSmall : ∀ i, μ.real {ω | ‖X i ω - z i‖ ≤ t / 3} ≤ 1 - q / 2) :
    μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ t ^ 2 * q * K / 72} ≤
      Real.exp (-q * (K : ℝ) / 8) := by
  let F : Ω → ℝ := fun ω => Real.exp (-(9 * (∑ i, ‖X i ω - z i‖ ^ 2) / t ^ 2))
  have hProduct : (∫ ω, F ω ∂μ) =
      ∏ i, ∫ ω, Real.exp (-(9 * ‖X i ω - z i‖ ^ 2 / t ^ 2)) ∂μ := by
    dsimp only [F]
    simp_rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact hInd.integral_fun_prod_comp
      (f := fun i w => Real.exp (-(9 * ‖w - z i‖ ^ 2 / t ^ 2)))
      (fun _ => (measurable_of_countable _).aemeasurable) (fun _ => by fun_prop)
  have hIntegral : (∫ ω, F ω ∂μ) ≤ Real.exp (-q * (K : ℝ) / 4) := by
    rw [hProduct]
    have hBound := Finset.prod_le_prod
      (s := Finset.univ) (fun _ _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
      (fun i _ => finite_rare_small_ball_laplace μ (X i) ht (z i) (hSmall i))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hBound
    rw [← Real.exp_nat_mul] at hBound
    convert hBound using 1
    congr 1
    ring
  have hSub : {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ t ^ 2 * q * K / 72} ⊆
      {ω | Real.exp (-q * (K : ℝ) / 8) ≤ F ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    dsimp only [F]
    have hScaled := mul_le_mul_of_nonneg_left hω (by norm_num : (0 : ℝ) ≤ 9)
    have hRatio : 9 * (∑ i, ‖X i ω - z i‖ ^ 2) / t ^ 2 ≤ q * K / 8 := by
      apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
      nlinarith
    linarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => (Real.exp_pos _).le) (show Integrable F μ from Integrable.of_finite)
    (Real.exp (-q * (K : ℝ) / 8))
  have hBound : Real.exp (-q * (K : ℝ) / 8) *
      μ.real {ω | (∑ i, ‖X i ω - z i‖ ^ 2) ≤ t ^ 2 * q * K / 72} ≤
        Real.exp (-q * (K : ℝ) / 4) :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hSub) (Real.exp_nonneg _)).trans
      (hMarkov.trans hIntegral)
  calc
    _ ≤ Real.exp (-q * (K : ℝ) / 4) / Real.exp (-q * (K : ℝ) / 8) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hBound
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      ring

end CircularLaw
