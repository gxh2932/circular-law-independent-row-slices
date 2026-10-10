import CircularLaw.GaussianRegularizedLogBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exact regularized logarithmic value for the actual Gaussian limit

The actual integral and its explicit Dyson expression have the same
derivative on the positive half-line. Both differences from log(t)
tend to zero at infinity, fixing the integration constant and proving
the value at every positive regularization. Removing regularization is
a separate limiting argument.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_regularized_log_formula_difference (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianRegularizedLogFormula r t - Real.log t =
      (1 / 2 : ℝ) * Real.log ((1 + gaussianHermitizedResolvent r t / t) ^ 2 + (r / t) ^ 2) -
        (1 / 2 : ℝ) * gaussianHermitizedResolvent r t ^ 2 := by
  have hFirst : 0 < 1 + gaussianHermitizedResolvent r t / t := by
    have hRatio := div_pos (gaussian_hermitized_resolvent_pos r ht) ht
    linarith
  have hPos : 0 < (1 + gaussianHermitizedResolvent r t / t) ^ 2 + (r / t) ^ 2 := by positivity
  have hFactor : (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2 =
      t ^ 2 * ((1 + gaussianHermitizedResolvent r t / t) ^ 2 + (r / t) ^ 2) := by
    field_simp [ne_of_gt ht]
  rw [gaussianRegularizedLogFormula, hFactor,
    Real.log_mul (ne_of_gt (sq_pos_of_pos ht)) (ne_of_gt hPos), Real.log_pow]
  ring

theorem gaussian_regularized_log_formula_normalization_atTop (r : ℝ) :
    Tendsto (fun t : ℝ => gaussianRegularizedLogFormula r t - Real.log t) atTop (𝓝 0) := by
  have hG := gaussian_hermitized_resolvent_tendsto_atTop r
  have hInv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hRatio : Tendsto (fun t : ℝ => gaussianHermitizedResolvent r t / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hG.mul hInv
  have hRadial : Tendsto (fun t : ℝ => r / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hInv
  have hA : Tendsto (fun t : ℝ => (1 + gaussianHermitizedResolvent r t / t) ^ 2 + (r / t) ^ 2)
      atTop (𝓝 1) := by
    simpa only [add_zero, one_pow, zero_pow (by decide : 2 ≠ 0)] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hRatio).pow 2).add
        (hRadial.pow 2)
  have hLog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hA
  have hExpr : Tendsto (fun t : ℝ =>
      (1 / 2 : ℝ) * Real.log ((1 + gaussianHermitizedResolvent r t / t) ^ 2 + (r / t) ^ 2) -
        (1 / 2 : ℝ) * gaussianHermitizedResolvent r t ^ 2) atTop (𝓝 0) := by
    simpa only [Real.log_one, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self] using
      (tendsto_const_nhds.mul hLog).sub (tendsto_const_nhds.mul (hG.pow 2))
  exact hExpr.congr' ((eventually_gt_atTop 0).mono
    (fun t ht => (gaussian_regularized_log_formula_difference r ht).symm))

theorem gaussian_regularized_log_value (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianRegularizedLog r t = gaussianRegularizedLogFormula r t := by
  let H : ℝ → ℝ := fun u => gaussianRegularizedLog r u - gaussianRegularizedLogFormula r u
  have hDeriv (u : ℝ) (hu : 0 < u) : HasDerivAt H 0 u := by
    simpa only [sub_self] using (gaussian_regularized_log_hasDerivAt r hu).sub
      (gaussian_regularized_log_formula_hasDerivAt r hu)
  have hDiff : DifferentiableOn ℝ H (Ioi 0) :=
    fun u hu => (hDeriv u hu).differentiableAt.differentiableWithinAt
  have hSame (u : ℝ) (hu : 0 < u) : H u = H 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected hDiff
      (fun v hv => (hDeriv v hv).deriv) hu (by norm_num)
  have hZeroLimit : Tendsto H atTop (𝓝 0) := by
    have h := (gaussian_regularized_log_normalization_atTop r).sub
      (gaussian_regularized_log_formula_normalization_atTop r)
    simpa only [sub_zero] using h.congr' (Eventually.of_forall (fun u => by dsimp [H]; ring))
  have hConstLimit : Tendsto H atTop (𝓝 (H 1)) :=
    tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono (fun u hu => (hSame u hu).symm))
  have hZero : H 1 = 0 := tendsto_nhds_unique hConstLimit hZeroLimit
  apply sub_eq_zero.mp
  change H t = 0
  rw [hSame t ht, hZero]

end CircularLaw
