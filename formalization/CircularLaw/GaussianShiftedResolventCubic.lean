import CircularLaw.SquaredResolventMomentSeries
import CircularLaw.PowerSeriesSums
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The actual shifted Gaussian squared resolvent satisfies the cubic

The checked limiting moment series evaluates to the actual resolvent
near zero. Absolute summability validates its formal cubic there. The
resolvent is analytic on the left half-plane, so the analytic identity
principle extends this cubic to every parameter in that half-plane.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

def gaussianShiftedResolventCubic (r : ℝ) (q : ℂ) : ℂ :=
  let v := squaredResolvent (gaussianShiftedSingularLimit (r : ℂ)) q
  q ^ 2 * v ^ 3 - 2 * q * v ^ 2 + (1 + q * (1 - (r : ℂ) ^ 2)) * v - 1

theorem gaussian_shifted_resolvent_cubic_near_zero (r : ℝ) (q : ℂ)
    (hSmall : ‖q‖ * (128 + ‖(r : ℂ)‖) ^ 2 < 1) :
    gaussianShiftedResolventCubic r q = 0 := by
  let m := gaussianShiftedEvenMomentSeries r
  let v := squaredResolvent (gaussianShiftedSingularLimit (r : ℂ)) q
  have hM : PowerSeriesSumsAt m q v := gaussian_shifted_squared_resolvent_hasSum r q hSmall
  have hX := power_series_sums_X q
  have hC := power_series_sums_C q (r : ℂ)
  have h1 := power_series_sums_one q
  have h2 := power_series_sums_two q
  have hPoly : PowerSeriesSumsAt
      (PowerSeries.X ^ 2 * m ^ 3 - 2 * PowerSeries.X * m ^ 2 +
        (1 + PowerSeries.X * (1 - PowerSeries.C (r : ℂ) ^ 2)) * m - 1) q
      (q ^ 2 * v ^ 3 - 2 * q * v ^ 2 + (1 + q * (1 - (r : ℂ) ^ 2)) * v - 1) :=
    power_series_sums_sub
      (power_series_sums_add
        (power_series_sums_sub
          (power_series_sums_mul (power_series_sums_pow hX 2) (power_series_sums_pow hM 3))
          (power_series_sums_mul (power_series_sums_mul h2 hX) (power_series_sums_pow hM 2)))
        (power_series_sums_mul
          (power_series_sums_add h1
            (power_series_sums_mul hX (power_series_sums_sub h1 (power_series_sums_pow hC 2)))) hM)) h1
  exact power_series_sums_zero_unique hPoly (gaussian_shifted_even_moment_series_cubic r)

theorem gaussian_shifted_resolvent_cubic_analytic (r : ℝ) :
    AnalyticOnNhd ℂ (gaussianShiftedResolventCubic r) {q : ℂ | q.re < 0} := by
  have hV := gaussian_shifted_squared_resolvent_analytic (r : ℂ)
  have hId : AnalyticOnNhd ℂ (fun q : ℂ => q) {q : ℂ | q.re < 0} := analyticOnNhd_id
  have h1 : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) {q : ℂ | q.re < 0} := analyticOnNhd_const
  have h2 : AnalyticOnNhd ℂ (fun _ : ℂ => (2 : ℂ)) {q : ℂ | q.re < 0} := analyticOnNhd_const
  have hC : AnalyticOnNhd ℂ (fun _ : ℂ => 1 - (r : ℂ) ^ 2)
      {q : ℂ | q.re < 0} := analyticOnNhd_const
  exact (((hId.pow 2).mul (hV.pow 3)).sub ((h2.mul hId).mul (hV.pow 2))).add
    ((h1.add (hId.mul hC)).mul hV) |>.sub h1

theorem gaussian_shifted_resolvent_cubic (r : ℝ) {q : ℂ} (hq : q.re < 0) :
    gaussianShiftedResolventCubic r q = 0 := by
  let R : ℝ := 128 + ‖(r : ℂ)‖
  have hR : 0 < R := by dsimp [R]; positivity
  let c : ℝ := (2 * R ^ 2)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hcR : c * R ^ 2 = 1 / 2 := by
    dsimp [c]
    field_simp
  let q₀ : ℂ := -(c : ℂ)
  have hq₀ : q₀.re < 0 := by change -c < 0; linarith
  have hSmall : ‖q₀‖ * R ^ 2 < 1 := by
    simp only [q₀, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [hcR]
    norm_num
  have hNear : ∀ᶠ p : ℂ in 𝓝 q₀, ‖p‖ * R ^ 2 < 1 :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds hSmall
  have hEq : gaussianShiftedResolventCubic r =ᶠ[𝓝 q₀] (fun _ => 0) :=
    hNear.mono (fun p hp => gaussian_shifted_resolvent_cubic_near_zero r p hp)
  have hConnected : IsPreconnected {p : ℂ | p.re < 0} :=
    (convex_halfSpace_lt Complex.reLm.isLinear 0).isPreconnected
  exact (gaussian_shifted_resolvent_cubic_analytic r).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hConnected hq₀ hEq hq

end CircularLaw
