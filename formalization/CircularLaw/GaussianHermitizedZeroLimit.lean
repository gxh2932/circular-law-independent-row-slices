import CircularLaw.GaussianHermitizedResolvent

/-!
# The actual Gaussian Hermitized resolvent at zero regularization

The checked Dyson equation determines the limit. Outside the unit disk,
the cube of the positive resolvent is bounded by the regularization.
Inside the disk, its square is squeezed between two explicit expressions
converging to `1-r^2`.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_hermitized_resolvent_cube_bound {r : ℝ} (hr : 1 ≤ r)
    {t : ℝ} (ht : 0 < t) : gaussianHermitizedResolvent r t ^ 3 ≤ t := by
  let g := gaussianHermitizedResolvent r t
  have hg : 0 < g := gaussian_hermitized_resolvent_pos r ht
  have hEq := gaussian_hermitized_resolvent_equation r ht
  change g * ((t + g) ^ 2 + r ^ 2) = t + g at hEq
  have hr2 : 0 ≤ r ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg hg.le hr2, mul_nonneg ht.le (sq_nonneg g),
    mul_nonneg hg.le (sq_nonneg t)]

theorem gaussian_hermitized_resolvent_tendsto_zero_outside {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (gaussianHermitizedResolvent r) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_lt_nhds (pow_pos hε 3)).filter_mono nhdsWithin_le_nhds] with t ht htε
  have hg := gaussian_hermitized_resolvent_pos r ht
  have hlt : gaussianHermitizedResolvent r t < ε :=
    lt_of_pow_lt_pow_left₀ 3 hε.le
      ((gaussian_hermitized_resolvent_cube_bound hr ht).trans_lt htε)
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hg] using hlt

theorem gaussian_hermitized_resolvent_lower_inside {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1 - r ^ 2) - t ≤ gaussianHermitizedResolvent r t := by
  have hRad : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hSq := Real.sq_sqrt hRad
  have hD := gaussian_hermitized_resolvent_denominator_gt_one r ht
  have hU : 0 < t + gaussianHermitizedResolvent r t :=
    add_pos ht (gaussian_hermitized_resolvent_pos r ht)
  have hlt : Real.sqrt (1 - r ^ 2) < t + gaussianHermitizedResolvent r t :=
    lt_of_pow_lt_pow_left₀ 2 hU.le (by linarith)
  linarith

theorem gaussian_hermitized_resolvent_square_bounds_inside {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) {t : ℝ} (ht : 0 < t)
    (htSmall : t < Real.sqrt (1 - r ^ 2) / 2) :
    (Real.sqrt (1 - r ^ 2) - t) ^ 2 ≤ gaussianHermitizedResolvent r t ^ 2 ∧
      gaussianHermitizedResolvent r t ^ 2 ≤
        (1 - r ^ 2) + 2 * t / Real.sqrt (1 - r ^ 2) := by
  let a := Real.sqrt (1 - r ^ 2)
  let g := gaussianHermitizedResolvent r t
  have hRad : 0 < 1 - r ^ 2 := by nlinarith
  have ha : 0 < a := Real.sqrt_pos.mpr hRad
  have haSq : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hRad.le
  have hg : 0 < g := gaussian_hermitized_resolvent_pos r ht
  have hLower : a - t ≤ g := gaussian_hermitized_resolvent_lower_inside hr0 hr1 ht
  have hgl : a / 2 ≤ g := by change t < a / 2 at htSmall; linarith
  constructor
  · exact pow_le_pow_left₀ (by change t < a / 2 at htSmall; linarith) hLower 2
  · have hD := gaussian_hermitized_resolvent_denominator_gt_one r ht
    have hEq := gaussian_hermitized_resolvent_equation r ht
    change 1 < (t + g) ^ 2 + r ^ 2 at hD
    change g * ((t + g) ^ 2 + r ^ 2) = t + g at hEq
    have hMult : (a / 2) * ((t + g) ^ 2 + r ^ 2 - 1) ≤ t := by
      calc
        _ ≤ g * ((t + g) ^ 2 + r ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right hgl (by linarith)
        _ = t := by nlinarith [hEq]
    have hSmallD : g ^ 2 + r ^ 2 - 1 ≤ (t + g) ^ 2 + r ^ 2 - 1 := by
      nlinarith [mul_nonneg ht.le hg.le]
    have hGM : (a / 2) * (g ^ 2 - a ^ 2) ≤ t := by
      calc
        _ = (a / 2) * (g ^ 2 + r ^ 2 - 1) := by rw [haSq]; ring
        _ ≤ (a / 2) * ((t + g) ^ 2 + r ^ 2 - 1) :=
          mul_le_mul_of_nonneg_left hSmallD (by positivity)
        _ ≤ t := hMult
    change g ^ 2 ≤ (1 - r ^ 2) + 2 * t / a
    rw [← haSq]
    apply (mul_le_mul_iff_right₀ ha).mp
    have hRewrite : (a ^ 2 + 2 * t / a) * a = a ^ 2 * a + 2 * t := by
      field_simp [ne_of_gt ha]
    rw [mul_comm a (a ^ 2 + 2 * t / a), hRewrite]
    nlinarith [hGM]

theorem gaussian_hermitized_resolvent_tendsto_zero_inside {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (gaussianHermitizedResolvent r) (𝓝[>] 0) (𝓝 (Real.sqrt (1 - r ^ 2))) := by
  let a := Real.sqrt (1 - r ^ 2)
  have hRad : 0 < 1 - r ^ 2 := by nlinarith
  have ha : 0 < a := Real.sqrt_pos.mpr hRad
  have haSq : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hRad.le
  have hId : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hLower : Tendsto (fun t : ℝ => (a - t) ^ 2) (𝓝[>] 0) (𝓝 (1 - r ^ 2)) := by
    simpa only [sub_zero, haSq] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a) (𝓝[>] 0) (𝓝 a)).sub hId).pow 2
  have hUpper : Tendsto (fun t : ℝ => (1 - r ^ 2) + 2 * t / a)
      (𝓝[>] 0) (𝓝 (1 - r ^ 2)) := by
    simpa using tendsto_const_nhds.add ((tendsto_const_nhds.mul hId).div_const a)
  have hBounds : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (a - t) ^ 2 ≤ gaussianHermitizedResolvent r t ^ 2 ∧
        gaussianHermitizedResolvent r t ^ 2 ≤ (1 - r ^ 2) + 2 * t / a := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (half_pos ha)).filter_mono nhdsWithin_le_nhds] with t ht htSmall
    exact gaussian_hermitized_resolvent_square_bounds_inside hr0 hr1 ht htSmall
  have hSquare : Tendsto (fun t : ℝ => gaussianHermitizedResolvent r t ^ 2)
      (𝓝[>] 0) (𝓝 (1 - r ^ 2)) :=
    hLower.squeeze' hUpper (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))
  have hSqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hSquare
  apply hSqrt.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact Real.sqrt_sq (gaussian_hermitized_resolvent_pos r ht).le

end CircularLaw
