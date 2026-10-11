import CircularLaw.EsseenConcentration

/-!
# Concentration in planar cubes

The square of half-side `r` contains the Euclidean ball of radius `r` and
lies in the Euclidean ball of radius `sqrt(2)*r`. Its concentration function
is the supremum of actual translated-square probabilities.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

def planarCube (z : ℂ) (r : ℝ) : Set ℂ :=
  {x | |(x - z).re| ≤ r ∧ |(x - z).im| ≤ r}

theorem measurableSet_planarCube (z : ℂ) (r : ℝ) : MeasurableSet (planarCube z r) := by
  unfold planarCube
  exact (measurableSet_le (by fun_prop : Measurable (fun x : ℂ => |(x - z).re|))
    measurable_const).inter
    (measurableSet_le (by fun_prop : Measurable (fun x : ℂ => |(x - z).im|)) measurable_const)

theorem planarCube_mono (z : ℂ) {r R : ℝ} (hr : r ≤ R) :
    planarCube z r ⊆ planarCube z R := fun _ hx => ⟨hx.1.trans hr, hx.2.trans hr⟩

theorem closedBall_subset_planarCube (z : ℂ) (r : ℝ) :
    Metric.closedBall z r ⊆ planarCube z r := by
  intro x hx
  have h : ‖x - z‖ ≤ r := hx
  exact ⟨(Complex.abs_re_le_norm _).trans h, (Complex.abs_im_le_norm _).trans h⟩

theorem planarCube_subset_closedBall (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    planarCube z r ⊆ Metric.closedBall z (Real.sqrt 2 * r) := by
  intro x hx
  change ‖x - z‖ ≤ Real.sqrt 2 * r
  have hRe := pow_le_pow_left₀ (abs_nonneg _) hx.1 2
  have hIm := pow_le_pow_left₀ (abs_nonneg _) hx.2 2
  simp only [sq_abs] at hRe hIm
  have hNorm : ‖x - z‖ ^ 2 = (x - z).re ^ 2 + (x - z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hRight : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), norm_nonneg (x - z)]

theorem planarCube_sub_triangle {x y z : ℂ} {r R : ℝ}
    (hxy : x + y ∈ planarCube z r) (hy : y ∈ planarCube (0 : ℂ) R) :
    x ∈ planarCube z (r + R) := by
  constructor
  · have h := abs_sub ((x + y - z).re) y.re
    have hEq : (x + y - z).re - y.re = (x - z).re := by simp; ring
    rw [hEq] at h
    have hY : |y.re| ≤ R := by simpa only [Complex.sub_re, Complex.zero_re, sub_zero] using hy.1
    exact h.trans (add_le_add hxy.1 hY)
  · have h := abs_sub ((x + y - z).im) y.im
    have hEq : (x + y - z).im - y.im = (x - z).im := by simp; ring
    rw [hEq] at h
    have hY : |y.im| ≤ R := by simpa only [Complex.sub_im, Complex.zero_im, sub_zero] using hy.2
    exact h.trans (add_le_add hxy.2 hY)

def cubeConcentration (μ : Measure ℂ) (r : ℝ) : ℝ := ⨆ z : ℂ, μ.real (planarCube z r)

theorem cube_probabilities_bddAbove (μ : Measure ℂ) [IsProbabilityMeasure μ] (r : ℝ) :
    BddAbove (Set.range (fun z => μ.real (planarCube z r))) :=
  ⟨1, fun _ ⟨_, hx⟩ => hx ▸ measureReal_le_one⟩

theorem probability_planarCube_le_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (r : ℝ) (z : ℂ) : μ.real (planarCube z r) ≤ cubeConcentration μ r :=
  le_ciSup (cube_probabilities_bddAbove μ r) z

theorem cubeConcentration_le_of_bounds (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (r A : ℝ) (h : ∀ z, μ.real (planarCube z r) ≤ A) : cubeConcentration μ r ≤ A :=
  ciSup_le h

theorem cubeConcentration_nonneg (μ : Measure ℂ) [IsProbabilityMeasure μ] (r : ℝ) :
    0 ≤ cubeConcentration μ r := measureReal_nonneg.trans
      (probability_planarCube_le_concentration μ r 0)

theorem cubeConcentration_le_one (μ : Measure ℂ) [IsProbabilityMeasure μ] (r : ℝ) :
    cubeConcentration μ r ≤ 1 := cubeConcentration_le_of_bounds μ r 1 (fun _ => measureReal_le_one)

theorem cubeConcentration_mono (μ : Measure ℂ) [IsProbabilityMeasure μ] {r R : ℝ} (hr : r ≤ R) :
    cubeConcentration μ r ≤ cubeConcentration μ R := by
  apply cubeConcentration_le_of_bounds
  intro z
  exact (measureReal_mono (planarCube_mono z hr)).trans
    (probability_planarCube_le_concentration μ R z)

theorem planarConcentration_le_of_bounds (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (r A : ℝ) (hA : 0 ≤ A) (h : ∀ z, μ.real (Metric.closedBall z r) ≤ A) :
    planarConcentration μ r ≤ A := by
  have hBound : levyConcentration μ id r ≤ ENNReal.ofReal A := by
    apply iSup_le
    intro z
    apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hA).mpr
    simpa only [Metric.closedBall, dist_eq_norm, id_eq, measureReal_def] using h z
  simpa only [ENNReal.toReal_ofReal hA] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound

theorem planarConcentration_le_cubeConcentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (r : ℝ) : planarConcentration μ r ≤ cubeConcentration μ r := by
  apply planarConcentration_le_of_bounds μ r _ (cubeConcentration_nonneg μ r)
  intro z
  exact (measureReal_mono (closedBall_subset_planarCube z r)).trans
    (probability_planarCube_le_concentration μ r z)

theorem cubeConcentration_le_planarConcentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) : cubeConcentration μ r ≤ planarConcentration μ (Real.sqrt 2 * r) := by
  apply cubeConcentration_le_of_bounds
  intro z
  exact (measureReal_mono (planarCube_subset_closedBall z hr)).trans
    (probability_closedBall_le_concentration μ _ z)

theorem planarConcentration_mono (μ : Measure ℂ) [IsProbabilityMeasure μ] {r R : ℝ} (hr : r ≤ R) :
    planarConcentration μ r ≤ planarConcentration μ R := by
  apply planarConcentration_le_of_bounds μ r _ (planarConcentration_nonneg μ R)
  intro z
  exact (measureReal_mono (Metric.closedBall_subset_closedBall hr)).trans
    (probability_closedBall_le_concentration μ R z)

end CircularLaw
