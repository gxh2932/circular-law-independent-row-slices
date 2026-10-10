import CircularLaw.CubeMedian

/-!
# Localized convolution probabilities in cubes

The actual convolution probability is an integral of translated-cube
probabilities. Restricting one summand to a half-mass cube yields the
two-term recurrence in Miroshnikov's proof.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Convolution

namespace CircularLaw

theorem planarCube_add_iff (x y z : ℂ) (r : ℝ) :
    x + y ∈ planarCube z r ↔ y ∈ planarCube (z - x) r := by
  unfold planarCube
  simp only [Set.mem_setOf_eq]
  rw [show x + y - z = y - (z - x) by abel]

theorem integral_cube_indicator_add (ν : Measure ℂ) (x z : ℂ) (r : ℝ) :
    (∫ y, (planarCube z r).indicator (fun _ => (1 : ℝ)) (x + y) ∂ν) =
      ν.real (planarCube (z - x) r) := by
  classical
  have hEq : (fun y => (planarCube z r).indicator (fun _ => (1 : ℝ)) (x + y)) =
      (planarCube (z - x) r).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp only [Set.indicator_apply, planarCube_add_iff]
  rw [hEq, integral_indicator_const _ (measurableSet_planarCube _ _)]
  simp only [smul_eq_mul, mul_one]

theorem cube_indicator_prod_integrable (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℂ) (r : ℝ) :
    Integrable (fun p : ℂ × ℂ => (planarCube z r).indicator (fun _ => (1 : ℝ)) (p.1 + p.2))
      (μ.prod ν) := by
  apply integrable_of_abs_bound _
    ((measurable_const.indicator (measurableSet_planarCube z r)).comp measurable_add) (C := 1)
  intro p
  by_cases hp : p.1 + p.2 ∈ planarCube z r <;> simp [hp]

theorem integrable_translated_cube_probability (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℂ) (r : ℝ) :
    Integrable (fun x => ν.real (planarCube (z - x) r)) μ := by
  simpa only [integral_cube_indicator_add] using
    (cube_indicator_prod_integrable μ ν z r).integral_prod_left

theorem convolution_planarCube_probability (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℂ) (r : ℝ) :
    (μ ∗ ν).real (planarCube z r) = ∫ x, ν.real (planarCube (z - x) r) ∂μ := by
  have hInd : Integrable ((planarCube z r).indicator (fun _ => (1 : ℝ))) (μ ∗ ν) :=
    (integrable_const 1).indicator (measurableSet_planarCube z r)
  rw [← integral_indicator_one (measurableSet_planarCube z r)]
  change (∫ x, (planarCube z r).indicator (fun _ => (1 : ℝ)) x ∂μ ∗ ν) = _
  rw [integral_conv hInd]
  simp only [integral_cube_indicator_add]

theorem convolution_cubeConcentration_le (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (r : ℝ) :
    cubeConcentration (μ ∗ ν) r ≤ cubeConcentration ν r := by
  apply cubeConcentration_le_of_bounds
  intro z
  rw [convolution_planarCube_probability]
  have h := integral_mono (integrable_translated_cube_probability μ ν z r)
    (integrable_const (cubeConcentration ν r))
    (fun x => probability_planarCube_le_concentration ν r (z - x))
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem convolution_restricted_cube_upper (ν μ : Measure ℂ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (b z : ℂ) (r R : ℝ) :
    (ν ∗ μ.restrict (planarCube b R)).real (planarCube z r) ≤
      cubeConcentration μ r * ν.real (planarCube (z - b) (r + R)) := by
  classical
  let B := planarCube b R
  let L := planarCube (z - b) (r + R)
  rw [convolution_planarCube_probability]
  have h := integral_mono (integrable_translated_cube_probability ν (μ.restrict B) z r)
    ((integrable_const (cubeConcentration μ r)).indicator (measurableSet_planarCube _ _))
    (fun x => by
      rw [measureReal_restrict_apply (measurableSet_planarCube _ _)]
      by_cases hx : x ∈ L
      · rw [Set.indicator_of_mem hx]
        exact (measureReal_mono Set.inter_subset_left).trans
          (probability_planarCube_le_concentration μ r (z - x))
      · rw [Set.indicator_of_notMem hx]
        have hEmpty : planarCube (z - x) r ∩ B = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          have hxy := (planarCube_add_iff x y z r).mpr hy.1
          have hShift : x + (y - b) ∈ planarCube (z - b) r := by
            change |(x + (y - b) - (z - b)).re| ≤ r ∧ |(x + (y - b) - (z - b)).im| ≤ r
            rw [show x + (y - b) - (z - b) = x + y - z by abel]
            exact hxy
          have hY : y - b ∈ planarCube (0 : ℂ) R := by
            simpa only [planarCube, sub_zero] using hy.2
          exact hx (planarCube_sub_triangle hShift hY)
        rw [hEmpty, measureReal_empty])
  rw [integral_indicator_const _ (measurableSet_planarCube _ _)] at h
  simpa only [B, L, smul_eq_mul, mul_comm] using h

theorem convolution_restricted_compl_cube_upper (ν μ : Measure ℂ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (B : Set ℂ) (z : ℂ) (r : ℝ) :
    (ν ∗ μ.restrict Bᶜ).real (planarCube z r) ≤ μ.real Bᶜ * cubeConcentration ν r := by
  rw [Measure.conv_comm, convolution_planarCube_probability]
  have h := integral_mono (integrable_translated_cube_probability (μ.restrict Bᶜ) ν z r)
    (integrable_const (cubeConcentration ν r))
    (fun y => probability_planarCube_le_concentration ν r (z - y))
  simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] using h

theorem convolution_half_mass_cube_recurrence (ν μ : Measure ℂ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (b : ℂ) (r R : ℝ)
    (hMass : 1 / 2 ≤ μ.real (planarCube b R)) :
    cubeConcentration (ν ∗ μ) r ≤ cubeConcentration μ r * cubeConcentration ν (r + R) +
      (1 / 2) * cubeConcentration ν r := by
  have hCompl : μ.real (planarCube b R)ᶜ ≤ 1 / 2 := by
    rw [probReal_compl_eq_one_sub (measurableSet_planarCube _ _)]
    linarith
  have hSplit : ν ∗ μ = ν ∗ μ.restrict (planarCube b R) + ν ∗ μ.restrict (planarCube b R)ᶜ := by
    rw [← Measure.conv_add, Measure.restrict_add_restrict_compl (measurableSet_planarCube _ _)]
  apply cubeConcentration_le_of_bounds
  intro z
  rw [hSplit, measureReal_add_apply]
  exact add_le_add
    ((convolution_restricted_cube_upper ν μ b z r R).trans
      (mul_le_mul_of_nonneg_left (probability_planarCube_le_concentration ν (r + R) (z - b))
        (cubeConcentration_nonneg μ r)))
    ((convolution_restricted_compl_cube_upper ν μ _ z r).trans
      (mul_le_mul_of_nonneg_right hCompl (cubeConcentration_nonneg ν r)))

end CircularLaw
