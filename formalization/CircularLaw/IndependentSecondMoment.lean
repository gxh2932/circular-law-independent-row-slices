import CircularLaw.PlanarDisk
import CircularLaw.SumLaw
import Mathlib.Probability.Moments.Variance

/-!
# Second moments of independent centered planar sums

Real and imaginary variances give the complex squared-norm identity.
Applied to the actual product of uniform disk laws, this supplies the
second-moment input for smoothing a discrete sum.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CircularLaw

theorem independent_centered_real_second_moment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hInd : iIndepFun X μ)
    (hMean : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, (∑ i, X i ω) ^ 2 ∂μ) = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
  classical
  have hS : MemLp (fun ω => ∑ i, X i ω) 2 μ := by
    exact memLp_finset_sum Finset.univ (fun i _ => hX i)
  have hMeanS : (∫ ω, (∑ i, X i ω) ∂μ) = 0 := by
    rw [integral_finset_sum _ (fun i _ => (hX i).integrable (by norm_num))]
    simp only [hMean, Finset.sum_const_zero]
  have hVar := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hX i)
    (fun i _ j _ hij => hInd.indepFun hij)
  have hSumFun : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hSumFun] at hVar
  rw [variance_of_integral_eq_zero hS.aemeasurable hMeanS] at hVar
  simpa only [variance_of_integral_eq_zero (hX _).aemeasurable (hMean _)] using hVar

theorem complex_second_moment_eq_re_im {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℂ} (hX : MemLp X 2 μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) =
      (∫ ω, (X ω).re ^ 2 ∂μ) + ∫ ω, (X ω).im ^ 2 ∂μ := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two]
  exact integral_add hX.re.integrable_sq hX.im.integrable_sq

theorem independent_centered_complex_second_moment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℂ) (hX : ∀ i, MemLp (X i) 2 μ) (hInd : iIndepFun X μ)
    (hMean : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂μ) = ∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  classical
  have hS : MemLp (fun ω => ∑ i, X i ω) 2 μ := by
    exact memLp_finset_sum Finset.univ (fun i _ => hX i)
  have hMeanR (i : ι) : (∫ ω, (X i ω).re ∂μ) = 0 := by
    simpa only [hMean i, map_zero] using integral_re ((hX i).integrable (by norm_num))
  have hMeanI (i : ι) : (∫ ω, (X i ω).im ∂μ) = 0 := by
    simpa only [hMean i, map_zero] using integral_im ((hX i).integrable (by norm_num))
  have hR := independent_centered_real_second_moment μ (fun i ω => (X i ω).re)
    (fun i => (hX i).re) (hInd.comp (fun _ => Complex.re) (fun _ => Complex.measurable_re)) hMeanR
  have hI := independent_centered_real_second_moment μ (fun i ω => (X i ω).im)
    (fun i => (hX i).im) (hInd.comp (fun _ => Complex.im) (fun _ => Complex.measurable_im)) hMeanI
  rw [complex_second_moment_eq_re_im hS]
  simp only [Complex.re_sum, Complex.im_sum]
  rw [hR, hI, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (complex_second_moment_eq_re_im (hX i)).symm)

theorem planarDisk_product_second_moment_le {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) :
    (∫ x : ι → ℂ, ‖∑ i, x i‖ ^ 2 ∂Measure.pi (fun _ => planarDiskLaw r)) ≤
      (Fintype.card ι : ℝ) * r ^ 2 := by
  haveI := planarDiskLaw_probability hr
  let μ := Measure.pi (fun _ : ι => planarDiskLaw r)
  have hLp : MemLp (fun x : ℂ => x) 2 (planarDiskLaw r) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable r planarDiskLaw_norm_le
  have hCoord (i : ι) : MemLp (fun x : ι → ℂ => x i) 2 μ :=
    hLp.comp_measurePreserving (measurePreserving_eval (fun _ => planarDiskLaw r) i)
  have hCoordMean (i : ι) : (∫ x : ι → ℂ, x i ∂μ) = 0 := by
    change (∫ x : ι → ℂ, (fun y : ℂ => y) (x i) ∂Measure.pi (fun _ => planarDiskLaw r)) = 0
    rw [← integral_map (μ := μ) (φ := fun x : ι → ℂ => x i)
      (measurable_pi_apply i).aemeasurable
      (f := fun y : ℂ => y) measurable_id.aestronglyMeasurable,
      (measurePreserving_eval (fun _ => planarDiskLaw r) i).map_eq]
    exact planarDiskLaw_mean_zero r
  rw [independent_centered_complex_second_moment μ (fun i x => x i) hCoord
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)) hCoordMean]
  calc
    _ ≤ ∑ _ : ι, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      change (∫ x : ι → ℂ, (fun y : ℂ => ‖y‖ ^ 2) (x i)
        ∂Measure.pi (fun _ => planarDiskLaw r)) ≤ r ^ 2
      rw [← integral_map (μ := μ) (φ := fun x : ι → ℂ => x i)
        (measurable_pi_apply i).aemeasurable (f := fun y : ℂ => ‖y‖ ^ 2)
        (by fun_prop),
        (measurePreserving_eval (fun _ => planarDiskLaw r) i).map_eq]
      exact planarDiskLaw_second_moment_le hr
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Independent disk noise stays within a radius proportional to
`sqrt(m)*r` with probability at least three quarters. -/
theorem planarDisk_sum_small_ball_lower {m : ℕ} (hm : 1 ≤ m)
    {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (3 / 4 : ℝ) ≤
      productSumLaw (fun _ : Fin m => planarDiskLaw r)
        (Metric.closedBall 0 (2 * Real.sqrt (m : ℝ) * r)) := by
  haveI := planarDiskLaw_probability hr
  let μ := Measure.pi (fun _ : Fin m => planarDiskLaw r)
  let R := 2 * Real.sqrt (m : ℝ) * r
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hR : 0 < R := mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hmR)) hr
  have hR2 : R ^ 2 = 4 * (m : ℝ) * r ^ 2 := by
    dsimp [R]
    nlinarith [Real.sq_sqrt hmR.le]
  have hLp : MemLp (fun x : ℂ => x) 2 (planarDiskLaw r) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable r planarDiskLaw_norm_le
  have hSumLp : MemLp (fun x : Fin m → ℂ => ∑ i, x i) 2 μ :=
    memLp_finset_sum Finset.univ (fun i _ => hLp.comp_measurePreserving
      (measurePreserving_eval (fun _ => planarDiskLaw r) i))
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => sq_nonneg ‖∑ i, x i‖))
    (hSumLp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) (R ^ 2)
  have hMoment : (∫ x : Fin m → ℂ, ‖∑ i, x i‖ ^ 2 ∂μ) ≤ (m : ℝ) * r ^ 2 := by
    simpa only [Fintype.card_fin] using planarDisk_product_second_moment_le (ι := Fin m) hr
  have hTail : μ.real {x | R < ‖∑ i, x i‖} ≤ 1 / 4 := by
    have hSub : {x : Fin m → ℂ | R < ‖∑ i, x i‖} ⊆ {x | R ^ 2 ≤ ‖∑ i, x i‖ ^ 2} := by
      intro x hx
      exact (sq_le_sq₀ hR.le (norm_nonneg _)).2 hx.le
    have h := (mul_le_mul_of_nonneg_left (measureReal_mono hSub) (sq_nonneg R)).trans
      (hMark.trans hMoment)
    rw [hR2] at h
    nlinarith [mul_pos hmR (sq_pos_of_pos hr)]
  have hGood : (3 / 4 : ℝ) ≤ μ.real {x | ‖∑ i, x i‖ ≤ R} := by
    have hCompl : {x : Fin m → ℂ | R < ‖∑ i, x i‖}ᶜ = {x | ‖∑ i, x i‖ ≤ R} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hProb := probReal_compl_eq_one_sub (μ := μ)
      (s := {x : Fin m → ℂ | R < ‖∑ i, x i‖})
      (measurableSet_lt measurable_const measurable_finite_sum.norm)
    rw [hCompl] at hProb
    linarith
  rw [productSumLaw, Measure.map_apply measurable_finite_sum measurableSet_closedBall]
  have hENN : ENNReal.ofReal (3 / 4 : ℝ) ≤ μ {x | ‖∑ i, x i‖ ≤ R} := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hGood
  simpa only [Set.preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero, R, μ] using hENN

end CircularLaw
